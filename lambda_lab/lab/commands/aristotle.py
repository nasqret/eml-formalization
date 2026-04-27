"""Komenda ``arist`` — integracja z Aristotle (Harmonic AI).

Subkomendy:
  arist submit "<prompt>"        — wysyła zadanie; zwraca project_id
  arist list [--status IN_PROGRESS] — historia
  arist watch <id>               — poll + auto-ściągnięcie po COMPLETE
  arist result <id>              — jednorazowe pobranie gotowego
  arist show <id>                — renderuje .lean z podświetlaniem
  arist compile <id>             — lake env lean … (w projekcie lean_aristotle/)
  arist cancel <id>              — anuluj zadanie
  arist formalize <plik>         — nieformalny tekst → Lean
  arist informal <id>            — GPT wyjaśnia Lean proof po polsku
  arist demo                     — demo De Morgana + submit jako przykład
  arist key                      — status klucza API
"""

from __future__ import annotations

import json
import os
import platform
import shlex
import shutil
import subprocess
import tarfile
import time
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import List, Optional

from rich.console import Console
from rich.panel import Panel
from rich.progress import (
    Progress,
    SpinnerColumn,
    TextColumn,
    TimeElapsedColumn,
)
from rich.syntax import Syntax
from rich.table import Table

from lambda_lab.lab.history import log_event, read_events
from lambda_lab.lab.i18n import t


ROOT = Path(__file__).resolve().parents[3]
LAKE_PROJECT = ROOT / "lambda_lab" / "proofs" / "lean_aristotle"
JOBS_DIR = ROOT / "lambda_lab" / "proofs" / "aristotle"
JOBS_FILE = JOBS_DIR / "jobs.json"

ARISTOTLE_ENV = Path.home() / ".config" / "aristotle" / "env"
OPENAI_ENV = Path.home() / ".config" / "openai" / "env"


# ---------------------------------------------------------------------------
# Ładowanie kluczy API
# ---------------------------------------------------------------------------


def _load_env_files() -> None:
    """Ładuje `~/.config/aristotle/env` i `~/.config/openai/env` bezpiecznie."""
    try:
        from dotenv import load_dotenv
    except ImportError:
        return
    for path in (ARISTOTLE_ENV, OPENAI_ENV):
        if path.exists():
            load_dotenv(path, override=False)


# ---------------------------------------------------------------------------
# Historia projektów (lokalny cache)
# ---------------------------------------------------------------------------


@dataclass
class JobRecord:
    project_id: str
    prompt: str
    created_at: float
    status: str = "SUBMITTED"
    solution_dir: Optional[str] = None

    def to_dict(self) -> dict:
        return {
            "project_id": self.project_id,
            "prompt": self.prompt,
            "created_at": self.created_at,
            "status": self.status,
            "solution_dir": self.solution_dir,
        }


def _load_jobs() -> List[dict]:
    if not JOBS_FILE.exists():
        return []
    try:
        return json.loads(JOBS_FILE.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return []


def _save_jobs(jobs: List[dict]) -> None:
    JOBS_DIR.mkdir(parents=True, exist_ok=True)
    JOBS_FILE.write_text(json.dumps(jobs, indent=2, ensure_ascii=False), encoding="utf-8")


def _record_job(job: JobRecord) -> None:
    jobs = _load_jobs()
    # deduplikacja po project_id
    jobs = [j for j in jobs if j.get("project_id") != job.project_id]
    jobs.insert(0, job.to_dict())
    _save_jobs(jobs)


def _update_job(project_id: str, **fields) -> None:
    jobs = _load_jobs()
    for j in jobs:
        if j.get("project_id") == project_id:
            j.update(fields)
            break
    _save_jobs(jobs)


# ---------------------------------------------------------------------------
# Helper: wywołaj CLI aristotle
# ---------------------------------------------------------------------------


def _aristotle_bin() -> Optional[str]:
    from shutil import which
    return which("aristotle")


_NETWORK_HINTS = (
    "nodename nor servname provided",
    "name or service not known",
    "temporary failure in name resolution",
    "could not resolve host",
    "network is unreachable",
    "no route to host",
    "connection refused",
    "connection reset",
    "connection timed out",
    "connect timeout",
    "no address associated",
    "eai_again", "eai_noname",
    "getaddrinfo failed",
    "ssl: connection",
    "httpx.connecterror",
    "connecterror",
    "readtimeout",
    "remotedisconnected",
)


def _looks_like_network_error(text: str) -> bool:
    t = (text or "").lower()
    return any(hint in t for hint in _NETWORK_HINTS)


def _offline_panel(kind: str, raw: str = "") -> Panel:
    """Wspólny friendly-komunikat gdy sieć padnie."""
    cached = _load_jobs()
    cached_tail = cached[:5]
    lines = [
        t("arist.offline.cant_reach", kind=kind),
        "",
        t("arist.offline.works_header"),
        t("arist.offline.works.1"),
        t("arist.offline.works.2"),
        t("arist.offline.works.3"),
        t("arist.offline.works.4"),
        t("arist.offline.works.5"),
        t("arist.offline.works.6"),
        "",
    ]
    if cached_tail:
        lines.append(t("arist.offline.cached_header"))
        for j in cached_tail:
            pid = str(j.get("project_id", ""))
            st = str(j.get("status", ""))
            pr = str(j.get("prompt", ""))[:60]
            lines.append(f"  • [accent]{pid}[/accent]  {st}  [muted]{pr}[/muted]")
        lines.append("")
        lines.append(t("arist.offline.cached_hint"))
    if raw:
        short = raw.strip().splitlines()[-1] if raw.strip() else ""
        lines.append("")
        lines.append(t("arist.offline.raw_msg", short=short[:140]))
    return Panel("\n".join(lines), title=f"[warn]{t('arist.offline.title')}[/]", border_style="warn")


def _run_aristotle(args: List[str], check: bool = False) -> subprocess.CompletedProcess:
    exe = _aristotle_bin()
    if exe is None:
        raise RuntimeError(t("arist.no_cli"))
    return subprocess.run(
        [exe, *args],
        capture_output=True,
        text=True,
        check=check,
    )


def _require_key(console: Console) -> bool:
    if os.environ.get("ARISTOTLE_API_KEY"):
        return True
    console.print(Panel(
        t("arist.no_key.body", path=ARISTOTLE_ENV),
        title=f"[warn]{t('arist.no_key.title')}[/]",
        border_style="warn",
    ))
    return False


# ---------------------------------------------------------------------------
# Parsowanie project_id z odpowiedzi CLI
# ---------------------------------------------------------------------------


def _extract_project_id(stdout: str) -> Optional[str]:
    """CLI zwraca JSON albo tekst z polem ``project_id``. Bierzemy co znajdziemy."""
    stdout = stdout.strip()
    if not stdout:
        return None
    try:
        payload = json.loads(stdout)
        if isinstance(payload, dict):
            for key in ("project_id", "id", "projectId"):
                if key in payload:
                    return str(payload[key])
    except json.JSONDecodeError:
        pass
    # Fallback: szukamy wzorca UUID / hex
    import re
    m = re.search(r"\b([0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12})\b", stdout)
    if m:
        return m.group(1)
    return None


# ---------------------------------------------------------------------------
# Subkomendy
# ---------------------------------------------------------------------------


def _cmd_submit(console: Console, args: List[str]) -> None:
    if not _require_key(console):
        return
    if not args:
        console.print(f"[warn]{t('arist.submit.usage')}[/warn] {t('arist.submit.usage_msg')}")
        return
    # Domyślnie używamy naszego projektu Lake (toolchain 4.28 + Mathlib).
    project_dir = LAKE_PROJECT if LAKE_PROJECT.exists() else None
    cli_args = ["submit"]
    # Oddzielamy prompt od flag — jeśli pierwszy arg zaczyna się od --, prompt ujęty jest przez shlex już wcześniej.
    prompt_text = args[0]
    extras = args[1:]
    use_wait = False
    explicit_dir: Optional[str] = None
    iterator = iter(extras)
    for tok in iterator:
        if tok == "--project-dir":
            explicit_dir = next(iterator, None)
        elif tok == "--wait":
            use_wait = True
    if explicit_dir:
        cli_args += ["--project-dir", explicit_dir]
    elif project_dir is not None:
        cli_args += ["--project-dir", str(project_dir)]
    if use_wait:
        cli_args.append("--wait")
    cli_args.append(prompt_text)

    console.print(f"[info]→ aristotle {' '.join(shlex.quote(a) for a in cli_args)}[/info]")
    try:
        result = _run_aristotle(cli_args)
    except RuntimeError as e:
        console.print(f"[err]{e}[/err]")
        return
    if result.returncode != 0:
        raw = result.stderr or result.stdout or t("arist.no_output")
        if _looks_like_network_error(raw):
            console.print(_offline_panel("aristotle submit", raw))
        else:
            console.print(Panel(raw, title=f"[err]{t('arist.submit.err_title')}[/]", border_style="err"))
        return

    project_id = _extract_project_id(result.stdout)
    if project_id is None:
        console.print(Panel(
            result.stdout or t("arist.no_output"),
            title=f"[warn]{t('arist.submit.no_id_title')}[/]",
            border_style="warn",
        ))
        return

    _record_job(JobRecord(
        project_id=project_id,
        prompt=prompt_text,
        created_at=time.time(),
        status="QUEUED",
    ))
    log_event("arist_submit", project_id=project_id, prompt=prompt_text)
    console.print(Panel(
        t("arist.submit.ok_body", project_id=project_id, prompt=prompt_text),
        title=f"[ok]{t('arist.submit.ok_title')}[/]",
        border_style="ok",
    ))


def _cmd_list(console: Console, args: List[str]) -> None:
    if not _require_key(console):
        return
    cli_args = ["list"]
    iterator = iter(args)
    for tok in iterator:
        if tok == "--status":
            statuses = []
            nxt = next(iterator, None)
            while nxt is not None and not nxt.startswith("--"):
                statuses.append(nxt)
                nxt = next(iterator, None)
            if statuses:
                cli_args += ["--status", *statuses]
            if nxt is not None:
                # oddać token z powrotem
                iterator = iter([nxt, *iterator])
        elif tok == "--limit":
            cli_args += ["--limit", next(iterator, "10")]

    try:
        result = _run_aristotle(cli_args)
    except RuntimeError as e:
        console.print(f"[err]{e}[/err]")
        return
    if result.returncode != 0:
        raw = result.stderr or result.stdout or ""
        if _looks_like_network_error(raw):
            console.print(_offline_panel("aristotle list", raw))
        else:
            console.print(Panel(raw, title=f"[err]{t('arist.list.err_title')}[/]", border_style="err"))
        return

    # Spróbuj zinterpretować JSON; w razie czego wypisz raw.
    try:
        payload = json.loads(result.stdout)
    except json.JSONDecodeError:
        console.print(result.stdout)
        return

    items = payload if isinstance(payload, list) else payload.get("items", [])
    table = Table(
        title=t("arist.list.title"),
        title_style="header",
        border_style="rule",
        show_header=True,
        header_style="bold",
    )
    table.add_column(t("arist.list.col.id"), style="accent", no_wrap=True)
    table.add_column(t("arist.list.col.status"), style="brand")
    table.add_column(t("arist.list.col.created"), style="muted")
    table.add_column(t("arist.list.col.prompt"), style="bright_white", overflow="fold")
    for item in items:
        pid = item.get("project_id") or item.get("id") or "?"
        status = item.get("status", "?")
        created = item.get("created_at") or item.get("createdAt") or ""
        prompt_text = (item.get("prompt") or item.get("name") or "")
        prompt_short = prompt_text[:80] + ("…" if len(prompt_text) > 80 else "")
        table.add_row(str(pid), str(status), str(created), prompt_short)
    console.print(table)


def _run_with_spinner(
    console: Console,
    cmd: List[str],
    cwd: Path,
    description: str,
) -> tuple[int, str]:
    """Uruchamia długi proces i pokazuje spinner + czas + ostatnią linię stdout/err.

    Zwraca (exit_code, pełne_wyjście). Łączy stdout i stderr w kolejności.
    """
    import queue
    import threading

    proc = subprocess.Popen(
        cmd,
        cwd=str(cwd),
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        bufsize=1,
    )
    q: "queue.Queue[str]" = queue.Queue()

    def _reader() -> None:
        assert proc.stdout is not None
        for line in proc.stdout:
            q.put(line.rstrip("\n"))
        proc.stdout.close()

    reader_thread = threading.Thread(target=_reader, daemon=True)
    reader_thread.start()

    collected: List[str] = []
    try:
        with Progress(
            SpinnerColumn(style="accent"),
            TextColumn("[progress.description]{task.description}"),
            TimeElapsedColumn(),
            console=console,
            transient=True,
        ) as progress:
            task_id = progress.add_task(description, total=None)
            while reader_thread.is_alive() or not q.empty() or proc.poll() is None:
                try:
                    line = q.get(timeout=0.2)
                except queue.Empty:
                    progress.refresh()
                    continue
                collected.append(line)
                # Skróć i oczyść z sekwencji sterujących dla spinnera
                preview = line.strip()
                if len(preview) > 90:
                    preview = preview[:87] + "…"
                if preview:
                    progress.update(task_id, description=f"{description} · [muted]{preview}[/muted]")
    except KeyboardInterrupt:
        proc.terminate()
        try:
            proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            proc.kill()
        console.print(f"[warn]{t('arist.spinner.interrupted')}[/warn]")
        reader_thread.join(timeout=1)
        return (130, "\n".join(collected))

    reader_thread.join()
    proc.wait()
    return (proc.returncode, "\n".join(collected))


def _extract_archive(archive: Path, into: Path) -> List[Path]:
    """Rozpakowuje tar.gz (albo zwykły plik .lean) i zwraca listę rozpakowanych plików.

    CLI Aristotle'a zapisuje rozwiązanie jako *plik* — zwykle tar.gz, ale jeżeli
    serwer zwróci pojedynczy ``.lean``, honoruje nazwę. Próbujemy więc najpierw
    otworzyć jako tarball; jeśli się nie uda — zostawiamy plik w miejscu.
    """
    into.mkdir(parents=True, exist_ok=True)
    extracted: List[Path] = []
    try:
        with tarfile.open(archive, "r:*") as tf:
            # Filter zapobiega atakom przez absolutne / wychodzące poza katalog ścieżki.
            tf.extractall(into, filter="data")
            for member in tf.getmembers():
                if member.isreg():
                    extracted.append(into / member.name)
        return extracted
    except tarfile.ReadError:
        # Nie jest tarballem — pewnie raw .lean / .json. Skopiuj pod known name.
        target = into / archive.name
        if archive.resolve() != target.resolve():
            target.write_bytes(archive.read_bytes())
        return [target]


def _cmd_watch(console: Console, args: List[str]) -> None:
    if not _require_key(console):
        return
    if not args:
        console.print(f"[warn]{t('arist.submit.usage')}[/warn] {t('arist.watch.usage')}")
        return
    project_id = args[0]
    dest_dir = JOBS_DIR / project_id
    dest_dir.mkdir(parents=True, exist_ok=True)
    archive_path = dest_dir / "solution.tar.gz"
    console.print(f"[info]{t('arist.watch.polling')}[/info]")
    try:
        result = _run_aristotle([
            "result", project_id, "--wait", "--destination", str(archive_path),
        ])
    except RuntimeError as e:
        console.print(f"[err]{e}[/err]")
        return
    except KeyboardInterrupt:
        console.print(f"[warn]{t('arist.watch.interrupted')}[/warn]")
        return
    if result.returncode != 0:
        raw = result.stderr or result.stdout or ""
        if _looks_like_network_error(raw):
            console.print(_offline_panel("aristotle result/watch", raw))
        else:
            console.print(Panel(raw, title=f"[err]{t('arist.watch.err_title')}[/]", border_style="err"))
        return

    files = _extract_archive(archive_path, dest_dir)
    lean_files = [f for f in files if f.suffix == ".lean"]
    _update_job(project_id, status="COMPLETE", solution_dir=str(dest_dir))
    log_event(
        "arist_watch_complete",
        project_id=project_id,
        lean_files=[str(f.relative_to(dest_dir)) for f in lean_files],
    )

    lines = [t("arist.watch.saved_in", dest=dest_dir)]
    if lean_files:
        lines.append(t("arist.watch.lean_files", count=len(lean_files)))
        for f in lean_files:
            lines.append(f"  • {f.relative_to(dest_dir)}")
    lines.append(t("arist.watch.next_steps", project_id=project_id))
    console.print(Panel("\n".join(lines), title=f"[ok]{t('arist.watch.done_title')}[/]", border_style="ok"))


def _cmd_result(console: Console, args: List[str]) -> None:
    if not _require_key(console):
        return
    if not args:
        console.print(f"[warn]{t('arist.submit.usage')}[/warn] {t('arist.result.usage')}")
        return
    project_id = args[0]
    dest_dir = JOBS_DIR / project_id
    dest_dir.mkdir(parents=True, exist_ok=True)
    archive_path = dest_dir / "solution.tar.gz"
    try:
        result = _run_aristotle([
            "result", project_id, "--destination", str(archive_path),
        ])
    except RuntimeError as e:
        console.print(f"[err]{e}[/err]")
        return
    if result.returncode != 0:
        console.print(Panel(result.stderr or result.stdout, title=f"[err]{t('arist.result.err_title')}[/]", border_style="err"))
        return
    files = _extract_archive(archive_path, dest_dir)
    lean_files = [f for f in files if f.suffix == ".lean"]
    _update_job(project_id, status="COMPLETE", solution_dir=str(dest_dir))
    console.print(t("arist.result.fetched", total=len(files), lean=len(lean_files), project_id=project_id))


def _find_lean_files(dest: Path) -> List[Path]:
    if not dest.exists():
        return []
    return sorted(dest.rglob("*.lean"))


def _cmd_show(console: Console, args: List[str]) -> None:
    if not args:
        console.print(f"[warn]{t('arist.submit.usage')}[/warn] {t('arist.show.usage')}")
        return
    project_id = args[0]
    dest = JOBS_DIR / project_id
    files = _find_lean_files(dest)
    if not files:
        console.print(f"[warn]{t('arist.show.no_files', dest=dest, project_id=project_id)}[/warn]")
        return
    for f in files:
        text = f.read_text(encoding="utf-8")
        console.print(Panel(
            Syntax(text, "lean", theme="ansi_dark", line_numbers=True),
            title=f"[header]{f.relative_to(dest)}[/header]",
            border_style="accent",
        ))


_STD_LEAN_ROOTS = {
    "Mathlib", "Init", "Std", "Lean", "Aesop", "Batteries",
    "Qq", "ProofWidgets", "LeanSearchClient", "ImportGraph", "Cli",
}


def _slug_short(project_id: str) -> str:
    """Z UUID produkuje prefix modułu — musi zaczynać się wielką literą."""
    hex_only = "".join(c for c in project_id if c.isalnum())[:12]
    return "P" + hex_only


def _rewrite_imports(text: str, prefix: str, local_roots: set[str]) -> str:
    """Przepisuje `import Foo.Bar` → `import <prefix>.Foo.Bar` jeśli `Foo`
    jest lokalnym modułem (nie z Mathliba/Std/etc.)."""
    import re
    def fix(match: "re.Match[str]") -> str:
        head = match.group(1)
        rest = match.group(2)
        if head in _STD_LEAN_ROOTS:
            return match.group(0)
        if head in local_roots:
            return f"import {prefix}.{head}{rest}"
        return match.group(0)
    return re.sub(r"^import\s+([A-Za-z_][\w]*)((?:\.[\w]+)*)\s*$", fix, text, flags=re.MULTILINE)


def _cache_into_library(console: Console, project_id: str, dest: Path) -> Optional[List[str]]:
    """Kopiuje pliki .lean z `dest` do ``LambdaAristotle/Solutions/P<id>/``
    i przepisuje wewnętrzne importy, żeby `lake build` zadziałał.

    Zwraca listę nazw modułów gotowych do `lake build`, albo None przy błędzie.
    """
    short = _slug_short(project_id)
    target_root = LAKE_PROJECT / "LambdaAristotle" / "Solutions" / short
    target_root.mkdir(parents=True, exist_ok=True)

    # Znajdź korzeń (katalog gdzie Aristotle wrzucił swój RequestProject/).
    # Szukamy najpłytszego katalogu zawierającego .lean.
    lean_files = _find_lean_files(dest)
    if not lean_files:
        console.print(f"[err]{t('arist.compile.no_lean_files')}[/err]")
        return None
    source_root = min((f.parent for f in lean_files), key=lambda p: len(p.parts))
    # lokalne korzenie = katalogi tuż pod source_root, oraz nazwy samych plików .lean
    local_roots = {p.name for p in source_root.iterdir() if p.is_dir()}
    local_roots |= {p.stem for p in source_root.glob("*.lean")}

    import re as _re
    copied_modules: List[str] = []
    for f in lean_files:
        rel = f.relative_to(source_root)
        out_path = target_root / rel
        out_path.parent.mkdir(parents=True, exist_ok=True)
        text = f.read_text(encoding="utf-8")
        text = _rewrite_imports(text, f"LambdaAristotle.Solutions.{short}", local_roots)
        out_path.write_text(text, encoding="utf-8")
        # moduł = LambdaAristotle.Solutions.P<id>.<rel_bez_lean_z_kropkami>
        mod_parts = list(rel.with_suffix("").parts)
        mod_name = ".".join(["LambdaAristotle", "Solutions", short, *mod_parts])
        copied_modules.append(mod_name)
    return copied_modules


def _cmd_compile(console: Console, args: List[str]) -> None:
    if not args:
        console.print(f"[warn]{t('arist.submit.usage')}[/warn] {t('arist.compile.usage')}")
        return
    use_cache = "--cache" in args
    use_server = "--server" in args
    positional = [a for a in args if not a.startswith("--")]
    if not positional:
        console.print(f"[warn]{t('arist.compile.no_id')}[/warn]")
        return
    project_id = positional[0]
    dest = JOBS_DIR / project_id
    files = _find_lean_files(dest)
    if not files:
        console.print(f"[warn]{t('arist.compile.no_files', project_id=project_id)}[/warn]")
        return
    if not LAKE_PROJECT.exists():
        console.print(Panel(
            t("arist.compile.no_lake_body", path=LAKE_PROJECT),
            title=f"[err]{t('arist.compile.no_lake_title')}[/]",
            border_style="err",
        ))
        return

    if use_cache:
        _compile_via_lake_build(console, project_id, dest)
        return
    if use_server:
        _compile_via_server(console, project_id, files)
        return

    # Ostrzeż o cold-start, jeśli to pierwsza kompilacja Mathliba w sesji.
    if not getattr(_cmd_compile, "_warned", False):
        console.print(t("arist.compile.modes_hint"))
        _cmd_compile._warned = True  # type: ignore[attr-defined]

    for f in files:
        rel = f.relative_to(dest) if dest in f.parents else f
        console.print(f"[info]→ lake env lean {rel}[/info]")
        rc, output = _run_with_spinner(
            console,
            ["lake", "env", "lean", str(f)],
            cwd=LAKE_PROJECT,
            description=t("arist.compile.compiling", name=f.name),
        )
        log_event(
            "arist_compile",
            project_id=project_id,
            file=f.name,
            exit_code=rc,
            output_bytes=len(output or ""),
        )
        if rc == 0:
            console.print(Panel(
                output or t("arist.compile.zero_warn"),
                title=f"[ok]{t('arist.compile.ok_title', name=f.name)}[/]",
                border_style="ok",
            ))
        else:
            console.print(Panel(
                output or t("arist.compile.no_output_dim"),
                title=f"[err]{t('arist.compile.fail_title', name=f.name, rc=rc)}[/]",
                border_style="err",
            ))


def _compile_via_lake_build(console: Console, project_id: str, dest: Path) -> None:
    """Kopiuje pliki do biblioteki i używa ``lake build`` — cachuje olean,
    więc kolejne uruchomienia są natychmiastowe."""
    console.print(f"[info]{t('arist.compile.cache_intro')}[/info]")
    modules = _cache_into_library(console, project_id, dest)
    if not modules:
        return
    console.print(t("arist.compile.modules_to_build", modules=", ".join(modules)))
    for mod in modules:
        rc, output = _run_with_spinner(
            console,
            ["lake", "build", mod],
            cwd=LAKE_PROJECT,
            description=f"lake build {mod}",
        )
        log_event(
            "arist_compile_cache",
            project_id=project_id,
            module=mod,
            exit_code=rc,
        )
        if rc == 0:
            console.print(Panel(
                output or t("arist.compile.cached_ok_body"),
                title=f"[ok]{t('arist.compile.cached_ok_title', mod=mod)}[/]",
                border_style="ok",
            ))
        else:
            console.print(Panel(
                output or t("arist.compile.no_output_dim"),
                title=f"[err]{t('arist.compile.cached_fail_title', mod=mod, rc=rc)}[/]",
                border_style="err",
            ))


def _compile_via_server(console: Console, project_id: str, files: List[Path]) -> None:
    """Używa persistentnego Lean LSP server — Mathlib raz na sesję."""
    try:
        from lambda_lab.lab.lean_server import LeanServer
    except ImportError as e:
        console.print(f"[err]{e}[/err]")
        return
    console.print(f"[info]{t('arist.compile.server_intro')}[/info]")
    try:
        server = LeanServer.get(LAKE_PROJECT)
    except Exception as e:
        console.print(Panel(
            t("arist.compile.server_start_fail", error=e),
            title=f"[err]{t('arist.compile.server_title')}[/]",
            border_style="err",
        ))
        return
    for f in files:
        t0 = time.monotonic()
        try:
            rc, diags = server.check_file(f)
        except TimeoutError as e:
            console.print(f"[err]{t('arist.compile.server_timeout')}[/err] {e}")
            continue
        except Exception as e:
            console.print(f"[err]{t('arist.compile.server_lsp_err')}[/err] {e}")
            continue
        elapsed = time.monotonic() - t0
        log_event(
            "arist_compile_server",
            project_id=project_id,
            file=f.name,
            errors=rc,
            elapsed_sec=round(elapsed, 2),
            diagnostics=len(diags),
        )
        if rc == 0:
            details = "\n".join(
                f"[muted]{d.line}:{d.col}[/muted] {d.message[:200]}" for d in diags[:6]
            ) or t("arist.compile.zero_warn")
            console.print(Panel(
                f"{details}\n\n{t('arist.compile.server_ok_extra', elapsed=elapsed)}",
                title=f"[ok]{t('arist.compile.server_ok_title', name=f.name)}[/]",
                border_style="ok",
            ))
        else:
            errors = "\n".join(
                f"[err]{d.line}:{d.col}[/err] {d.message[:300]}"
                for d in diags if d.is_error
            )
            console.print(Panel(
                errors or t("arist.compile.server_no_details"),
                title=f"[err]{t('arist.compile.server_fail_title', name=f.name, rc=rc, elapsed=elapsed)}[/]",
                border_style="err",
            ))


def _cmd_server(console: Console, args: List[str]) -> None:
    """`arist server [start|stop|status]` — zarządza persistentnym Lean LSP."""
    from lambda_lab.lab.lean_server import LeanServer
    action = args[0] if args else "status"
    if action == "start":
        try:
            LeanServer.get(LAKE_PROJECT)
            console.print(f"[ok]{t('arist.server.started')}[/ok]")
        except Exception as e:
            console.print(f"[err]{e}[/err]")
    elif action == "stop":
        LeanServer.stop_if_running()
        console.print(f"[muted]{t('arist.server.stopped')}[/muted]")
    elif action == "status":
        inst = LeanServer._instance
        if inst is None or not inst._started:
            console.print(f"[muted]{t('arist.server.idle')}[/muted]")
        else:
            console.print(f"[ok]{t('arist.server.running', dir=inst.project_dir)}[/ok]")
    else:
        console.print(f"[warn]{t('arist.server.unknown')}[/warn] {action}. {t('arist.server.usage')}")


def _cmd_cancel(console: Console, args: List[str]) -> None:
    if not _require_key(console):
        return
    if not args:
        console.print(f"[warn]{t('arist.submit.usage')}[/warn] {t('arist.cancel.usage')}")
        return
    project_id = args[0]
    try:
        result = _run_aristotle(["cancel", project_id])
    except RuntimeError as e:
        console.print(f"[err]{e}[/err]")
        return
    console.print(result.stdout or result.stderr)
    if result.returncode == 0:
        _update_job(project_id, status="CANCELED")


def _cmd_formalize(console: Console, args: List[str]) -> None:
    if not _require_key(console):
        return
    if not args:
        console.print(f"[warn]{t('arist.submit.usage')}[/warn] {t('arist.formalize.usage')}")
        return
    path = Path(args[0]).expanduser()
    if not path.exists():
        console.print(f"[err]{t('arist.formalize.no_file')}[/err] {path}")
        return
    try:
        result = _run_aristotle(["formalize", str(path)])
    except RuntimeError as e:
        console.print(f"[err]{e}[/err]")
        return
    if result.returncode != 0:
        console.print(Panel(result.stderr or result.stdout, title=f"[err]{t('arist.formalize.err_title')}[/]", border_style="err"))
        return
    project_id = _extract_project_id(result.stdout)
    if project_id:
        _record_job(JobRecord(
            project_id=project_id,
            prompt=f"formalize: {path.name}",
            created_at=time.time(),
            status="QUEUED",
        ))
        console.print(t("arist.formalize.queued", pid=project_id))
    else:
        console.print(result.stdout)


def _cmd_informal(console: Console, args: List[str]) -> None:
    """Tłumaczy Lean proof na polski (OpenAI Responses API)."""
    if not args:
        console.print(f"[warn]{t('arist.submit.usage')}[/warn] {t('arist.informal.usage')}")
        return
    project_id = args[0]
    dest = JOBS_DIR / project_id
    files = _find_lean_files(dest)
    if not files:
        console.print(f"[warn]{t('arist.informal.no_files', project_id=project_id)}[/warn]")
        return
    api_key = os.environ.get("OPENAI_API_KEY")
    if not api_key:
        console.print(Panel(
            t("arist.informal.no_openai_body", path=OPENAI_ENV),
            title=f"[warn]{t('arist.informal.no_openai_title')}[/]",
            border_style="warn",
        ))
        return

    try:
        from openai import OpenAI
    except ImportError:
        console.print(f"[err]{t('arist.informal.no_lib')}[/err]")
        return

    model = os.environ.get("OPENAI_MODEL", "gpt-5.5-reasoning")
    effort = os.environ.get("OPENAI_REASONING_EFFORT", "high")
    client = OpenAI(api_key=api_key)

    for f in files:
        text = f.read_text(encoding="utf-8")
        prompt = t("arist.informal.prompt", text=text)

        console.print(f"[info]{t('arist.informal.requesting', model=model, effort=effort, name=f.name)}[/info]")
        try:
            # Responses API — preferowane dla modeli z reasoningiem.
            try:
                response = client.responses.create(
                    model=model,
                    input=prompt,
                    reasoning={"effort": effort},
                )
                out = response.output_text
            except Exception:
                # Fallback na Chat Completions dla modeli bez Responses.
                response = client.chat.completions.create(
                    model=model,
                    messages=[{"role": "user", "content": prompt}],
                )
                out = response.choices[0].message.content or ""
        except Exception as e:
            msg = str(e)
            if _looks_like_network_error(msg):
                console.print(_offline_panel(t("arist.informal.offline_kind"), msg))
                return
            if "model_not_found" in msg or "does not exist" in msg:
                try:
                    models = client.models.list()
                    available = sorted(m.id for m in models.data)[:30]
                    hint = "\n".join(f"  • {m}" for m in available)
                    console.print(Panel(
                        t("arist.informal.model_not_found_body", model=model, hint=hint, path=OPENAI_ENV),
                        title=f"[err]{t('arist.informal.model_not_found_title')}[/]",
                        border_style="err",
                    ))
                except Exception:
                    console.print(f"[err]{msg}[/err]")
            else:
                console.print(f"[err]{t('arist.informal.openai_err', msg=msg)}[/err]")
            return

        console.print(Panel(
            out,
            title=f"[header]{t('arist.informal.panel_title', name=f.name, model=model)}[/header]",
            border_style="brand",
        ))
        # Zapisz do cache — przyda się w `arist export / arist pdf`.
        slug = f.stem
        (dest / f"informal_{slug}.md").write_text(out, encoding="utf-8")
        # Łączny plik (jeśli wiele dowodów w jednym projekcie).
        combined = dest / "informal.md"
        existing = combined.read_text(encoding="utf-8") if combined.exists() else ""
        section = f"\n\n# {f.name}\n\n{out}\n"
        if slug not in existing:
            combined.write_text(existing + section, encoding="utf-8")
        log_event(
            "arist_informal",
            project_id=project_id,
            file=str(f.relative_to(dest)),
            model=model,
            effort=effort,
            length=len(out),
        )


LEAN_LSTDEF = r"""\lstdefinelanguage{lean}{%
  morekeywords={theorem,lemma,def,example,by,intro,intros,exact,apply,rw,rewrite,simp,refine,tauto,tautology,have,show,sorry,induction,cases,if,then,else,let,in,fun,fn,match,with,namespace,end,import,open,structure,class,instance,where,do,return,from,of,this},%
  sensitive=true,%
  morecomment=[l]{--},%
  morecomment=[s]{/-}{-/},%
  morestring=[b]",%
  basicstyle=\ttfamily\small,%
  keywordstyle=\bfseries\color[HTML]{005A9C},%
  commentstyle=\itshape\color[HTML]{636363},%
  stringstyle=\color[HTML]{A31515},%
  frame=single,%
  breaklines=true,%
  columns=flexible,%
  showstringspaces=false,%
  backgroundcolor=\color[HTML]{F6F1DF},%
  literate=%
    {λ}{$\lambda$}1 {∀}{$\forall$}1 {∃}{$\exists$}1 {¬}{$\neg$}1%
    {∧}{$\wedge$}1 {∨}{$\vee$}1 {→}{$\to$}1 {↔}{$\leftrightarrow$}1%
    {≠}{$\neq$}1 {≤}{$\leq$}1 {≥}{$\geq$}1 {ℕ}{$\mathbb{N}$}1 {ℤ}{$\mathbb{Z}$}1%
    {ℝ}{$\mathbb{R}$}1 {ℚ}{$\mathbb{Q}$}1 {⇒}{$\Rightarrow$}1 {⟨}{$\langle$}1 {⟩}{$\rangle$}1%
}
"""


def _find_prompt_for(project_id: str) -> str:
    for j in _load_jobs():
        if j.get("project_id") == project_id:
            return j.get("prompt", "")
    return ""


def _safe_title(s: str, fallback: str) -> str:
    s = (s or "").strip().replace("\n", " ")
    if not s:
        return fallback
    return s[:120] + ("…" if len(s) > 120 else "")


_ORPHAN_MACROS = __import__("re").compile(
    r"(\\(?:operatorname|mathbb|mathcal|mathbf|mathfrak|mathrm|text|"
    r"frac|sqrt|sum|prod|int|oint|lim|limsup|liminf|infty|forall|exists|neg|"
    r"alpha|beta|gamma|Gamma|delta|Delta|epsilon|varepsilon|zeta|eta|theta|Theta|"
    r"iota|kappa|lambda|Lambda|mu|nu|xi|Xi|pi|Pi|rho|sigma|Sigma|tau|upsilon|"
    r"phi|Phi|chi|psi|Psi|omega|Omega|partial|nabla|cdot|times|div|pm|mp|"
    r"leq|geq|neq|approx|equiv|propto|sim|cong|"
    r"subset|subseteq|supset|supseteq|in|notin|cup|cap|setminus|emptyset|varnothing|"
    r"rightarrow|leftarrow|Rightarrow|Leftarrow|leftrightarrow|Leftrightarrow|to|mapsto)"
    r"(?:\{[^{}]*\})?)"
)


def _normalize_math_delims(text: str) -> str:
    """Czyści matematykę tak, żeby pandoc/xelatex nie wybuchał.

    GPT zwraca mieszankę: ``\\(x^2\\)``, ``\\[...\\]``, czasem ``$ \\mathbb{Z} $``
    ze spacjami (pandoc traktuje to jako literał), oraz wolnostojące makra LaTeX
    poza ``$...$`` (``\\operatorname{…}``). Każde z nich psuje ostatecznie xelatex.

    Algorytm:
    1. ``\\[...\\]`` → ``$$...$$``, ``\\(...\\)`` → ``$...$``  (strip wewnętrznych spacji)
    2. ``$ X $`` → ``$X$``  (pandoc nie akceptuje spacji tuż przy ``$``)
    3. Tokenizuj tekst na **segmenty matematyczne/kodowe** i **zwykły tekst**:
       ``$$…$$``, ``$…$``, ```…```, ``\\`…\\``` — zostawiamy nietknięte.
       W segmentach zwykłego tekstu wolnostojące makra (``\\operatorname`` itp.)
       opakowujemy w ``$…$``.
    """
    import re

    # 1) display/inline math z `\[...\]` / `\(...\)`
    text = re.sub(r"\\\[\s*([\s\S]+?)\s*\\\]", lambda m: "$$" + m.group(1).strip() + "$$", text)
    text = re.sub(r"\\\(\s*([^\n]+?)\s*\\\)", lambda m: "$" + m.group(1).strip() + "$", text)
    # 2) strip spacji tuż za/przed `$` (pandoc wymaga)
    text = re.sub(r"\$[ \t]+([^$\n]+?)[ \t]+\$", lambda m: "$" + m.group(1) + "$", text)
    text = re.sub(r"\$[ \t]+([^$\n]+?)\$", lambda m: "$" + m.group(1) + "$", text)
    text = re.sub(r"\$([^$\n]+?)[ \t]+\$", lambda m: "$" + m.group(1) + "$", text)

    # 3) Tokenizer: dzielimy na (math|code) + (reszta). Do reszty aplikujemy wrap orphanów.
    token_re = re.compile(
        r"(\$\$[\s\S]+?\$\$"   # display math
        r"|\$[^$\n]+?\$"       # inline math
        r"|```[\s\S]+?```"     # fenced code
        r"|`[^`\n]+`"          # inline code
        r")"
    )
    parts = token_re.split(text)
    for i, part in enumerate(parts):
        if i % 2 == 1:
            # segment math/code — nie rusz.
            continue
        parts[i] = _ORPHAN_MACROS.sub(lambda m: "$" + m.group(1) + "$", part)
    return "".join(parts)


def _build_markdown_report(project_id: str, dest: Path, lean_files: List[Path]) -> Path:
    """Składa ``report.md`` z preambułą YAML, źródłem Lean i informalizacją GPT."""
    prompt = _find_prompt_for(project_id)
    title = _safe_title(prompt, fallback=f"Aristotle · {project_id[:8]}")
    informal_path = dest / "informal.md"
    informal = informal_path.read_text(encoding="utf-8") if informal_path.exists() else ""
    informal = _normalize_math_delims(informal)
    today = datetime.now().strftime("%d %B %Y")
    model = os.environ.get("OPENAI_MODEL", "gpt")
    header_include = LEAN_LSTDEF.replace("\\", "\\\\").replace("\n", "\\n")  # unused; pandoc czyta plik

    safe_title = title.replace('"', '\\"')
    author = t("arist.report.author_suffix", model=model)
    author = author.replace('"', '\\"')
    yaml = [
        "---",
        f"title: \"{safe_title}\"",
        f"author: \"{author}\"",
        f"date: \"{today}\"",
        f"lang: {t('arist.report.lang')}",
        "geometry: margin=2.2cm",
        "documentclass: article",
        "fontsize: 11pt",
        "colorlinks: true",
        "linkcolor: RoyalBlue",
        "urlcolor: RoyalBlue",
        "header-includes:",
        "  - \\usepackage{amsmath, amssymb, amsthm, mathtools}",
        "  - \\usepackage{xcolor}",
        "  - \\usepackage{fvextra}",
        "  - \\DefineVerbatimEnvironment{Highlighting}{Verbatim}{commandchars=\\\\\\{\\},breaklines,breakanywhere,fontsize=\\small}",
        "---",
        "",
    ]

    sections: List[str] = []
    sections.append(t("arist.report.section.task"))
    if prompt:
        sections.append(f"> {prompt}\n")
    sections.append(f"- **project\\_id**: `{project_id}`\n")
    sections.append(f"- **Lean**: v4.28.0 + Mathlib v4.28.0\n")
    sections.append(f"- **{t('arist.report.section.informalization')}**: OpenAI `{model}`\n")

    sections.append(t("arist.report.section.lean_proof"))
    for f in lean_files:
        rel = f.relative_to(dest) if dest in f.parents else f.name
        sections.append(f"\n### `{rel}`\n")
        body = f.read_text(encoding="utf-8")
        sections.append("```lean\n" + body.rstrip() + "\n```\n")

    sections.append(t("arist.report.section.explanation"))
    if informal.strip():
        sections.append(informal)
    else:
        sections.append(t("arist.report.no_informal"))

    md = "\n".join(yaml) + "\n".join(sections)
    report_md = dest / "report.md"
    report_md.write_text(md, encoding="utf-8")
    # Plik pomocniczy z definicją listings dla Leana (wczytywany przez \input).
    (dest / "lean-lst.tex").write_text(LEAN_LSTDEF, encoding="utf-8")
    return report_md


def _compile_pdf(console: Console, report_md: Path) -> Optional[Path]:
    """Kompiluje ``report.md`` → ``report.pdf`` przez pandoc + xelatex."""
    dest = report_md.parent
    pdf_path = dest / "report.pdf"
    if shutil.which("pandoc") is None:
        console.print(Panel(
            t("arist.pdf.no_pandoc_body"),
            title=f"[err]{t('arist.pdf.no_pandoc_title')}[/]", border_style="err",
        ))
        return None
    engine = None
    for candidate in ("xelatex", "pdflatex"):
        if shutil.which(candidate):
            engine = candidate
            break
    if engine is None:
        console.print(Panel(
            t("arist.pdf.no_engine_body"),
            title=f"[err]{t('arist.pdf.no_pandoc_title')}[/]", border_style="err",
        ))
        return None

    # `tex_math_single_backslash` + `_double_backslash` — GPT często zwraca
    # `\(x^2\)` i `\[...\]` zamiast `$x^2$`/`$$...$$`. Bez tych rozszerzeń
    # pandoc traktuje \operatorname{…} jako raw LaTeX poza math mode i xelatex
    # rzuca „Missing $ inserted".
    input_format = "markdown+tex_math_single_backslash+tex_math_double_backslash"
    # Bez --listings: lstlisting nie łyka Unicode (Lean ma ₀, ≠, ∈). Domyślny
    # pandocowy Highlighting/Verbatim w xelatex ogarnia wszystko.
    cmd = [
        "pandoc", str(report_md),
        "-f", input_format,
        "-o", str(pdf_path),
        f"--pdf-engine={engine}",
        "--highlight-style=tango",
        "--standalone",
        "--toc", "--toc-depth=2",
    ]
    rc, out = _run_with_spinner(
        console, cmd, cwd=dest,
        description=t("arist.pdf.spinner", engine=engine),
    )
    if rc != 0 or not pdf_path.exists():
        console.print(Panel(
            out or t("arist.no_output"),
            title=f"[err]{t('arist.pdf.engine_fail_title', engine=engine, rc=rc)}[/]",
            border_style="err",
        ))
        return None
    return pdf_path


def _open_pdf(console: Console, pdf_path: Path) -> None:
    system = platform.system()
    if system == "Darwin":
        subprocess.Popen(["open", str(pdf_path)])
    elif system == "Linux":
        subprocess.Popen(["xdg-open", str(pdf_path)])
    elif system == "Windows":
        os.startfile(str(pdf_path))  # type: ignore[attr-defined]
    else:
        console.print(t("arist.pdf.open_manual", path=pdf_path))
        return
    console.print(f"[info]{t('arist.pdf.opened')}[/info] {pdf_path}")


def _cmd_export(console: Console, args: List[str]) -> None:
    if not args:
        console.print(f"[warn]{t('arist.submit.usage')}[/warn] {t('arist.export.usage')}")
        return
    project_id = args[0]
    dest = JOBS_DIR / project_id
    lean_files = _find_lean_files(dest)
    if not lean_files:
        console.print(f"[warn]{t('arist.export.no_files', dest=dest, project_id=project_id)}[/warn]")
        return
    console.print(f"[info]{t('arist.export.composing')}[/info]")
    report_md = _build_markdown_report(project_id, dest, lean_files)
    pdf = _compile_pdf(console, report_md)
    if pdf is None:
        console.print(t("arist.export.markdown_path", path=report_md))
        return
    log_event("arist_export", project_id=project_id, pdf=str(pdf))
    console.print(Panel(
        t("arist.export.ok_body", md=report_md, pdf=pdf, project_id=project_id),
        title=f"[ok]{t('arist.export.ok_title')}[/]",
        border_style="ok",
    ))


def _cmd_pdf(console: Console, args: List[str]) -> None:
    """informal (jeśli trzeba) → export → otwórz PDF w systemowym podglądzie."""
    if not args:
        console.print(f"[warn]{t('arist.submit.usage')}[/warn] {t('arist.pdf.usage')}")
        return
    project_id = args[0]
    dest = JOBS_DIR / project_id
    lean_files = _find_lean_files(dest)
    if not lean_files:
        console.print(f"[warn]{t('arist.pdf.no_files', project_id=project_id)}[/warn]")
        return
    # Krok 1 — informal, jeśli brak cache.
    informal_path = dest / "informal.md"
    if not informal_path.exists() or not informal_path.read_text(encoding="utf-8").strip():
        if not os.environ.get("OPENAI_API_KEY"):
            console.print(Panel(
                t("arist.pdf.no_openai_body"),
                title=f"[warn]{t('arist.pdf.no_openai_title')}[/]", border_style="warn",
            ))
        else:
            _cmd_informal(console, [project_id])
    # Krok 2 — export.
    report_md = _build_markdown_report(project_id, dest, lean_files)
    pdf = _compile_pdf(console, report_md)
    if pdf is None:
        return
    # Krok 3 — podgląd.
    log_event("arist_pdf_preview", project_id=project_id, pdf=str(pdf))
    _open_pdf(console, pdf)


def _cmd_warmup(console: Console, args: List[str]) -> None:
    """Prewarm: ładuje oleany Mathliba do page cache, żeby następne
    kompilacje były 3-4x szybsze (cold 13.8 s → warm 3.8 s dla pełnego
    ``Mathlib.Tactic``). Puść raz na początku sesji wykładowej."""
    if not LAKE_PROJECT.exists():
        console.print(f"[warn]{t('arist.warmup.no_lake')}[/warn]")
        return
    warm_file = LAKE_PROJECT / "LambdaAristotle" / "Warmup.lean"
    if not warm_file.exists():
        console.print(f"[warn]{t('arist.warmup.no_file', path=warm_file)}[/warn]")
        return
    console.print(f"[info]{t('arist.warmup.starting')}[/info]")
    t0 = time.monotonic()
    rc, out = _run_with_spinner(
        console,
        ["lake", "env", "lean", str(warm_file)],
        cwd=LAKE_PROJECT,
        description=t("arist.warmup.spinner"),
    )
    elapsed = time.monotonic() - t0
    log_event("arist_warmup", exit_code=rc, elapsed_sec=round(elapsed, 2))
    if rc == 0:
        console.print(Panel(
            t("arist.warmup.ok_body", elapsed=elapsed),
            title=f"[ok]{t('arist.warmup.ok_title')}[/]",
            border_style="ok",
        ))
    else:
        console.print(Panel(
            out or t("arist.no_output"),
            title=f"[err]{t('arist.warmup.fail_title', rc=rc)}[/]",
            border_style="err",
        ))


def _cmd_log(console: Console, args: List[str]) -> None:
    """Pokazuje dziennik wszystkiego, co kiedyś zrobiłem w REPL-u."""
    limit = 30
    project_filter: Optional[str] = None
    iterator = iter(args)
    for tok in iterator:
        if tok == "--limit":
            nxt = next(iterator, None)
            try:
                limit = int(nxt) if nxt is not None else limit
            except ValueError:
                console.print(f"[err]{t('arist.log.bad_limit')}[/err] {nxt}")
                return
        elif tok == "--project":
            project_filter = next(iterator, None)
        elif tok == "--all":
            limit = 10_000

    events = read_events()
    if project_filter:
        events = [e for e in events if e.get("project_id") == project_filter]
    events = events[-limit:]
    if not events:
        console.print(f"[muted]{t('arist.log.empty')}[/muted]")
        return

    table = Table(
        title=t("arist.log.title", count=len(events)),
        title_style="header",
        border_style="rule",
        show_header=True,
        header_style="bold",
    )
    table.add_column(t("arist.log.col.time"), style="muted", no_wrap=True)
    table.add_column(t("arist.log.col.kind"), style="brand", no_wrap=True)
    table.add_column(t("arist.log.col.project"), style="accent", no_wrap=True)
    table.add_column(t("arist.log.col.details"), style="bright_white", overflow="fold")

    for e in events:
        ts = str(e.get("ts", ""))[:19]
        kind = str(e.get("kind", ""))
        pid = str(e.get("project_id", "") or "")
        pid_short = (pid[:8] + "…") if len(pid) > 10 else pid
        details = {k: v for k, v in e.items() if k not in ("ts", "kind", "project_id")}
        details_str = ", ".join(f"{k}={v}" for k, v in details.items())
        if len(details_str) > 100:
            details_str = details_str[:97] + "…"
        table.add_row(ts, kind, pid_short, details_str)
    console.print(table)


def _cmd_demo(console: Console, args: List[str]) -> None:
    """Przykład z wykładu: De Morgan — wysyłany do Aristotle'a na żywo."""
    if not _require_key(console):
        return
    prompt_text = (
        "Prove in Lean 4 with Mathlib: "
        "theorem demorgan_and (a b : Prop) : ¬ (a ∧ b) ↔ ¬ a ∨ ¬ b. "
        "Use classical logic if needed. Keep the proof short and pedagogical."
    )
    console.print(Panel(
        t("arist.demo.body", prompt=prompt_text),
        title=f"[header]{t('arist.demo.title')}[/]",
        border_style="accent",
    ))
    _cmd_submit(console, [prompt_text])
    try:
        from lambda_lab.lab.kb import cross_ref_line
        line = cross_ref_line("aristotle-system", "kb.crossref.aristotle")
        if line:
            console.print(f"[muted]{line}[/muted]")
    except Exception:  # pragma: no cover
        pass


def _cmd_key(console: Console, args: List[str]) -> None:
    ar = t("arist.key.set") if os.environ.get("ARISTOTLE_API_KEY") else t("arist.key.missing")
    oa = t("arist.key.set") if os.environ.get("OPENAI_API_KEY") else t("arist.key.missing")
    model = os.environ.get("OPENAI_MODEL", "—")
    effort = os.environ.get("OPENAI_REASONING_EFFORT", "—")
    console.print(Panel(
        t("arist.key.body",
          ar=ar, oa=oa, model=model, effort=effort,
          arist_env=ARISTOTLE_ENV, openai_env=OPENAI_ENV,
          lake=LAKE_PROJECT, jobs=JOBS_FILE),
        title=f"[header]{t('arist.key.title')}[/]",
        border_style="rule",
    ))


# ---------------------------------------------------------------------------
# Dispatch
# ---------------------------------------------------------------------------


SUBCOMMANDS = {
    "submit": _cmd_submit,
    "list": _cmd_list,
    "ls": _cmd_list,
    "watch": _cmd_watch,
    "result": _cmd_result,
    "show": _cmd_show,
    "compile": _cmd_compile,
    "cancel": _cmd_cancel,
    "formalize": _cmd_formalize,
    "informal": _cmd_informal,
    "export": _cmd_export,
    "pdf": _cmd_pdf,
    "preview": _cmd_pdf,
    "log": _cmd_log,
    "history": _cmd_log,
    "warmup": _cmd_warmup,
    "warm": _cmd_warmup,
    "server": _cmd_server,
    "demo": _cmd_demo,
    "key": _cmd_key,
    "keys": _cmd_key,
}


def handle(console: Console, args: str) -> None:
    _load_env_files()
    if not args.strip():
        console.print(Panel(
            t("arist.help.body"),
            title=f"[header]{t('arist.help.title')}[/]",
            border_style="brand",
        ))
        return
    try:
        parts = shlex.split(args)
    except ValueError as e:
        console.print(f"[err]{t('arist.argparse_err', error=e)}[/err]")
        return
    sub = parts[0]
    rest = parts[1:]
    handler = SUBCOMMANDS.get(sub)
    if handler is None:
        console.print(f"[warn]{t('arist.unknown_sub')}[/warn] {sub}. {t('arist.unknown_sub_hint')}")
        return
    handler(console, rest)
