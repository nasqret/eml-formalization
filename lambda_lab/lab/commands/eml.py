"""Komenda ``eml`` - dashboard formalizacji arXiv:2603.21852.

Subkomendy:
  eml list [--status STATE] [--difficulty N]
  eml show <chunk-id>
  eml tree
  eml status
  eml submit <chunk-id> [--all-pending] [--limit N]
  eml watch <chunk-id> [--all]
  eml verify [<chunk-id>]
  eml combine [--pdf] [--html]
  eml refresh-paper

Architektura:
  - Same path constants/manifest helpers utrzymywane lokalnie.
  - Dla wywolan Aristotle/Lean reuse-ujemy pierwotne pomocnicze z
    ``aristotle.py``: ``_load_env_files``, ``_extract_project_id``,
    ``_offline_panel``, ``_run_aristotle``, ``_run_with_spinner``,
    ``_compile_pdf``.
  - Caly modul jest off-network w testach: zewnetrzne calle ida przez
    ``subprocess.run`` ktory testy mockuja.
"""

from __future__ import annotations

import json
import shlex
import subprocess
import tarfile
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from rich.console import Console
from rich.panel import Panel
from rich.syntax import Syntax
from rich.table import Table
from rich.tree import Tree

from lambda_lab.lab.commands.aristotle import (
    LAKE_PROJECT,
    _compile_pdf,
    _extract_project_id,
    _load_env_files,
    _offline_panel,
    _run_aristotle,
    _run_with_spinner,
)
from lambda_lab.lab.i18n import t


# ---------------------------------------------------------------------------
# Path constants (mirror aristotle.py shape).
# ---------------------------------------------------------------------------

ROOT = Path(__file__).resolve().parents[3]
EML_ROOT = ROOT / "lambda_lab" / "proofs" / "eml"
DEFAULT_PAPER = "2603_21852"
PAPER_DIR = EML_ROOT / DEFAULT_PAPER
CHUNKS_DIR = PAPER_DIR / "chunks"
LEAN_WS = PAPER_DIR / "lean_workspace"
MANIFEST = PAPER_DIR / "manifest.json"
SOLUTIONS_DIR = LEAN_WS / "EML" / "Solutions"
REPORT_MD = PAPER_DIR / "report.md"
REPORT_HTML = PAPER_DIR / "report.html"


# ---------------------------------------------------------------------------
# Manifest + chunk helpers.
# ---------------------------------------------------------------------------


def _paper_dir() -> Path:
    """Return the active paper dir; tests monkeypatch ``PAPER_DIR``."""
    return PAPER_DIR


def _chunks_dir() -> Path:
    return CHUNKS_DIR


def _manifest_path() -> Path:
    return MANIFEST


def _load_manifest() -> dict:
    """Load ``manifest.json``; if missing/corrupt return ``{"chunks": []}``."""
    p = _manifest_path()
    if not p.exists():
        return {"chunks": []}
    try:
        data = json.loads(p.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return {"chunks": []}
    if not isinstance(data, dict):
        return {"chunks": []}
    data.setdefault("chunks", [])
    return data


def _save_manifest(m: dict) -> None:
    p = _manifest_path()
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(m, indent=2, ensure_ascii=False), encoding="utf-8")


def _chunk_dir(chunk_id: str) -> Path:
    return _chunks_dir() / chunk_id


def _load_chunk_meta(chunk_id: str) -> dict:
    p = _chunk_dir(chunk_id) / "meta.json"
    if not p.exists():
        return {}
    try:
        data = json.loads(p.read_text(encoding="utf-8"))
        return data if isinstance(data, dict) else {}
    except json.JSONDecodeError:
        return {}


def _save_chunk_meta(chunk_id: str, meta: dict) -> None:
    p = _chunk_dir(chunk_id) / "meta.json"
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(meta, indent=2, ensure_ascii=False), encoding="utf-8")


def _list_chunks() -> List[str]:
    """All chunk ids (directory names) sorted lexicographically."""
    base = _chunks_dir()
    if not base.exists():
        return []
    return sorted(p.name for p in base.iterdir() if p.is_dir())


def _resolve_chunk_id(prefix: str) -> Optional[str]:
    """Resolve a prefix to a full chunk id.

    Accepts numeric prefixes (``001``), partial slugs (``001_def``) and
    full ids (``001_def_eml``). Returns ``None`` on no match or ambiguity.
    """
    if not prefix:
        return None
    chunks = _list_chunks()
    # exact match wins
    if prefix in chunks:
        return prefix
    matches = [c for c in chunks if c.startswith(prefix) or c.startswith(f"{prefix}_")]
    # also accept "_def" inside the slug after the numeric prefix
    if not matches:
        matches = [c for c in chunks if prefix in c]
    if len(matches) == 1:
        return matches[0]
    return None


def _read_text_safe(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except OSError:
        return ""


def _meta_title(meta: dict) -> str:
    for key in ("title_en", "title_pl", "title", "name"):
        v = meta.get(key)
        if v:
            return str(v)
    return meta.get("id", "")


# ---------------------------------------------------------------------------
# Subcommands
# ---------------------------------------------------------------------------


def _show_help(console: Console) -> None:
    console.print(Panel(
        t("eml.help.body"),
        title=f"[header]{t('eml.help.title')}[/header]",
        border_style="brand",
    ))


def _check_workspace(console: Console) -> bool:
    if not _paper_dir().exists():
        console.print(f"[warn]{t('eml.no_paper')}[/warn]")
        return False
    return True


def _cmd_list(console: Console, args: List[str]) -> None:
    if not _check_workspace(console):
        return
    status_filter: Optional[str] = None
    diff_filter: Optional[int] = None
    iterator = iter(args)
    for tok in iterator:
        if tok == "--status":
            status_filter = next(iterator, None)
        elif tok == "--difficulty":
            nxt = next(iterator, None)
            try:
                diff_filter = int(nxt) if nxt is not None else None
            except ValueError:
                diff_filter = None

    chunk_ids = _list_chunks()
    rows: List[Tuple[str, dict]] = []
    for cid in chunk_ids:
        meta = _load_chunk_meta(cid)
        if status_filter and str(meta.get("status", "pending")) != status_filter:
            continue
        if diff_filter is not None and int(meta.get("difficulty", 0) or 0) != diff_filter:
            continue
        rows.append((cid, meta))

    if not rows:
        console.print(f"[muted]{t('eml.list.no_chunks')}[/muted]")
        return

    table = Table(
        title=t("eml.list.title", count=len(rows)),
        title_style="header",
        border_style="rule",
        show_header=True,
        header_style="bold",
    )
    table.add_column(t("eml.list.col.id"), style="accent", no_wrap=True)
    table.add_column(t("eml.list.col.title"), style="bright_white", overflow="fold")
    table.add_column(t("eml.list.col.kind"), style="brand")
    table.add_column(t("eml.list.col.difficulty"), style="muted", justify="right")
    table.add_column(t("eml.list.col.status"), style="brand")
    table.add_column(t("eml.list.col.project"), style="muted")
    table.add_column(t("eml.list.col.deps"), style="muted", overflow="fold")
    for cid, meta in rows:
        title = _meta_title(meta)
        kind = str(meta.get("kind", ""))
        diff = str(meta.get("difficulty", "") or "")
        status = str(meta.get("status", "pending"))
        pid = str(meta.get("aristotle_project_id", "") or "")
        pid_short = pid[:8] + ("..." if len(pid) > 10 else "")
        deps = ", ".join(meta.get("depends_on", []) or [])
        table.add_row(cid, title[:60], kind, diff, status, pid_short, deps)
    console.print(table)


def _cmd_show(console: Console, args: List[str]) -> None:
    if not _check_workspace(console):
        return
    if not args:
        console.print(f"[warn]{t('eml.show.usage')}[/warn]")
        return
    prefix = args[0]
    chunk_id = _resolve_chunk_id(prefix)
    if chunk_id is None:
        console.print(f"[warn]{t('eml.show.no_chunk', prefix=prefix)}[/warn]")
        return
    meta = _load_chunk_meta(chunk_id)
    cdir = _chunk_dir(chunk_id)
    chunk_md = cdir / "chunk.md"
    target_lean = cdir / "target.lean"
    result_lean = cdir / "result.lean"

    title = t("eml.show.title", chunk_id=chunk_id)
    sections: List[str] = []
    if chunk_md.exists():
        sections.append(_read_text_safe(chunk_md))
    else:
        # Reconstruct a minimal view from meta.json fields.
        paper = meta.get("paper_quote") or ""
        informal = meta.get("informal_en") or meta.get("informal_pl") or ""
        sig = meta.get("lean_target_signature") or ""
        block = []
        if paper:
            block.append(f"### {t('eml.show.section.paper')}\n\n> {paper}\n")
        if informal:
            block.append(f"### {t('eml.show.section.informal')}\n\n{informal}\n")
        if sig:
            block.append(f"### {t('eml.show.section.lean')}\n\n```lean\n{sig}\n```\n")
        sections.append("\n".join(block))

    body = "\n".join(sections).strip() or t("eml.show.no_target")
    console.print(Panel(body, title=f"[header]{title}[/header]", border_style="brand"))

    # Show Lean target separately with syntax highlighting.
    lean_path = result_lean if result_lean.exists() else target_lean
    if lean_path.exists():
        text = _read_text_safe(lean_path)
        console.print(Panel(
            Syntax(text, "lean", theme="ansi_dark", line_numbers=True),
            title=f"[accent]{lean_path.name}[/accent]",
            border_style="accent",
        ))
    else:
        console.print(f"[muted]{t('eml.show.no_target')}[/muted]")

    status_line = (
        f"status={meta.get('status', 'pending')}  "
        f"difficulty={meta.get('difficulty', '?')}  "
        f"deps=[{', '.join(meta.get('depends_on', []) or []) or '-'}]  "
        f"project_id={meta.get('aristotle_project_id') or '-'}"
    )
    console.print(Panel(
        status_line,
        title=f"[muted]{t('eml.show.section.status')}[/muted]",
        border_style="rule",
    ))


def _cmd_tree(console: Console, args: List[str]) -> None:
    if not _check_workspace(console):
        return
    chunk_ids = _list_chunks()
    if not chunk_ids:
        console.print(f"[muted]{t('eml.tree.no_chunks')}[/muted]")
        return

    metas: Dict[str, dict] = {cid: _load_chunk_meta(cid) for cid in chunk_ids}
    deps: Dict[str, List[str]] = {
        cid: list(metas[cid].get("depends_on", []) or []) for cid in chunk_ids
    }

    # Cycle detection via DFS coloring.
    WHITE, GRAY, BLACK = 0, 1, 2
    color: Dict[str, int] = {cid: WHITE for cid in chunk_ids}
    cycle_nodes: set = set()

    def dfs(node: str, stack: List[str]) -> None:
        color[node] = GRAY
        for d in deps.get(node, []):
            if d not in color:
                continue
            if color[d] == GRAY:
                # cycle: every node in current stack from d onwards is part of it
                if d in stack:
                    idx = stack.index(d)
                    for n in stack[idx:]:
                        cycle_nodes.add(n)
                cycle_nodes.add(node)
                cycle_nodes.add(d)
            elif color[d] == WHITE:
                dfs(d, stack + [d])
        color[node] = BLACK

    for cid in chunk_ids:
        if color[cid] == WHITE:
            dfs(cid, [cid])

    # Roots = chunks with no deps; build a forest.
    root = Tree(f"[header]{t('eml.tree.title')}[/header]")
    roots = [cid for cid in chunk_ids if not deps.get(cid)]
    # walk known roots first
    rendered: set = set()

    def add_node_track(parent: Tree, cid: str, seen: set) -> None:
        meta = metas.get(cid, {})
        status = str(meta.get("status", "pending"))
        label = f"{cid} [muted]({status})[/muted]"
        if cid in cycle_nodes:
            label = f"[err]{cid} {t('eml.tree.cycle')}[/err]"
        if cid in seen:
            parent.add(f"[muted]{cid} ...[/muted]")
            return
        rendered.add(cid)
        node = parent.add(label)
        children = [c for c in chunk_ids if cid in (deps.get(c) or [])]
        for ch in children:
            add_node_track(node, ch, seen | {cid})

    if not roots:
        # all in cycles; render every chunk flat
        for cid in chunk_ids:
            if cid not in rendered:
                add_node_track(root, cid, set())
    else:
        for cid in roots:
            add_node_track(root, cid, set())
        # also surface any cycle nodes that didn't show up under roots
        for cid in cycle_nodes:
            if cid not in rendered:
                add_node_track(root, cid, set())

    console.print(root)


def _cmd_status(console: Console, args: List[str]) -> None:
    if not _check_workspace(console):
        return
    chunk_ids = _list_chunks()
    if not chunk_ids:
        console.print(t("eml.status.empty"))
        return
    counts = {"pending": 0, "submitted": 0, "complete": 0, "failed": 0}
    for cid in chunk_ids:
        meta = _load_chunk_meta(cid)
        status = str(meta.get("status", "pending"))
        counts[status] = counts.get(status, 0) + 1
    total = len(chunk_ids)
    coverage = round(100.0 * counts.get("complete", 0) / total, 1) if total else 0.0
    console.print(t(
        "eml.status.summary",
        pending=counts.get("pending", 0),
        submitted=counts.get("submitted", 0),
        complete=counts.get("complete", 0),
        failed=counts.get("failed", 0),
        coverage=coverage,
        total=total,
    ))


# ---------------------------------------------------------------------------
# Submit / watch / verify
# ---------------------------------------------------------------------------


def _build_submission_prompt(chunk_id: str, meta: dict, target_text: str, chunk_md: str) -> str:
    """Compose the submission text we send to ``aristotle submit``."""
    head = "Prove this Lean theorem against Lean 4.28.0 + Mathlib v4.28.0."
    informal = (meta.get("informal_en") or meta.get("informal_pl") or "").strip()
    if not informal and chunk_md:
        # take first non-empty paragraph
        for para in chunk_md.split("\n\n"):
            para = para.strip()
            if para and not para.startswith("#"):
                informal = para
                break
    informal_short = " ".join(informal.split())[:600]
    parts = [head]
    if informal_short:
        parts.append("Context: " + informal_short)
    parts.append(target_text.strip())
    return "\n\n".join(parts)


def _record_submission(chunk_id: str, project_id: str, prompt: str) -> None:
    meta = _load_chunk_meta(chunk_id)
    meta["aristotle_project_id"] = project_id
    meta["status"] = "submitted"
    meta["submitted_at"] = datetime.now(tz=timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    _save_chunk_meta(chunk_id, meta)

    manifest = _load_manifest()
    chunks = manifest.setdefault("chunks", [])
    found = False
    for entry in chunks:
        # Manifest entries authored by the decomposition agent use `id`;
        # entries authored by an earlier _record_submission used `chunk_id`.
        # Match either, so we update in place rather than duplicate.
        if (entry.get("id") or entry.get("chunk_id")) == chunk_id:
            entry.update({
                "id": chunk_id,
                "project_id": project_id,
                "submitted_at": meta["submitted_at"],
                "status": "submitted",
                "prompt": prompt[:400],
            })
            found = True
            break
    if not found:
        chunks.append({
            "id": chunk_id,
            "project_id": project_id,
            "submitted_at": meta["submitted_at"],
            "status": "submitted",
            "prompt": prompt[:400],
        })
    _save_manifest(manifest)


def _submit_one(console: Console, chunk_id: str) -> str:
    """Submit a single chunk. Returns 'ok'|'skipped'|'failed'."""
    meta = _load_chunk_meta(chunk_id)
    status = str(meta.get("status", "pending"))
    if status in ("complete", "submitted"):
        console.print(f"[muted]{t('eml.submit.already_complete', chunk_id=chunk_id, status=status)}[/muted]")
        return "skipped"
    target_path = _chunk_dir(chunk_id) / "target.lean"
    if not target_path.exists():
        console.print(f"[warn]{t('eml.submit.no_target', chunk_id=chunk_id)}[/warn]")
        return "skipped"
    target_text = _read_text_safe(target_path)
    chunk_md = _read_text_safe(_chunk_dir(chunk_id) / "chunk.md")
    prompt = _build_submission_prompt(chunk_id, meta, target_text, chunk_md)

    console.print(f"[info]{t('eml.submit.submitting', chunk_id=chunk_id)}[/info]")
    cli_args = ["submit", "--project-dir", str(LAKE_PROJECT), prompt]
    try:
        result = _run_aristotle(cli_args)
    except RuntimeError as e:
        console.print(f"[err]{t('eml.submit.err', chunk_id=chunk_id, error=e)}[/err]")
        return "failed"
    if result.returncode != 0:
        raw = result.stderr or result.stdout or ""
        console.print(Panel(
            raw or t("eml.submit.err", chunk_id=chunk_id, error="?"),
            title=f"[err]{t('eml.submit.err', chunk_id=chunk_id, error='rc!=0')}[/err]",
            border_style="err",
        ))
        return "failed"
    project_id = _extract_project_id(result.stdout) or _extract_project_id(result.stderr)
    if project_id is None:
        # Aristotle CLI 1.0.x prints API-level errors to stderr with rc=0.
        # Surface the actual message so the user can act (rate limit, etc.).
        api_msg = (result.stderr or result.stdout or "").strip().splitlines()
        api_msg = " | ".join(line for line in api_msg if line)[:240] or "no project_id"
        console.print(f"[warn]{t('eml.submit.err', chunk_id=chunk_id, error=api_msg)}[/warn]")
        return "failed"
    _record_submission(chunk_id, project_id, prompt)
    console.print(f"[ok]{t('eml.submit.ok', chunk_id=chunk_id, project_id=project_id)}[/ok]")
    return "ok"


def _deps_satisfied(chunk_id: str, all_metas: Dict[str, dict]) -> Tuple[bool, List[str]]:
    deps = list(all_metas.get(chunk_id, {}).get("depends_on", []) or [])
    missing = [d for d in deps if str(all_metas.get(d, {}).get("status", "pending")) != "complete"]
    return (not missing, missing)


def _cmd_submit(console: Console, args: List[str]) -> None:
    if not _check_workspace(console):
        return
    if not args:
        console.print(f"[warn]{t('eml.submit.usage')}[/warn]")
        return

    all_pending = "--all-pending" in args
    limit = 5
    positional: List[str] = []
    iterator = iter(args)
    for tok in iterator:
        if tok == "--all-pending":
            continue
        if tok == "--limit":
            nxt = next(iterator, None)
            try:
                limit = int(nxt) if nxt is not None else limit
            except ValueError:
                pass
            continue
        positional.append(tok)

    if all_pending:
        chunk_ids = _list_chunks()
        all_metas = {c: _load_chunk_meta(c) for c in chunk_ids}
        ok = skipped = failed = 0
        sent = 0
        for cid in chunk_ids:
            if sent >= limit:
                break
            meta = all_metas.get(cid, {})
            if str(meta.get("status", "pending")) != "pending":
                continue
            satisfied, missing = _deps_satisfied(cid, all_metas)
            if not satisfied:
                console.print(f"[muted]{t('eml.submit.no_dependencies_met', chunk_id=cid, missing=', '.join(missing))}[/muted]")
                skipped += 1
                continue
            outcome = _submit_one(console, cid)
            if outcome == "ok":
                ok += 1
                sent += 1
            elif outcome == "skipped":
                skipped += 1
            else:
                failed += 1
        console.print(t("eml.submit.batch_summary", ok=ok, skipped=skipped, failed=failed))
        return

    if not positional:
        console.print(f"[warn]{t('eml.submit.usage')}[/warn]")
        return
    chunk_id = _resolve_chunk_id(positional[0])
    if chunk_id is None:
        console.print(f"[warn]{t('eml.show.no_chunk', prefix=positional[0])}[/warn]")
        return
    _submit_one(console, chunk_id)


def _extract_archive(archive: Path, into: Path) -> List[Path]:
    """Extract a tar archive (or copy a single file) and return collected paths."""
    into.mkdir(parents=True, exist_ok=True)
    extracted: List[Path] = []
    try:
        with tarfile.open(archive, "r:*") as tf:
            tf.extractall(into, filter="data")
            for member in tf.getmembers():
                if member.isreg():
                    extracted.append(into / member.name)
        return extracted
    except tarfile.ReadError:
        target = into / archive.name
        if archive.resolve() != target.resolve():
            target.write_bytes(archive.read_bytes())
        return [target]


def _watch_one(console: Console, chunk_id: str) -> bool:
    meta = _load_chunk_meta(chunk_id)
    project_id = meta.get("aristotle_project_id")
    if not project_id:
        console.print(f"[warn]{t('eml.watch.no_project', chunk_id=chunk_id)}[/warn]")
        return False
    archive_dir = _chunk_dir(chunk_id) / "_archive"
    archive_dir.mkdir(parents=True, exist_ok=True)
    archive_path = archive_dir / "solution.tar.gz"

    console.print(f"[info]{t('eml.watch.polling', chunk_id=chunk_id, project_id=project_id)}[/info]")
    try:
        result = _run_aristotle([
            "result", project_id, "--wait", "--destination", str(archive_path),
        ])
    except RuntimeError as e:
        console.print(f"[err]{t('eml.watch.err', chunk_id=chunk_id, error=e)}[/err]")
        return False
    if result.returncode != 0:
        raw = result.stderr or result.stdout or ""
        console.print(Panel(
            raw or "?",
            title=f"[err]{t('eml.watch.err', chunk_id=chunk_id, error='rc!=0')}[/err]",
            border_style="err",
        ))
        return False

    files = _extract_archive(archive_path, archive_dir)
    lean_files = [f for f in files if f.suffix == ".lean"]
    if not lean_files:
        console.print(f"[warn]{t('eml.watch.no_lean_files', chunk_id=chunk_id)}[/warn]")
        return False

    # Aristotle returns the entire project snapshot. The actual NEW proof
    # is the file Aristotle authored — typically `EML.lean` at the project
    # root. Filter the noise out: prefer a top-level `EML.lean`; fall back
    # to any `.lean` whose path stem starts with `EML`; final fallback is
    # the shallowest `.lean` at the project root, excluding the known
    # `LambdaAristotle.lean` umbrella file.
    KNOWN_PROJECT_FILES = {"LambdaAristotle.lean"}
    proof_files = [f for f in lean_files if f.name == "EML.lean"]
    if not proof_files:
        proof_files = [
            f for f in lean_files
            if f.stem.startswith("EML") and f.name not in KNOWN_PROJECT_FILES
        ]
    if not proof_files:
        # Fallback: shallowest unknown .lean at project root.
        min_depth = min(len(f.relative_to(archive_dir).parts) for f in lean_files)
        candidates = [
            f for f in lean_files
            if len(f.relative_to(archive_dir).parts) == min_depth
            and f.name not in KNOWN_PROJECT_FILES
        ]
        proof_files = candidates or lean_files

    # Write JUST the proof file content (no concatenation noise).
    pieces: List[str] = []
    for f in sorted(proof_files):
        pieces.append(_read_text_safe(f).rstrip())
    result_lean = _chunk_dir(chunk_id) / "result.lean"
    result_lean.write_text("\n\n".join(pieces) + "\n", encoding="utf-8")

    # mirror into lean_workspace/EML/Solutions/<chunk_id>.lean
    SOLUTIONS_DIR.mkdir(parents=True, exist_ok=True)
    solution_path = SOLUTIONS_DIR / f"{chunk_id}.lean"
    solution_path.write_text(result_lean.read_text(encoding="utf-8"), encoding="utf-8")

    # update meta + manifest
    meta["status"] = "complete"
    meta["completed_at"] = datetime.now(tz=timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    _save_chunk_meta(chunk_id, meta)
    manifest = _load_manifest()
    for entry in manifest.get("chunks", []):
        if (entry.get("id") or entry.get("chunk_id")) == chunk_id:
            entry["status"] = "complete"
            entry["completed_at"] = meta["completed_at"]
            break
    _save_manifest(manifest)

    console.print(f"[ok]{t('eml.watch.saved', path=solution_path)}[/ok]")
    return True


def _cmd_watch(console: Console, args: List[str]) -> None:
    if not _check_workspace(console):
        return
    do_all = "--all" in args
    positional = [a for a in args if not a.startswith("--")]

    if do_all:
        chunk_ids = _list_chunks()
        any_done = False
        for cid in chunk_ids:
            meta = _load_chunk_meta(cid)
            if str(meta.get("status", "pending")) == "submitted":
                any_done |= _watch_one(console, cid)
        if not any_done:
            console.print("[muted]nothing submitted to watch[/muted]")
        return

    if not positional:
        console.print(f"[warn]{t('eml.watch.usage')}[/warn]")
        return
    chunk_id = _resolve_chunk_id(positional[0])
    if chunk_id is None:
        console.print(f"[warn]{t('eml.show.no_chunk', prefix=positional[0])}[/warn]")
        return
    _watch_one(console, chunk_id)


def _cmd_verify(console: Console, args: List[str]) -> None:
    if not _check_workspace(console):
        return
    if not LEAN_WS.exists():
        console.print(f"[warn]{t('eml.verify.no_workspace')}[/warn]")
        return
    if args:
        chunk_id = _resolve_chunk_id(args[0])
        if chunk_id is None:
            console.print(f"[warn]{t('eml.show.no_chunk', prefix=args[0])}[/warn]")
            return
        targets = [chunk_id]
    else:
        # verify every chunk that has a solution file
        targets = [
            cid for cid in _list_chunks()
            if (SOLUTIONS_DIR / f"{cid}.lean").exists()
        ]

    if not targets:
        console.print(f"[muted]{t('eml.verify.no_artifact', chunk_id='*', path=SOLUTIONS_DIR)}[/muted]")
        return

    for cid in targets:
        artifact = SOLUTIONS_DIR / f"{cid}.lean"
        if not artifact.exists():
            console.print(f"[warn]{t('eml.verify.no_artifact', chunk_id=cid, path=artifact)}[/warn]")
            continue
        rel = artifact.relative_to(LEAN_WS)
        console.print(f"[info]-> lake env lean {rel}[/info]")
        rc, out = _run_with_spinner(
            console,
            ["lake", "env", "lean", str(rel)],
            cwd=LEAN_WS,
            description=f"verify {cid}",
        )
        if rc == 0:
            console.print(Panel(
                out or "(ok)",
                title=f"[ok]{t('eml.verify.ok', chunk_id=cid)}[/ok]",
                border_style="ok",
            ))
        else:
            console.print(Panel(
                out or "(no output)",
                title=f"[err]{t('eml.verify.err', chunk_id=cid, rc=rc)}[/err]",
                border_style="err",
            ))


# ---------------------------------------------------------------------------
# Combine
# ---------------------------------------------------------------------------


_STATUS_BADGE = {
    "complete": "✓",
    "partial":  "◐",
    "submitted": "…",
    "failed":   "✗",
    "pending":  "·",
}


def _build_combined_markdown() -> Optional[Path]:
    chunk_ids = _list_chunks()
    if not chunk_ids:
        return None
    # Sort by leading numeric prefix (001, 002, ..., 045) — chunks were
    # decomposed in the order paper sections appear, so this reads top-down.
    def sort_key(cid: str) -> tuple:
        head = cid.split("_", 1)[0]
        try:
            return (int(head), cid)
        except ValueError:
            return (10_000, cid)
    ordered = sorted(chunk_ids, key=sort_key)

    today = datetime.now().strftime("%Y-%m-%d")
    yaml = [
        "---",
        'title: "EML — hybrid formal/informal report"',
        'subtitle: "Auto-formalization of arXiv:2603.21852 (Odrzywołek)"',
        f'date: "{today}"',
        "lang: en",
        "geometry: margin=2.2cm",
        "documentclass: article",
        "fontsize: 11pt",
        "colorlinks: true",
        "linkcolor: RoyalBlue",
        "header-includes:",
        "  - \\usepackage{amsmath, amssymb}",
        "  - \\usepackage{fvextra}",
        "  - \\DefineVerbatimEnvironment{Highlighting}{Verbatim}{commandchars=\\\\\\{\\},breaklines,breakanywhere,fontsize=\\small}",
        "---",
        "",
    ]

    # Counts for the dashboard table.
    counts = {k: 0 for k in _STATUS_BADGE}
    metas = {cid: _load_chunk_meta(cid) for cid in ordered}
    for cid in ordered:
        s = str(metas[cid].get("status", "pending"))
        counts[s] = counts.get(s, 0) + 1

    sections: List[str] = []
    sections.append("# EML formalization — hybrid report\n")
    sections.append(
        f"This document interleaves the paper *All elementary functions from "
        f"a single binary operator* (arXiv:2603.21852, A. Odrzywołek) with the "
        f"corresponding Lean 4 + Mathlib v4.28 artifacts. Proofs were produced "
        f"by Aristotle (Harmonic) plus hand-curated definitions.\n"
    )

    # ---- Status dashboard --------------------------------------------------
    sections.append("## Status dashboard\n")
    sections.append("| Status | Count | Symbol |")
    sections.append("|---|---:|:---:|")
    label = {"complete": "Verified", "partial": "Partial",
             "submitted": "Submitted", "failed": "Failed", "pending": "Pending"}
    for k in ["complete", "partial", "submitted", "failed", "pending"]:
        sections.append(f"| {label.get(k, k)} | {counts.get(k, 0)} | {_STATUS_BADGE.get(k, '?')} |")
    sections.append(f"| **Total** | **{len(ordered)}** | |")
    sections.append("")

    # ---- Index of chunks ---------------------------------------------------
    sections.append("## Index\n")
    sections.append("| | ID | Title | Kind | Diff | Section |")
    sections.append("|:---:|---|---|---|:---:|---|")
    for cid in ordered:
        m = metas[cid]
        badge = _STATUS_BADGE.get(str(m.get("status", "pending")), "?")
        title = _meta_title(m) or cid
        kind = m.get("kind", "")
        diff = m.get("difficulty", "")
        sec = (m.get("paper_section") or "").replace("|", "/")
        # Render a section anchor link. Pandoc auto-generates anchors from headers.
        anchor = cid.lower().replace("_", "-")
        sections.append(f"| {badge} | [{cid}](#{anchor}) | {title} | {kind} | {diff} | {sec} |")
    sections.append("")

    # ---- Per-chunk dossiers ------------------------------------------------
    for cid in ordered:
        meta = metas[cid]
        title = _meta_title(meta) or cid
        badge = _STATUS_BADGE.get(str(meta.get("status", "pending")), "?")
        status = str(meta.get("status", "pending"))
        section_id = meta.get("paper_section", "")
        sections.append(f"\n## {cid} {badge} {title}\n")
        meta_line = []
        if section_id:
            meta_line.append(f"*Paper section:* `{section_id}`")
        meta_line.append(f"*Status:* `{status}`")
        diff = meta.get("difficulty")
        if diff is not None:
            meta_line.append(f"*Difficulty:* {diff}/5")
        sections.append("  •  ".join(meta_line) + "\n")

        paper_quote = meta.get("paper_quote") or ""
        if paper_quote:
            sections.append(f"> {paper_quote}\n")
        informal = (meta.get("informal_en") or meta.get("informal_pl") or "").strip()
        if informal:
            sections.append(f"\n{informal}\n")
        notes = (meta.get("notes") or "").strip()
        if notes and status in ("partial", "failed"):
            sections.append(f"\n**Notes:** {notes}\n")
        # pick result.lean if available, else target.lean
        cdir = _chunk_dir(cid)
        lean_src = cdir / "result.lean" if (cdir / "result.lean").exists() else cdir / "target.lean"
        if lean_src.exists():
            body = _read_text_safe(lean_src).rstrip()
            sections.append("\n```lean\n" + body + "\n```\n")
        else:
            sections.append("\n*not formalized yet*\n")

    md = "\n".join(yaml) + "\n".join(sections)
    REPORT_MD.parent.mkdir(parents=True, exist_ok=True)
    REPORT_MD.write_text(md, encoding="utf-8")
    return REPORT_MD


def _cmd_combine(console: Console, args: List[str]) -> None:
    if not _check_workspace(console):
        return
    want_pdf = "--pdf" in args
    want_html = "--html" in args

    console.print(f"[info]{t('eml.combine.building', path=REPORT_MD)}[/info]")
    report = _build_combined_markdown()
    if report is None:
        console.print(f"[warn]{t('eml.combine.no_chunks')}[/warn]")
        return

    if want_pdf:
        pdf = _compile_pdf(console, report)
        if pdf is not None:
            console.print(f"[ok]{t('eml.combine.pdf_done', path=pdf)}[/ok]")

    if want_html:
        # Re-render the markdown via Rich for a quick HTML view.
        from io import StringIO
        export_buf = StringIO()
        html_console = Console(record=True, file=export_buf, width=120)
        from rich.markdown import Markdown
        html_console.print(Markdown(report.read_text(encoding="utf-8")))
        REPORT_HTML.parent.mkdir(parents=True, exist_ok=True)
        REPORT_HTML.write_text(html_console.export_html(inline_styles=True), encoding="utf-8")
        console.print(f"[ok]{t('eml.combine.html_done', path=REPORT_HTML)}[/ok]")


def _cmd_refresh_paper(console: Console, args: List[str]) -> None:
    console.print(Panel(
        t("eml.refresh.body"),
        title="[header]eml refresh-paper[/header]",
        border_style="rule",
    ))


# ---------------------------------------------------------------------------
# Dispatch
# ---------------------------------------------------------------------------


SUBCOMMANDS = {
    "list": _cmd_list,
    "ls": _cmd_list,
    "show": _cmd_show,
    "tree": _cmd_tree,
    "status": _cmd_status,
    "submit": _cmd_submit,
    "watch": _cmd_watch,
    "verify": _cmd_verify,
    "combine": _cmd_combine,
    "refresh-paper": _cmd_refresh_paper,
    "refresh": _cmd_refresh_paper,
    "help": lambda console, args: _show_help(console),
    "?": lambda console, args: _show_help(console),
}


def handle(console: Console, args: str) -> None:
    _load_env_files()
    args = (args or "").strip()
    if not args:
        _show_help(console)
        return
    try:
        parts = shlex.split(args)
    except ValueError as e:
        console.print(f"[err]{t('eml.parse_err', error=e)}[/err]")
        return
    sub = parts[0]
    rest = parts[1:]
    handler = SUBCOMMANDS.get(sub)
    if handler is None:
        console.print(
            f"[warn]{t('eml.unknown_sub', sub=sub)}[/warn] {t('eml.unknown_sub_hint')}"
        )
        return
    handler(console, rest)


__all__ = ["SUBCOMMANDS", "handle"]
