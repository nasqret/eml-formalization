"""Persistentna historia REPL + append-only dziennik eventów.

- [`HISTORY_FILE`] — `~/.local/share/lambda_lab/repl_history`.
  Używane przez `prompt_toolkit.FileHistory` — strzałka w górę wraca komendy
  po restarcie.
- [`EVENTS_FILE`] — `~/.local/share/lambda_lab/events.jsonl`.
  Jeden JSON na linię, append-only, nie jest czyszczony.
  Format wpisu: `{"ts": "2026-04-24T01:23:45", "kind": "...", ...}`.
"""

from __future__ import annotations

import json
import os
from datetime import datetime
from pathlib import Path
from typing import Any


def _data_dir() -> Path:
    base = os.environ.get("XDG_DATA_HOME") or (Path.home() / ".local" / "share")
    return Path(base) / "lambda_lab"


HISTORY_FILE = _data_dir() / "repl_history"
EVENTS_FILE = _data_dir() / "events.jsonl"


def ensure_dirs() -> None:
    _data_dir().mkdir(parents=True, exist_ok=True)


def log_event(kind: str, **fields: Any) -> None:
    """Dopisuje wpis do dziennika. Błędy IO tłumimy — nie blokują komendy."""
    try:
        ensure_dirs()
        entry = {"ts": datetime.now().isoformat(timespec="seconds"), "kind": kind, **fields}
        with EVENTS_FILE.open("a", encoding="utf-8") as fh:
            fh.write(json.dumps(entry, ensure_ascii=False) + "\n")
    except OSError:
        pass


def read_events(limit: int | None = None) -> list[dict]:
    """Czyta ostatnie ``limit`` eventów (albo wszystkie). Cicho na brak pliku."""
    if not EVENTS_FILE.exists():
        return []
    events: list[dict] = []
    try:
        for line in EVENTS_FILE.read_text(encoding="utf-8").splitlines():
            line = line.strip()
            if not line:
                continue
            try:
                events.append(json.loads(line))
            except json.JSONDecodeError:
                continue
    except OSError:
        return []
    if limit is not None and limit > 0:
        events = events[-limit:]
    return events
