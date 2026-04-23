"""Komendy interaktywne Lambda Lab.

Każda komenda jest zdefiniowana w osobnym module i rejestrowana
w ``REGISTRY`` — słowniku ``name → handler(console, args)``.
"""

from __future__ import annotations

from typing import Callable, Dict

from rich.console import Console


CommandHandler = Callable[[Console, str], None]


# rejestrowane dynamicznie w repl.py
REGISTRY: Dict[str, CommandHandler] = {}
