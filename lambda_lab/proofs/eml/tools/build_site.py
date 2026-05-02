#!/usr/bin/env python3
"""Static site generator for the EML formalization (arXiv:2603.21852).

Reads the manifest + per-chunk metadata from
``lambda_lab/proofs/eml/2603_21852/`` and writes a navigable HTML companion
to ``docs/`` at the repository root.  No build step is required: the output
is plain HTML/CSS/JS, suitable for GitHub Pages (Settings → Pages → Source:
main /docs).

Usage::

    python3 lambda_lab/proofs/eml/tools/build_site.py

The script is idempotent — running it again overwrites the previous output
verbatim.  No file under ``chunks/`` or ``lean_workspace/`` is modified.
"""

from __future__ import annotations

import datetime as _dt
import html
import json
import os
import re
import shutil
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional

# ---------------------------------------------------------------------------
# Paths
# ---------------------------------------------------------------------------

THIS_FILE = Path(__file__).resolve()
REPO_ROOT = THIS_FILE.parents[4]                   # falenty_2026/
EML_ROOT = REPO_ROOT / "lambda_lab" / "proofs" / "eml" / "2603_21852"
CHUNKS_DIR = EML_ROOT / "chunks"
SOLUTIONS_DIR = EML_ROOT / "lean_workspace" / "EML" / "Solutions"
MANIFEST_PATH = EML_ROOT / "manifest.json"

DOCS_DIR = REPO_ROOT / "docs"
CHUNK_OUT_DIR = DOCS_DIR / "chunk"
STATIC_DIR = DOCS_DIR / "static"

PAPER_ID = "arXiv:2603.21852"
PAPER_TITLE = "All elementary functions from a single binary operator"
PAPER_AUTHOR = "Andrzej Odrzywołek"
GITHUB_REPO_URL = "https://github.com/"  # generic placeholder; user can override

# ---------------------------------------------------------------------------
# Status presentation
# ---------------------------------------------------------------------------

STATUS_BADGE = {
    "complete": ("ok",       "✓", "complete"),
    "partial":  ("partial",  "◐", "partial"),
    "pending":  ("pending",  "·", "pending"),
    "blocked":  ("blocked",  "!", "blocked"),
    "stub":     ("partial",  "◐", "stub"),
}


def badge(status: str) -> str:
    cls, sym, label = STATUS_BADGE.get(
        status.lower(), ("unknown", "?", status)
    )
    return (
        f'<span class="badge badge-{cls}" title="{html.escape(label)}">'
        f'<span class="badge-sym">{sym}</span>'
        f'<span class="badge-label">{html.escape(label)}</span></span>'
    )


# ---------------------------------------------------------------------------
# Loading
# ---------------------------------------------------------------------------

def load_manifest() -> dict:
    with MANIFEST_PATH.open(encoding="utf-8") as fh:
        return json.load(fh)


def load_chunk_meta(chunk_id: str) -> dict:
    meta_path = CHUNKS_DIR / chunk_id / "meta.json"
    if not meta_path.exists():
        return {}
    with meta_path.open(encoding="utf-8") as fh:
        return json.load(fh)


def load_chunk_md(chunk_id: str) -> str:
    md_path = CHUNKS_DIR / chunk_id / "chunk.md"
    if not md_path.exists():
        return ""
    return md_path.read_text(encoding="utf-8")


def load_lean_source(chunk_id: str) -> tuple[str, str]:
    """Return (source_label, source_text).

    Prefers the verified Solutions/ file, falls back to result.lean, then
    target.lean.
    """
    sol = SOLUTIONS_DIR / f"{chunk_id}.lean"
    if sol.exists() and sol.stat().st_size > 0:
        return (
            f"lean_workspace/EML/Solutions/{chunk_id}.lean",
            sol.read_text(encoding="utf-8"),
        )
    result = CHUNKS_DIR / chunk_id / "result.lean"
    if result.exists() and result.stat().st_size > 0:
        return (
            f"chunks/{chunk_id}/result.lean",
            result.read_text(encoding="utf-8"),
        )
    target = CHUNKS_DIR / chunk_id / "target.lean"
    if target.exists():
        return (
            f"chunks/{chunk_id}/target.lean (target only)",
            target.read_text(encoding="utf-8"),
        )
    return ("(no Lean source available)", "")


# ---------------------------------------------------------------------------
# chunk.md parsing — extract the structured fields without depending on a
# full Markdown library.
# ---------------------------------------------------------------------------

_SECTION_RE = re.compile(r"^##\s+(.+?)\s*$", re.MULTILINE)


def parse_chunk_md(md: str) -> Dict[str, str]:
    """Pull the named sections out of a chunk.md file.

    Returns a dict keyed by lower-cased section name (e.g. ``"informal (pl)"``).
    """
    sections: Dict[str, str] = {}
    if not md:
        return sections
    indices = [(m.start(), m.group(1)) for m in _SECTION_RE.finditer(md)]
    for i, (start, name) in enumerate(indices):
        end = indices[i + 1][0] if i + 1 < len(indices) else len(md)
        body = md[start:end]
        # drop the heading line itself
        body = body.split("\n", 1)[1] if "\n" in body else ""
        sections[name.strip().lower()] = body.strip()
    return sections


def extract_quote(section_text: str) -> str:
    """Pull the blockquote text out of a "## Source quote" section."""
    if not section_text:
        return ""
    lines = []
    for ln in section_text.splitlines():
        stripped = ln.lstrip()
        if stripped.startswith(">"):
            lines.append(stripped[1:].lstrip())
        elif lines:  # stop at the first non-quote line after we started
            break
    return "\n".join(lines).strip()


# ---------------------------------------------------------------------------
# HTML rendering primitives
# ---------------------------------------------------------------------------

def page_shell(*, title: str, body: str, depth: int = 0,
               extra_head: str = "") -> str:
    """Wrap *body* in the standard HTML scaffold.

    ``depth`` is how many directories deep this page is from ``docs/``
    (0 for index, 1 for chunk pages).
    """
    base = "../" * depth
    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{html.escape(title)}</title>
<link rel="stylesheet" href="{base}static/main.css">
<link rel="stylesheet"
      href="https://cdnjs.cloudflare.com/ajax/libs/highlight.js/11.9.0/styles/atom-one-light.min.css"
      crossorigin="anonymous"
      onerror="this.onerror=null;this.remove();">
<script defer src="https://cdnjs.cloudflare.com/ajax/libs/highlight.js/11.9.0/highlight.min.js"
        crossorigin="anonymous"></script>
<script defer src="{base}static/lean-hljs.js"></script>
<script defer src="{base}static/main.js"></script>
{extra_head}
</head>
<body>
<a class="skip" href="#main">Skip to content</a>
<header class="site-header">
  <div class="wrap">
    <a class="brand" href="{base}index.html">
      <span class="brand-mark">EML</span>
      <span class="brand-text">formalization</span>
    </a>
    <nav class="site-nav">
      <a href="{base}index.html">Index</a>
      <a href="https://arxiv.org/abs/2603.21852" rel="noopener" target="_blank">Paper</a>
      <a href="{base}README.html">About</a>
    </nav>
  </div>
</header>
<main id="main" class="wrap">
{body}
</main>
<footer class="site-footer">
  <div class="wrap">
    <p>
      Built {_dt.date.today().isoformat()} from
      <code>lambda_lab/proofs/eml/2603_21852/manifest.json</code>.
      Lean 4 + Mathlib v4.28.0.
    </p>
    <p class="muted">arXiv:2603.21852 — A. Odrzywołek — CC BY 4.0.</p>
  </div>
</footer>
</body>
</html>
"""


def render_index(manifest: dict, chunks: List[Dict[str, Any]]) -> str:
    stats = manifest.get("stats", {})
    by_status = stats.get("by_status", {})
    by_kind = stats.get("by_kind", {})
    by_diff = stats.get("by_difficulty", {})

    # actual computed counts (the manifest's by_status numbers are pre-update,
    # so prefer the live count from the chunk list).
    live_status: Dict[str, int] = {}
    for c in chunks:
        live_status[c["status"]] = live_status.get(c["status"], 0) + 1

    def stat_card(label: str, value: Any, mod: str = "") -> str:
        return (
            f'<div class="stat {mod}"><div class="stat-value">{value}</div>'
            f'<div class="stat-label">{html.escape(label)}</div></div>'
        )

    dashboard_cards = [
        stat_card("total chunks", stats.get("total_chunks", len(chunks))),
        stat_card("complete", live_status.get("complete", 0), "stat-ok"),
        stat_card("partial",  live_status.get("partial", 0),  "stat-partial"),
        stat_card("pending",  live_status.get("pending", 0),  "stat-pending"),
    ]

    # difficulty + kind breakdowns as compact bars
    def _kv_table(title: str, mapping: Dict[str, Any]) -> str:
        items = sorted(mapping.items(), key=lambda kv: str(kv[0]))
        rows = "".join(
            f"<tr><th>{html.escape(str(k))}</th><td>{v}</td></tr>"
            for k, v in items
        )
        return (
            f'<section class="breakdown">'
            f'<h3>{html.escape(title)}</h3>'
            f'<table>{rows}</table></section>'
        )

    rows = []
    for c in chunks:
        meta = c["meta"]
        title_en = meta.get("title_en", c["id"])
        title_pl = meta.get("title_pl", "")
        kind = meta.get("kind", c.get("kind", ""))
        difficulty = meta.get("difficulty", c.get("difficulty", ""))
        section = meta.get("paper_section", "")
        deps = meta.get("depends_on") or []
        deps_html = (
            ", ".join(
                f'<a href="chunk/{d}.html" class="dep">{html.escape(d)}</a>'
                for d in deps
            )
            if deps else '<span class="muted">—</span>'
        )
        rows.append(
            "<tr>"
            f"<td>{badge(c['status'])}</td>"
            f'<td><a class="chunk-id" href="chunk/{c["id"]}.html">'
            f"{html.escape(c['id'])}</a></td>"
            f"<td>{html.escape(title_en)}"
            + (f'<div class="title-pl">{html.escape(title_pl)}</div>'
               if title_pl else "")
            + "</td>"
            f"<td><span class=\"kind kind-{html.escape(kind)}\">"
            f"{html.escape(kind)}</span></td>"
            f"<td><span class=\"diff diff-{difficulty}\">"
            f"{difficulty}/5</span></td>"
            f"<td class=\"section\">{html.escape(section)}</td>"
            f"<td class=\"deps\">{deps_html}</td>"
            "</tr>"
        )

    body = f"""
<section class="hero">
  <h1>EML formalization — interactive index</h1>
  <p class="lede">All {stats.get("total_chunks", len(chunks))} chunks of
    <a href="https://arxiv.org/abs/2603.21852" rel="noopener" target="_blank">
      {PAPER_ID}</a>
    ({html.escape(PAPER_AUTHOR)}), formally verified in Lean 4 + Mathlib v4.28.0.</p>
</section>

<section class="dashboard">
  <h2>Status dashboard</h2>
  <div class="stats">
    {''.join(dashboard_cards)}
  </div>
  <div class="breakdowns">
    {_kv_table("By kind", by_kind)}
    {_kv_table("By difficulty", by_diff)}
    {_kv_table("By status (manifest)", by_status)}
  </div>
</section>

<section class="index">
  <div class="index-header">
    <h2>All chunks</h2>
    <input type="search" id="filter" placeholder="Filter by id, title, kind…"
           aria-label="Filter chunks">
  </div>
  <table class="chunks-table" id="chunks-table">
    <thead>
      <tr>
        <th>Status</th>
        <th>ID</th>
        <th>Title</th>
        <th>Kind</th>
        <th>Diff.</th>
        <th>Paper section</th>
        <th>Depends on</th>
      </tr>
    </thead>
    <tbody>
      {''.join(rows)}
    </tbody>
  </table>
</section>
"""
    return page_shell(
        title="EML formalization — interactive index",
        body=body,
        depth=0,
    )


def render_aristotle_block(meta: dict) -> str:
    fields = [
        ("Aristotle project_id", meta.get("aristotle_project_id")),
        ("Submitted",             meta.get("submitted_at")),
        ("Completed",             meta.get("completed_at")),
        ("Notes",                 meta.get("notes")),
    ]
    rows = []
    for label, value in fields:
        if not value:
            continue
        rows.append(
            f"<dt>{html.escape(label)}</dt>"
            f"<dd>{html.escape(str(value))}</dd>"
        )
    if not rows:
        return ""
    return (
        '<aside class="aristotle">'
        '<h3>Aristotle metadata</h3>'
        f'<dl>{"".join(rows)}</dl>'
        "</aside>"
    )


def render_paper_panel(meta: dict, chunk_md_sections: Dict[str, str]) -> str:
    section = meta.get("paper_section", "")
    quote = (
        meta.get("paper_quote")
        or extract_quote(chunk_md_sections.get("source quote", ""))
    )
    informal_pl = (
        meta.get("informal_pl")
        or chunk_md_sections.get("informal (pl)", "")
    )
    informal_en = (
        meta.get("informal_en")
        or chunk_md_sections.get("informal (en)", "")
    )

    parts = []
    if section:
        parts.append(
            f'<p class="paper-section"><span class="lbl">Section</span>'
            f' {html.escape(section)}</p>'
        )
    if quote:
        parts.append(
            f'<blockquote class="paper-quote">{html.escape(quote)}</blockquote>'
        )
    if informal_en:
        parts.append(
            '<div class="informal informal-en">'
            '<h4>Informal explanation (EN)</h4>'
            f'<p>{html.escape(informal_en)}</p></div>'
        )
    if informal_pl:
        parts.append(
            '<div class="informal informal-pl">'
            '<h4>Wyjaśnienie nieformalne (PL)</h4>'
            f'<p>{html.escape(informal_pl)}</p></div>'
        )
    return "\n".join(parts) or "<p class=\"muted\">No paper text available.</p>"


def render_lean_panel(source_label: str, source_text: str) -> str:
    if not source_text.strip():
        return (
            f'<p class="muted">No Lean source found for this chunk '
            f'(<code>{html.escape(source_label)}</code>).</p>'
        )
    escaped = html.escape(source_text)
    return f"""
<div class="lean-meta">
  <span class="lean-path">{html.escape(source_label)}</span>
  <button type="button" class="copy-btn" data-copy-target="lean-code">Copy</button>
</div>
<pre class="lean-pre"><code id="lean-code" class="language-lean">{escaped}</code></pre>
"""


def render_chunk_page(c: Dict[str, Any], all_chunks: List[Dict[str, Any]],
                      idx: int) -> str:
    meta = c["meta"]
    chunk_md = c["chunk_md"]
    chunk_md_sections = parse_chunk_md(chunk_md)
    title_en = meta.get("title_en", c["id"])
    title_pl = meta.get("title_pl", "")
    kind = meta.get("kind", "")
    difficulty = meta.get("difficulty", "")
    deps = meta.get("depends_on") or []
    deps_html = (
        ", ".join(
            f'<a href="{d}.html">{html.escape(d)}</a>' for d in deps
        ) if deps else '<span class="muted">—</span>'
    )

    source_label, source_text = c["lean"]
    paper_html = render_paper_panel(meta, chunk_md_sections)
    lean_html = render_lean_panel(source_label, source_text)
    aristotle_html = render_aristotle_block(meta)

    prev_link = ""
    next_link = ""
    if idx > 0:
        prev = all_chunks[idx - 1]
        prev_link = (
            f'<a class="nav-prev" id="nav-prev" href="{prev["id"]}.html" '
            f'rel="prev">← {html.escape(prev["id"])}</a>'
        )
    if idx + 1 < len(all_chunks):
        nxt = all_chunks[idx + 1]
        next_link = (
            f'<a class="nav-next" id="nav-next" href="{nxt["id"]}.html" '
            f'rel="next">{html.escape(nxt["id"])} →</a>'
        )

    body = f"""
<article class="chunk">
  <header class="chunk-head">
    <p class="crumbs"><a href="../index.html">← back to index</a></p>
    <h1>
      <span class="chunk-id-pill">{html.escape(c["id"])}</span>
      <span class="chunk-title">{html.escape(title_en)}</span>
    </h1>
    {f'<p class="title-pl">{html.escape(title_pl)}</p>' if title_pl else ''}
    <ul class="meta-strip">
      <li><span class="lbl">Section</span>
          {html.escape(meta.get("paper_section", "—"))}</li>
      <li><span class="lbl">Status</span> {badge(c["status"])}</li>
      <li><span class="lbl">Kind</span>
          <span class="kind kind-{html.escape(kind)}">{html.escape(kind)}</span></li>
      <li><span class="lbl">Difficulty</span>
          <span class="diff diff-{difficulty}">{difficulty}/5</span></li>
      <li><span class="lbl">Depends on</span> {deps_html}</li>
    </ul>
  </header>

  <section class="view-switcher" aria-label="View switcher">
    <div class="view-toggle" role="radiogroup" aria-label="Choose view">
      <input type="radio" name="view" id="view-paper"  value="paper">
      <label for="view-paper" title="Show paper text only (1)">
        <span class="key">1</span> Paper
      </label>
      <input type="radio" name="view" id="view-lean"   value="lean">
      <label for="view-lean" title="Show Lean source only (2)">
        <span class="key">2</span> Lean
      </label>
      <input type="radio" name="view" id="view-split"  value="split" checked>
      <label for="view-split" title="Show both side by side (3)">
        <span class="key">3</span> Side by side
      </label>
    </div>

    <div class="panes" data-view="split">
      <section class="pane pane-paper" aria-label="Paper">
        <h2>Paper</h2>
        {paper_html}
      </section>
      <section class="pane pane-lean" aria-label="Lean source">
        <h2>Lean</h2>
        {lean_html}
      </section>
    </div>
  </section>

  {aristotle_html}

  <nav class="chunk-nav" aria-label="Chunk navigation">
    <div class="nav-side">{prev_link}</div>
    <div class="nav-mid"><a href="../index.html">index</a></div>
    <div class="nav-side nav-side-right">{next_link}</div>
  </nav>
</article>
"""
    title = f"{c['id']} — {title_en} — EML formalization"
    return page_shell(title=title, body=body, depth=1)


# ---------------------------------------------------------------------------
# Static assets
# ---------------------------------------------------------------------------

CSS = """\
/* EML formalization — site styles. */
:root {
  --bg: #fbfaf6;
  --bg-elev: #ffffff;
  --ink: #182233;
  --ink-soft: #4a566b;
  --muted: #8b94a3;
  --rule: #e6e1d5;
  --rule-strong: #cfc8b8;
  --accent: #1f3a5f;
  --accent-soft: #ecf1f7;
  --code-bg: #f5f2e8;
  --ok: #2f7a3a;
  --ok-soft: #e6f1e8;
  --warn: #b56b14;
  --warn-soft: #fbeed7;
  --pending: #707683;
  --pending-soft: #ececec;
  --blocked: #a32626;
  --blocked-soft: #fbe6e6;
  --serif: ui-serif, Georgia, "Iowan Old Style", Cambria, "Times New Roman", serif;
  --sans:  -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Helvetica, Arial, sans-serif;
  --mono:  ui-monospace, "SF Mono", "JetBrains Mono", Menlo, Consolas, monospace;
  --maxw:  72rem;
}

* { box-sizing: border-box; }
html, body { margin: 0; padding: 0; }
body {
  background: var(--bg);
  color: var(--ink);
  font-family: var(--sans);
  font-size: 16px;
  line-height: 1.55;
  -webkit-font-smoothing: antialiased;
}
.wrap { max-width: var(--maxw); margin: 0 auto; padding: 0 1.25rem; }

a { color: var(--accent); text-decoration: none; }
a:hover { text-decoration: underline; }

.skip {
  position: absolute; left: -9999px; top: auto; width: 1px; height: 1px;
  overflow: hidden;
}
.skip:focus { position: static; width: auto; height: auto; padding: .5rem; }

/* ---------- header / footer ---------- */
.site-header {
  background: var(--accent);
  color: #f6f1e2;
  padding: .8rem 0;
  border-bottom: 1px solid #15263d;
}
.site-header .wrap {
  display: flex; align-items: center; justify-content: space-between;
  gap: 1rem;
}
.site-header a { color: #f6f1e2; }
.brand { font-weight: 600; letter-spacing: .02em; }
.brand-mark {
  display: inline-block; padding: .15rem .5rem; margin-right: .35rem;
  border: 1px solid #f6f1e2; border-radius: .25rem;
  font-family: var(--mono); font-size: .85rem;
}
.brand-text { font-family: var(--serif); font-style: italic; }
.site-nav a { margin-left: 1rem; font-size: .95rem; }

.site-footer {
  margin-top: 4rem; padding: 1.5rem 0; background: #f0ebdb;
  border-top: 1px solid var(--rule); color: var(--ink-soft);
  font-size: .9rem;
}
.site-footer p { margin: .25rem 0; }
.muted { color: var(--muted); }

/* ---------- index page ---------- */
.hero { padding: 2rem 0 1rem; }
.hero h1 {
  font-family: var(--serif); font-size: 2.2rem; margin: 0 0 .5rem;
  color: var(--accent);
}
.lede { font-size: 1.05rem; color: var(--ink-soft); margin: 0; }

.dashboard { padding: 1.5rem 0; }
.dashboard h2, .index h2 {
  font-family: var(--serif); color: var(--accent);
  border-bottom: 1px solid var(--rule); padding-bottom: .25rem;
}

.stats {
  display: grid; gap: .75rem;
  grid-template-columns: repeat(auto-fit, minmax(8rem, 1fr));
  margin: 1rem 0;
}
.stat {
  background: var(--bg-elev); border: 1px solid var(--rule);
  border-radius: .35rem; padding: .9rem 1rem;
}
.stat-value { font-size: 1.7rem; font-weight: 600; line-height: 1; }
.stat-label { font-size: .85rem; color: var(--ink-soft); margin-top: .35rem; }
.stat-ok      { border-left: 3px solid var(--ok); }
.stat-partial { border-left: 3px solid var(--warn); }
.stat-pending { border-left: 3px solid var(--pending); }

.breakdowns {
  display: grid; gap: 1rem;
  grid-template-columns: repeat(auto-fit, minmax(14rem, 1fr));
}
.breakdown {
  background: var(--bg-elev); border: 1px solid var(--rule);
  border-radius: .35rem; padding: .75rem 1rem;
}
.breakdown h3 { margin: 0 0 .5rem; font-size: .95rem; color: var(--ink-soft);
  font-family: var(--sans); font-weight: 600; }
.breakdown table { width: 100%; border-collapse: collapse; font-size: .9rem; }
.breakdown th { text-align: left; font-weight: 500; color: var(--ink); }
.breakdown td { text-align: right; color: var(--ink-soft); }

.index { padding: 1.5rem 0 3rem; }
.index-header {
  display: flex; align-items: center; justify-content: space-between;
  flex-wrap: wrap; gap: 1rem; margin-bottom: .5rem;
}
.index-header input[type="search"] {
  flex: 1 1 14rem; max-width: 22rem; padding: .4rem .6rem;
  border: 1px solid var(--rule-strong); border-radius: .25rem;
  font: inherit; background: var(--bg-elev);
}

.chunks-table {
  width: 100%; border-collapse: collapse; font-size: .92rem;
  background: var(--bg-elev); border: 1px solid var(--rule);
}
.chunks-table thead th {
  background: var(--accent-soft); text-align: left; padding: .55rem .65rem;
  font-weight: 600; border-bottom: 1px solid var(--rule-strong);
  color: var(--accent);
}
.chunks-table tbody td {
  padding: .5rem .65rem; border-bottom: 1px solid var(--rule);
  vertical-align: top;
}
.chunks-table tbody tr:hover { background: #fffbe9; }
.chunks-table .chunk-id {
  font-family: var(--mono); font-size: .9em;
  background: var(--code-bg); padding: .05rem .35rem; border-radius: .2rem;
}
.chunks-table .title-pl {
  font-size: .82em; color: var(--muted); font-style: italic;
}
.chunks-table .deps a { font-family: var(--mono); font-size: .85em; }
.chunks-table .section { color: var(--ink-soft); font-size: .88em; }

/* ---------- badges, kinds, difficulty pills ---------- */
.badge {
  display: inline-flex; align-items: center; gap: .35rem;
  padding: .1rem .45rem; border-radius: 1rem; font-size: .78rem;
  border: 1px solid transparent; line-height: 1.4;
}
.badge-sym { font-weight: 700; }
.badge-ok      { background: var(--ok-soft);      color: var(--ok);
                 border-color: #b8d8be; }
.badge-partial { background: var(--warn-soft);    color: var(--warn);
                 border-color: #e8c98a; }
.badge-pending { background: var(--pending-soft); color: var(--pending);
                 border-color: #d2d2d2; }
.badge-blocked { background: var(--blocked-soft); color: var(--blocked);
                 border-color: #e7b3b3; }
.badge-unknown { background: #eee; color: #555; border-color: #ddd; }

.kind { font-size: .8rem; padding: .05rem .4rem; border-radius: .2rem;
  background: #efeadb; color: var(--ink-soft); }
.kind-definition             { background: #e3edf7; color: #1c4d7a; }
.kind-identity               { background: #f3e9d6; color: #7a5418; }
.kind-theorem                { background: #e6e9f5; color: #344082; }
.kind-calculator-equivalence { background: #e9f0e7; color: #2d5e36; }

.diff { font-family: var(--mono); font-size: .82rem;
  background: var(--code-bg); padding: .05rem .35rem; border-radius: .2rem; }
.diff-1 { color: #2f7a3a; }
.diff-2 { color: #4a7a2f; }
.diff-3 { color: #7a6b15; }
.diff-4 { color: #a35919; }
.diff-5 { color: #a32626; }

/* ---------- chunk page ---------- */
.chunk { padding-top: 1.25rem; }
.chunk-head h1 {
  font-family: var(--serif); margin: .25rem 0 .25rem;
  font-size: 1.7rem; color: var(--accent);
  display: flex; align-items: baseline; flex-wrap: wrap; gap: .6rem;
}
.chunk-id-pill {
  font-family: var(--mono); font-size: .9rem;
  background: var(--accent); color: #f6f1e2;
  padding: .15rem .55rem; border-radius: .25rem;
}
.chunk-title { font-style: italic; }
.title-pl { color: var(--muted); font-style: italic; margin: 0 0 .5rem; }

.crumbs { margin: 0 0 .25rem; font-size: .9rem; }

.meta-strip {
  list-style: none; padding: .5rem .75rem; margin: .75rem 0 1rem;
  background: var(--bg-elev); border: 1px solid var(--rule);
  border-radius: .35rem;
  display: flex; flex-wrap: wrap; gap: .25rem 1.2rem;
  font-size: .9rem;
}
.meta-strip li { display: flex; align-items: center; gap: .35rem; }
.lbl { color: var(--muted); font-size: .78rem; text-transform: uppercase;
  letter-spacing: .04em; }

/* view toggle */
.view-toggle {
  display: inline-flex; border: 1px solid var(--rule-strong);
  border-radius: .35rem; overflow: hidden; background: var(--bg-elev);
  margin: .5rem 0 1rem;
}
.view-toggle input { position: absolute; opacity: 0; pointer-events: none; }
.view-toggle label {
  padding: .35rem .8rem; cursor: pointer; font-size: .92rem;
  border-right: 1px solid var(--rule);
  display: inline-flex; align-items: center; gap: .35rem;
  color: var(--ink-soft);
}
.view-toggle label:last-of-type { border-right: 0; }
.view-toggle input:checked + label {
  background: var(--accent); color: #f6f1e2;
}
.view-toggle .key {
  font-family: var(--mono); font-size: .72rem;
  background: rgba(0,0,0,.08); padding: 0 .35rem; border-radius: .15rem;
}
.view-toggle input:checked + label .key {
  background: rgba(255,255,255,.18); color: #f6f1e2;
}

.panes {
  display: grid; gap: 1rem;
  transition: grid-template-columns .25s ease;
}
.panes[data-view="split"] { grid-template-columns: 1fr 1fr; }
.panes[data-view="paper"] { grid-template-columns: 1fr; }
.panes[data-view="paper"] .pane-lean  { display: none; }
.panes[data-view="lean"]  { grid-template-columns: 1fr; }
.panes[data-view="lean"]  .pane-paper { display: none; }

.pane {
  background: var(--bg-elev); border: 1px solid var(--rule);
  border-radius: .35rem; padding: 1rem 1.1rem;
  min-width: 0;  /* allow inner <pre> to scroll */
}
.pane h2 {
  margin: 0 0 .75rem; font-family: var(--serif);
  font-size: 1.05rem; color: var(--accent); font-weight: 600;
  border-bottom: 1px solid var(--rule); padding-bottom: .25rem;
}
.paper-section { margin: 0 0 .5rem; font-size: .9rem; color: var(--ink-soft); }
.paper-quote {
  margin: .5rem 0; padding: .55rem .85rem; background: var(--accent-soft);
  border-left: 3px solid var(--accent); font-family: var(--serif);
  font-size: 1.02rem; font-style: italic; color: var(--accent);
}
.informal { margin: .85rem 0; }
.informal h4 {
  margin: 0 0 .25rem; font-size: .82rem; text-transform: uppercase;
  letter-spacing: .05em; color: var(--muted); font-weight: 600;
}
.informal p { margin: 0; }
.informal-pl p { color: var(--ink-soft); }

.lean-meta {
  display: flex; align-items: center; justify-content: space-between;
  gap: .5rem; margin-bottom: .35rem; font-size: .82rem;
  color: var(--ink-soft);
}
.lean-path { font-family: var(--mono); }
.copy-btn {
  font: inherit; font-size: .8rem;
  border: 1px solid var(--rule-strong); background: var(--bg);
  border-radius: .25rem; padding: .15rem .55rem; cursor: pointer;
  color: var(--ink); transition: background .15s;
}
.copy-btn:hover { background: var(--accent-soft); }
.copy-btn.copied { background: var(--ok-soft); color: var(--ok);
  border-color: #b8d8be; }
.lean-pre {
  margin: 0; background: var(--code-bg); border: 1px solid var(--rule);
  border-radius: .25rem; padding: .65rem .85rem; overflow: auto;
  max-height: 60vh;
}
.lean-pre code {
  font-family: var(--mono); font-size: .82rem; line-height: 1.45;
  background: transparent !important;
}
.hljs { background: transparent !important; }

/* aristotle metadata */
.aristotle {
  margin: 1.5rem 0; background: var(--bg-elev); border: 1px solid var(--rule);
  border-left: 3px solid var(--warn); border-radius: .35rem;
  padding: .75rem 1rem;
}
.aristotle h3 {
  margin: 0 0 .5rem; font-size: .9rem; color: var(--ink-soft);
  text-transform: uppercase; letter-spacing: .04em; font-weight: 600;
}
.aristotle dl { margin: 0; display: grid;
  grid-template-columns: max-content 1fr; gap: .15rem .75rem; }
.aristotle dt { color: var(--muted); font-size: .85rem; }
.aristotle dd { margin: 0; font-size: .9rem; word-break: break-word; }

/* nav */
.chunk-nav {
  margin-top: 2rem; padding-top: 1rem; border-top: 1px solid var(--rule);
  display: grid; grid-template-columns: 1fr auto 1fr; gap: 1rem;
  align-items: center;
}
.nav-side { font-family: var(--mono); font-size: .9rem; }
.nav-side-right { text-align: right; }
.nav-mid { font-size: .9rem; color: var(--muted); }

/* ---------- responsive ---------- */
@media (max-width: 720px) {
  .panes[data-view="split"] { grid-template-columns: 1fr; }
  .meta-strip { font-size: .85rem; gap: .25rem .9rem; }
  .chunk-head h1 { font-size: 1.4rem; }
  .chunks-table { font-size: .85rem; }
  .chunks-table .deps, .chunks-table .section { display: none; }
}
"""

JS = r"""
// EML formalization — interactive site logic.
// Pure ES2017, no dependencies. Loaded with `defer`.

(function () {
  "use strict";

  const STORAGE_KEY = "eml.viewPreference";
  const VALID_VIEWS = ["paper", "lean", "split"];

  function pickInitialView() {
    const saved = localStorage.getItem(STORAGE_KEY);
    if (saved && VALID_VIEWS.indexOf(saved) >= 0) return saved;
    // Default: side-by-side on wide screens, paper on mobile.
    return window.matchMedia("(max-width: 720px)").matches ? "paper" : "split";
  }

  function applyView(view) {
    if (VALID_VIEWS.indexOf(view) < 0) view = "split";
    const panes = document.querySelector(".panes");
    if (panes) panes.setAttribute("data-view", view);
    const radio = document.querySelector(
      `.view-toggle input[value="${view}"]`
    );
    if (radio) radio.checked = true;
    try { localStorage.setItem(STORAGE_KEY, view); } catch (_) { /* private mode */ }
  }

  function wireToggle() {
    const inputs = document.querySelectorAll('.view-toggle input[name="view"]');
    if (!inputs.length) return;
    inputs.forEach(function (i) {
      i.addEventListener("change", function () {
        if (i.checked) applyView(i.value);
      });
    });
    applyView(pickInitialView());
  }

  function wireCopyButtons() {
    document.querySelectorAll(".copy-btn").forEach(function (btn) {
      btn.addEventListener("click", function () {
        const target = document.getElementById(btn.dataset.copyTarget);
        if (!target) return;
        const text = target.innerText;
        const done = function () {
          const orig = btn.textContent;
          btn.textContent = "Copied";
          btn.classList.add("copied");
          setTimeout(function () {
            btn.textContent = orig;
            btn.classList.remove("copied");
          }, 1400);
        };
        if (navigator.clipboard && navigator.clipboard.writeText) {
          navigator.clipboard.writeText(text).then(done, function () {
            fallbackCopy(text); done();
          });
        } else {
          fallbackCopy(text); done();
        }
      });
    });
  }
  function fallbackCopy(text) {
    const ta = document.createElement("textarea");
    ta.value = text;
    ta.style.position = "fixed"; ta.style.opacity = "0";
    document.body.appendChild(ta); ta.select();
    try { document.execCommand("copy"); } catch (_) {}
    document.body.removeChild(ta);
  }

  function wireKeyboard() {
    document.addEventListener("keydown", function (ev) {
      // Ignore if user is typing in a field
      const tgt = ev.target;
      if (tgt && (tgt.tagName === "INPUT" || tgt.tagName === "TEXTAREA"
                  || tgt.isContentEditable)) {
        return;
      }
      if (ev.metaKey || ev.ctrlKey || ev.altKey) return;
      switch (ev.key) {
        case "1": applyView("paper"); break;
        case "2": applyView("lean");  break;
        case "3": applyView("split"); break;
        case "ArrowLeft": {
          const prev = document.getElementById("nav-prev");
          if (prev) { ev.preventDefault(); window.location.href = prev.href; }
          break;
        }
        case "ArrowRight": {
          const next = document.getElementById("nav-next");
          if (next) { ev.preventDefault(); window.location.href = next.href; }
          break;
        }
      }
    });
  }

  function wireFilter() {
    const input = document.getElementById("filter");
    const table = document.getElementById("chunks-table");
    if (!input || !table) return;
    const rows = Array.prototype.slice.call(table.tBodies[0].rows);
    input.addEventListener("input", function () {
      const q = input.value.trim().toLowerCase();
      rows.forEach(function (row) {
        if (!q) { row.style.display = ""; return; }
        const text = row.textContent.toLowerCase();
        row.style.display = text.indexOf(q) >= 0 ? "" : "none";
      });
    });
  }

  function runHighlight() {
    if (window.hljs && typeof window.hljs.highlightAll === "function") {
      try { window.hljs.highlightAll(); } catch (_) { /* graceful */ }
    }
  }

  document.addEventListener("DOMContentLoaded", function () {
    wireToggle();
    wireCopyButtons();
    wireKeyboard();
    wireFilter();
    // Highlight runs after the lean grammar registers itself (also on DCL).
    setTimeout(runHighlight, 0);
  });
})();
"""

LEAN_HLJS = r"""
// Minimal Lean 4 grammar for highlight.js.  Registered if hljs is loaded;
// otherwise the script is a no-op and the code blocks stay plain monospace.
(function () {
  "use strict";
  if (typeof window === "undefined" || !window.hljs) return;
  const KEYWORDS = [
    "abbrev", "axiom", "by", "class", "def", "deriving", "do", "else",
    "end", "example", "exists", "export", "extends", "fun", "have",
    "hiding", "if", "import", "in", "inductive", "infix", "infixl",
    "infixr", "instance", "let", "macro", "macro_rules", "match",
    "mutual", "namespace", "noncomputable", "notation", "open", "partial",
    "prefix", "private", "protected", "renaming", "return", "section",
    "set_option", "show", "structure", "suffices", "syntax", "termination_by",
    "theorem", "then", "this", "universe", "unsafe", "variable", "where",
    "with", "λ", "fun", "forall", "∀", "∃", "from", "for", "as"
  ].join(" ");
  const BUILT_INS = [
    "Type", "Prop", "Sort", "True", "False", "And", "Or", "Not", "Eq",
    "Iff", "Real", "Nat", "Int", "ℝ", "ℕ", "ℤ", "ℚ", "ℂ", "Mathlib", "EML"
  ].join(" ");
  const LITERALS = "true false";
  hljs.registerLanguage("lean", function (hljs) {
    return {
      name: "Lean",
      aliases: ["lean", "lean4"],
      keywords: { keyword: KEYWORDS, built_in: BUILT_INS, literal: LITERALS },
      contains: [
        // doc-comment /-! ... -/
        hljs.COMMENT(/\/-!/, /-\//, { relevance: 0 }),
        hljs.COMMENT(/\/-/, /-\//, { relevance: 0 }),
        hljs.COMMENT(/--/, /$/),
        { className: "string",
          begin: /"/, end: /"/,
          contains: [{ begin: /\\./ }] },
        { className: "string",
          begin: /'(?:[^'\\]|\\.)'/ },
        { className: "number",
          begin: /\b\d+(\.\d+)?\b/, relevance: 0 },
        { className: "symbol",
          // Greek / sub-script identifiers are common in Mathlib.
          begin: /[A-Za-zα-ωΑ-Ω_][A-Za-zα-ωΑ-Ω_0-9'₀-₉]*\.[A-Za-zα-ωΑ-Ω_][A-Za-zα-ωΑ-Ω_0-9'₀-₉]*/,
          relevance: 0 },
        { className: "operator",
          begin: /:=|=>|->|→|↦|⟨|⟩|≤|≥|≠|∘|∀|∃/, relevance: 0 }
      ]
    };
  });
})();
"""

README = """\
# EML formalization site

This directory hosts the static GitHub Pages site for
**[arXiv:2603.21852](https://arxiv.org/abs/2603.21852)** — *“All elementary
functions from a single binary operator”* by A. Odrzywołek — formally
verified chunk-by-chunk in Lean 4 + Mathlib v4.28.0.

* `index.html` — landing page with the status dashboard and the indexed
  table of all 45 chunks.
* `chunk/<chunk_id>.html` — one page per chunk with a three-way toggle
  (Paper / Lean / Side-by-side) and Aristotle metadata.
* `static/` — CSS, JS, and the Lean grammar for highlight.js.
* `_config.yml` — Jekyll config so the site renders on GitHub Pages.

## Regenerating

The site is produced by a single Python script:

```
python3 lambda_lab/proofs/eml/tools/build_site.py
```

The generator only reads from
`lambda_lab/proofs/eml/2603_21852/` (manifest, chunk metadata) and
`lambda_lab/proofs/eml/2603_21852/lean_workspace/EML/Solutions/`
(verified Lean source). Nothing inside those trees is modified.

## Enabling GitHub Pages

In your GitHub repository: **Settings → Pages → Source: `main` branch /
`/docs` folder**. The site will be available at
`https://<user>.github.io/<repo>/`.
"""

CONFIG_YML = """\
title: EML Formalization
description: All 45 chunks of arXiv:2603.21852 formally verified in Lean 4 + Mathlib v4.28.0
theme: jekyll-theme-minimal
"""


# ---------------------------------------------------------------------------
# Top-level build
# ---------------------------------------------------------------------------

def write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def build() -> None:
    manifest = load_manifest()
    raw_chunks = manifest.get("chunks", [])
    if not raw_chunks:
        print("manifest has no chunks; aborting", file=sys.stderr)
        sys.exit(1)

    # Hydrate each chunk with its meta + chunk.md + Lean source.
    chunks: List[Dict[str, Any]] = []
    for c in raw_chunks:
        cid = c["id"]
        meta = load_chunk_meta(cid) or c
        # Carry forward defaults from the manifest entry where meta lacks them.
        for k, v in c.items():
            meta.setdefault(k, v)
        chunk_md = load_chunk_md(cid)
        lean = load_lean_source(cid)
        chunks.append({
            "id": cid,
            "status": (meta.get("status") or c.get("status") or "unknown"),
            "kind":   meta.get("kind", c.get("kind", "")),
            "difficulty": meta.get("difficulty", c.get("difficulty", "")),
            "meta": meta,
            "chunk_md": chunk_md,
            "lean": lean,
        })

    # ---- write static assets ----
    write(STATIC_DIR / "main.css",   CSS)
    write(STATIC_DIR / "main.js",    JS)
    write(STATIC_DIR / "lean-hljs.js", LEAN_HLJS)

    # ---- top-level files ----
    write(DOCS_DIR / "index.html",   render_index(manifest, chunks))
    write(DOCS_DIR / "_config.yml",  CONFIG_YML)
    write(DOCS_DIR / "README.md",    README)

    # ---- per-chunk pages ----
    for idx, c in enumerate(chunks):
        page = render_chunk_page(c, chunks, idx)
        write(CHUNK_OUT_DIR / f"{c['id']}.html", page)

    # Tiny convenience: a passthrough HTML view of README so the header
    # link doesn't 404. (GitHub Pages renders Markdown, but locally we
    # want something that works without Jekyll.)
    readme_html = page_shell(
        title="About — EML formalization",
        body=(
            "<article class=\"chunk\"><header class=\"chunk-head\">"
            "<h1>About this site</h1></header>"
            "<p>The companion site for the EML formalization of "
            "<a href=\"https://arxiv.org/abs/2603.21852\">arXiv:2603.21852</a>.</p>"
            "<p>The full README lives in <code>docs/README.md</code> and is "
            "rendered by GitHub Pages. Generator script: "
            "<code>lambda_lab/proofs/eml/tools/build_site.py</code>.</p>"
            "<p><a href=\"index.html\">← back to index</a></p></article>"
        ),
        depth=0,
    )
    write(DOCS_DIR / "README.html", readme_html)

    # ---- summary ----
    n_chunk_pages = len(chunks)
    print(f"  wrote: {DOCS_DIR / 'index.html'}")
    print(f"  wrote: {DOCS_DIR / '_config.yml'}")
    print(f"  wrote: {DOCS_DIR / 'README.md'}")
    print(f"  wrote: {DOCS_DIR / 'README.html'}")
    print(f"  wrote: {STATIC_DIR / 'main.css'}")
    print(f"  wrote: {STATIC_DIR / 'main.js'}")
    print(f"  wrote: {STATIC_DIR / 'lean-hljs.js'}")
    print(f"  wrote: {n_chunk_pages} chunk pages under {CHUNK_OUT_DIR}/")
    print(f"  total HTML files: {1 + n_chunk_pages + 1}"
          " (index + chunks + README.html)")


if __name__ == "__main__":
    build()
