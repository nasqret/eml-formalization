# EML auto-formalization presentation

A 26-slide reveal-md deck about the EML (`exp(x) - ln(y)`) auto-formalization
project: how Aristotle, Claude, Codex, Mathematica and a human jointly
sealed 66 chunks of the paper *"All elementary functions from a single
binary operator"* into Lean 4 + Mathlib.

## Build

```
./build.sh         # static HTML  -> build/index.html
./build.sh pdf     # PDF (one slide per page) -> eml_presentation.pdf
./build.sh serve   # live server  -> http://localhost:1948
```

Equivalent `make html`, `make pdf`, `make serve`, `make clean`.

The PDF target spawns a tiny static server (`http-server`) on port 18948 and
prints with **headless Google Chrome** against `?print-pdf` — the only
reliable way to get exactly one slide per PDF page. `reveal-md --print` (the
built-in mode) frequently splits tall slides across two pages. If your
Chrome lives elsewhere, set `CHROME_BIN`:

```
CHROME_BIN=/path/to/chromium ./build.sh pdf
```

## Files

- `eml_presentation.md` — the slide deck (reveal-md, 26 slides).
- `assets/theme.css` — custom typography overrides on top of the `simple`
  theme. Tightens fonts and adds a `.compact` slide class.
- `assets/*.svg` — diagrams: factory schematic, wave timeline,
  Swiss-army-knife visual, spec-tightening cycle, multi-agent dispatch,
  pi witness tree, Curry-Howard correspondence.
- `build/` — generated HTML output (gitignored).
- `eml_presentation.pdf` — generated PDF (gitignored).
- `build.sh` / `Makefile` — one-line build entry points.

## Math notes

Reveal-md's bundled MathJax 2 sometimes mishandles the thin/medium spacing
macros `\,` and `\;`. Use `\ ` (backslash-space) or `\quad` for spacing.

## Reuses

- `slides/assets/theme.css` — read-only reference for styling conventions
  in the lecture deck.
- `slides/slides_en.md` — read-only reference for YAML / separator
  conventions.
- `docs/static/formalization_factory.svg` — reused as the slide-9 schematic
  (copied into `assets/`).

The Lean source, the technical report, and the chunk catalogue live in
`lambda_lab/proofs/eml/2603_21852/` and are read-only references for this
deck.
