# EML auto-formalization presentation

A 26-slide reveal-md deck about the EML (`exp(x) - ln(y)`) auto-formalization
project: how Aristotle, Claude, Codex, Mathematica and a human jointly
sealed 66 chunks of the paper *"All elementary functions from a single
binary operator"* into Lean 4 + Mathlib.

## Build

```
./build.sh        # static HTML  -> build/eml_presentation.html
./build.sh pdf    # PDF          -> eml_presentation.pdf
./build.sh serve  # live server  -> http://localhost:1948
```

Equivalent `make html`, `make pdf`, `make serve`, `make clean`.

## Files

- `eml_presentation.md` — the slide deck (reveal-md, 26 slides).
- `assets/` — diagrams (SVG): the factory schematic, wave timeline,
  Swiss-army-knife visual, spec-tightening cycle, multi-agent dispatch,
  pi witness tree, Curry-Howard correspondence.
- `build/` — generated HTML output (gitignore).
- `build.sh` / `Makefile` — one-line build entry points.

## Reuses

- `slides/assets/theme.css` — read-only reference for styling conventions.
- `slides/slides_en.md` — read-only reference for YAML / separator conventions.
- `docs/static/formalization_factory.svg` — reused as the slide-9 schematic
  (copied into `assets/`).

The Lean source, the technical report, and the chunk catalogue live in
`lambda_lab/proofs/eml/2603_21852/` and are read-only references for this
deck.
