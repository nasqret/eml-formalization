# GhostDay 2026 — full presentation

This is the working folder for the full presentation:
**"Automatic verification of mathematical theorems with AI"**
by dr Bartosz Naskręcki, GhostDay 2026.

## Folder layout

| Subfolder | Purpose |
|---|---|
| `source_decks/` | **Drop your existing PowerPoint files here.** I'll read them, extract content, and merge useful general material into the unified deck. |
| `assets/` | Diagrams, logos, images for the unified deck. |
| `build/` | Generated outputs — HTML, PDF, PPTX. |

## Where to put your existing PowerPoints

Upload (or `cp`) all relevant `.pptx` files into:

```
/Users/airbartek/claude/eml-formalization/process_archive/slides_ghostday/source_decks/
```

A useful naming convention while uploading multiple decks:

```
source_decks/
  2024_lecture_intro.pptx        ← general intro / what is formal verification
  2025_aristotle_demo.pptx       ← Aristotle in action
  2025_lambda_calculus.pptx      ← Curry-Howard / type theory
  ...
```

Anything similar works. I'll pull what's useful from each.

## Output formats

I'll produce three artefacts:

| Artefact | Purpose |
|---|---|
| `build/ghostday.html` | Live reveal.js presentation (animations, transitions) |
| `build/ghostday.pdf`  | Print-ready PDF (one slide per page) |
| `build/ghostday.pptx` | PowerPoint version (editable in Keynote / PowerPoint) |

The PowerPoint version is what you'd use if you need to make last-minute edits on the conference laptop, or if the venue requires it.

## How the merge will work

1. You upload `.pptx` files into `source_decks/`
2. I convert each via `pandoc` to extract text content and embedded images
3. I identify which slides cover **general material the audience needs** (intro to formal verification, Curry-Howard, AI prover landscape) — not the EML case study
4. I merge that general material into the unified reveal-md deck, keeping the existing EML / GPT Pro / framework story intact
5. I tighten the diagrams (arrows, alignment, typography)
6. I export to all three formats

## Note on PowerPoint as the canonical format

reveal-md (current source format) gives us:
- Pixel-perfect typography, MathJax, CSS animations
- Easier git diffing (Markdown is text)
- Single source of truth

PowerPoint export is reasonable but loses:
- Live MathJax (renders math as static images)
- Custom CSS classes (theme.css won't apply)
- SVG interactivity

**Recommendation:** keep reveal-md as canonical, generate PPTX as a *transport format* for venue compatibility. If you want PowerPoint as canonical, say so and I'll restructure.
