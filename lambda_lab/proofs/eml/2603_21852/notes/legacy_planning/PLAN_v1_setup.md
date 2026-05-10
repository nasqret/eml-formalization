# Plan — auto-formalize arXiv:2603.21852 with Aristotle

> "All elementary functions from a single binary operator" — A. Odrzywołek
>
> Goal: produce a navigable hybrid repository where each paragraph of the
> paper is augmented with a formally verified Lean 4 (Mathlib) artifact, and
> all formal artifacts are reachable via a new EML section in the lambda_lab
> dashboard.

## High-level orchestration

```
                ┌─────────────────────────────────────┐
                │  lambda_lab/proofs/eml/2603_21852/  │
                └───────────────┬─────────────────────┘
                                │
        ┌───────────────────────┼──────────────────────────┐
        │                       │                          │
   source/                 chunks/                lean_workspace/
   ├ paper_extracted.md   ├ 001_def_eml/         ├ lakefile.toml
   ├ decomposition.md     ├ 002_eml_e/           ├ EML/
   └ chunks_index.json    ├ 003_eml_exp/         │  ├ Basic.lean
                          ├ ...                   │  └ Functions/
                          └ 050_calc1_eml/       └ lean-toolchain
                                │
                                ▼
                  manifest.json  (status of every chunk)
                                │
                                ▼
                  arist submit ... (parallel waves)
                                │
                                ▼
                  eml combine  →  hybrid PDF/HTML
```

## Phases

### Phase A — Workspace setup (LOCAL ONLY, no API)

1. Create `source/paper_extracted.md` (DONE) — seed material, never re-fetch.
2. Create `lean_workspace/lakefile.toml` requiring Mathlib v4.28.0.
3. Create `lean_workspace/EML/Basic.lean` with `def eml` and the `EMLTerm`
   inductive.
4. Create `lean_workspace/EML/Functions/{Constants,Arithmetic,Transcendental}.lean`
   with `sorry`-stubbed targets that the chunks will populate.

### Phase B — Decomposition (LOCAL, can use one agent)

Walk the paper paragraph-by-paragraph. For each "atomic claim" produce:

```
chunks/<NNN_slug>/
├── chunk.md         informal text + Lean target + dependencies + status
├── target.lean      the Lean statement we want Aristotle to prove
├── meta.json        machine-readable record (project_id, status, paper_section, deps)
└── result.lean      Aristotle's proof, post-fetch (initially absent)
```

Target chunk count: **30-50** (a sweet spot; small enough to track, big enough
to cover the paper meaningfully). Difficulty 1-5.

Suggested ordering by difficulty:
- **1** — pure definitions: `def eml`, `def EMLTerm`, `def eval`
- **2** — single-step identities: `eml 1 1 = e`, `eml x 1 = exp x`
- **3** — two-step identities with side conditions: `ln z = eml(1, eml(eml(1, z), 1))` for `z > 0`
- **4** — calculator-equivalence lemmas (Table 2 rows)
- **5** — completeness statements (mostly `sorry`-stubbed; will defer)

### Phase C — EML REPL command (LOCAL ONLY, no API)

`lambda_lab/lab/commands/eml.py` exposing:

| Command | Purpose |
|---|---|
| `eml list [--status STATE]` | Table of chunks with status |
| `eml show <chunk-id>` | Display chunk: paper text + Lean + status side-by-side |
| `eml tree` | Dependency tree |
| `eml status` | Summary stats |
| `eml submit <chunk-id> [--all-pending] [--limit N]` | Submit to Aristotle; record `project_id` |
| `eml watch <chunk-id> [--all]` | Poll for completion; download solution; copy into `lean_workspace/` |
| `eml verify [<chunk-id>]` | `lake env lean` on the assembled chunk(s) |
| `eml combine [--pdf]` | Build hybrid HTML/Markdown interleaving paper text + formal proofs |
| `eml refresh-paper` | Re-pull the paper extraction (rare) |

Internally reuses `lambda_lab/lab/commands/aristotle.py` for actual submission.

### Phase D — Aristotle submissions (with confirmation)

**First wave** (target ~10 chunks): definitions + the trivial single-step
identities. Submit in parallel; estimated time per chunk ~10-30 min, so
first wave should clear in ~30 min wall-clock.

**Second wave**: medium difficulty identities + calculator-equivalence
lemmas.

**Third wave**: completeness statements (likely many will fail; we accept
that).

User confirmation required before each wave. Each submission is logged
in `manifest.json` with `{chunk_id, project_id, submitted_at, status}`.

### Phase E — Combine

`eml combine` produces:
- `report.md` — interleaves each paper paragraph with its formal Lean
  artifact (or "not formalized" placeholder)
- `report.pdf` — pandoc + xelatex (reuses Aristotle's pipeline)
- `report.html` — for the EML dashboard view (Rich-rendered tables)

The EML dashboard section is just `eml list` + `eml show` invoked via the
REPL; no separate web UI.

## Cost / time estimate

| Phase | Local? | Wall clock | Notes |
|---|---|---|---|
| A — Setup | yes | 10 min |  |
| B — Decomposition | yes | 30-60 min | one agent |
| C — REPL command | yes | 1-2 h | one agent |
| D wave 1 (~10 chunks) | NO (Aristotle) | ~30 min | parallel submissions |
| D wave 2 | NO | ~30-60 min | dependent on wave 1 |
| D wave 3 | NO | ~60 min | many will fail |
| E — Combine | yes | 30 min | reuses pandoc pipeline |

Token cost: each Aristotle job is ~$? to the user (depends on Harmonic
billing). We will not exceed ~30 submissions in the first three waves
combined unless you specifically authorize a wider sweep.

## Open questions for the user

1. **Folder name** — `eml/2603_21852/` is what I picked. Alternative:
   `eml/odrzywolek-2026-eml/`. Both work; first is shorter.
2. **Lean target ambitions** — should we aim for the literal 193-instruction
   π-tree to be formalized, or accept "exists EMLTerm s.t. eval = π" as a
   non-constructive stub? Recommend the latter for the first pass.
3. **Wave 1 size** — I'll start at 10 chunks unless you prefer fewer.
4. **Dashboard section name** — `eml` REPL command name; "EML" is the
   surface label in `lambda_lab` help text.

## Stop conditions

I will pause and ask you before:
- Submitting any wave to Aristotle (cost gate).
- Re-fetching the paper from arXiv (rare).
- Modifying the existing Aristotle integration in any non-additive way.
- Moving anything outside `lambda_lab/proofs/eml/` and the new
  `lambda_lab/lab/commands/eml.py`.
