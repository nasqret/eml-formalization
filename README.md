# EML formalization — arXiv:2603.21852

Lean 4 + Mathlib v4.28 formalization of *"All elementary functions
from a single binary operator"* (Andrzej Odrzywołek, arXiv:2603.21852),
together with the orchestration scaffolding (Aristotle CLI, Eagle HPC
scripts, Mathematica entry-point) used to drive the proof.

This repository is an **extracted slice** of a larger workspace
(`falenty-2026` lambda-lab project). It contains *only* the artefacts
relevant to the EML proof itself — see `lambda_lab/proofs/eml/2603_21852/`
for the formalisation, `lambda_lab/lab/commands/aristotle.py` and
`lambda_lab/lab/commands/eml.py` for the proof-tooling CLI, plus
`mathematica/` and `eagle_scripts/` for the auxiliary backends.

## Headline result

> **All 36 paper primitives are formalized completely on a non-empty
> open subdomain of their natural domain — modulo three structural
> boundary points (`√0`, `arcosh 1`, `hypot(0, 0)`).**

Each paper primitive is sealed via a literal `EMLTermℂ` (or `EMLTerm`,
real fragment) witness term whose `eval?` matches the paper's stated
value, with the Lean kernel as the only acceptance criterion.

## Repository layout

| Path | Purpose |
|---|---|
| `lambda_lab/proofs/eml/2603_21852/` | The Lean artefact. Subtrees `lean_workspace/EML/Framework/` (the public API), `chunks/` (per-statement decomposition), `notes/` (the expository paper on the proof structure), `report/` (the auto-generated hybrid report). |
| `lambda_lab/proofs/lean_aristotle/` | The Lake project Aristotle submissions return into. |
| `lambda_lab/lab/commands/aristotle.py` | CLI integration with Harmonic AI's Aristotle proof search. |
| `lambda_lab/lab/commands/eml.py` | Per-chunk submission / verification commands for the EML proof. |
| `EML_review_bundle_sources/` | Paper sources (`paper_source/EML.tex`), the Supplementary Information PDF, and the bibliography. |
| `eagle_scripts/` | PCSS Eagle HPC SLURM scripts (`rebuild_cache.sbatch`, `verify_all.sbatch`, …). |
| `mathematica/` | Entry-point for the Mathematica side: a stub pointing at the upstream `VA00/SymbolicRegressionPackage` repository where the `VerifyBaseSet` procedure that originally discovered the EML operator lives. |
| `slides/` | Three EML slide decks: the original `eml_presentation/`, the GhostDay 2026 `ghostday/` (submitted), and `ghostday_post_submission/` (post-submission widening update). |

## Where to look first

| Goal | Start here |
|---|---|
| Read the formal claim, primitive by primitive | `lambda_lab/proofs/eml/2603_21852/lean_workspace/EML/Framework/PaperClaims.lean` |
| Understand the architecture of the proof | `lambda_lab/proofs/eml/2603_21852/notes/proof_structure.pdf` |
| See what's open / what plans exist | `lambda_lab/proofs/eml/2603_21852/OPEN_QUESTIONS.md` |
| Author-facing synopsis suitable to share | `lambda_lab/proofs/eml/2603_21852/AUTHOR_SUMMARY.md` |
| Re-verify locally | `cd lambda_lab/proofs/eml/2603_21852/lean_workspace && lake build` (~8 054 jobs, sorry-free) |
| Re-verify on PCSS Eagle | `eagle_scripts/verify_all.sbatch` |

## What is sealed

* **Atoms (7)** — full domain.
* **Real unaries (8)** — full natural domain except `√0` (§G boundary).
* **Hyperbolic family (6)** — full natural domain except `arcosh 1`.
* **Real binaries (8)** — full natural domain except `hypot(0, 0)`.
* **Trig (6)** — wide subdomains around `0`:
  * `cos` on `ℝ \ {0}`,
  * `sin`, `arctan` on `(-π, π) \ {0}`,
  * `arccos`, `arcsin` on full open `(-1, 1)`,
  * `tan` on `(-π/2, π/2) \ {0}`.
* **`π`, `i`** — full literal.

## Build instructions

### Lean / Lake

```bash
cd lambda_lab/proofs/eml/2603_21852/lean_workspace
lake build
```

The Mathlib snapshot is pinned in `lakefile.toml`. First build pulls
~6 GB of olean cache; subsequent builds are incremental.

### Python CLI scaffold (optional)

```bash
pip install -e .
```

The package installs the `lambda_lab` namespace. Aristotle commands
are reachable as Python modules:

```bash
python -m lambda_lab.lab.commands.aristotle submit "<prompt>"
python -m lambda_lab.lab.commands.eml list
python -m lambda_lab.lab.commands.eml watch <chunk-id>
```

(The original `lambda-lab` console script is not carried in this
extract; the CLI is invoked module-style.)

## Provenance

This repository was extracted from the larger `falenty-2026` workspace
on 2026-05-08 via `git filter-repo`, retaining only the paths relevant
to the EML formalisation and its proof-tooling scaffold. The git
history of every retained file is preserved. The "EML notes:
structure-of-proof expository paper" commit (`b9f1fcd` at the time of
extraction) is the most recent EML commit.

## Authors and acknowledgements

* **Bartosz Naskręcki** (UAM Poznań / Politechnika Warszawska) —
  formalisation lead.
* **Aristotle** (Harmonic) — proof search for many individual chunks.
* **GPT Pro** — independent code review across multiple rounds;
  recommended the structural-compiler architecture and the
  Cayley-quotient route for `tan`.
* **Claude** (Anthropic) — orchestration, scaffolding, post-submission
  trig widenings.
* **Mathematica / `VerifyBaseSet`** — enumeration and witness candidate
  search (upstream at `github.com/VA00/SymbolicRegressionPackage`).
* **Codex** (OpenAI) — paraphrase and informalisation.
* **Mathlib community** — the underlying Lean library.
* **Andrzej Odrzywołek** — the source paper.

## Licence

MIT — see `LICENSE`.
