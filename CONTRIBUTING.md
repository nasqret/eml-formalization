# Contributing

## Getting set up

```bash
# Verify prerequisites (elan, lake, python3, git)
make prereqs

# First build (cold cache pulls ~6 GB of Mathlib oleans, takes 30–60 min)
make build

# Run the public-API sanity probe
make sanity

# Print the scoreboard
make scoreboard
```

A bootstrap recipe for fresh checkouts is in [`process_archive/First_run.md`](process_archive/First_run.md).

## Repository layout

| Path | What lives there |
|---|---|
| [`lambda_lab/proofs/eml/2603_21852/lean_workspace/EML/`](lambda_lab/proofs/eml/2603_21852/lean_workspace/EML/) | The Lean artefact. Public API in `Framework/PaperClaims.lean` and `Framework/Sheffer.lean`. |
| [`lambda_lab/proofs/eml/2603_21852/notes/`](lambda_lab/proofs/eml/2603_21852/notes/) | Expository writeup (`proof_structure.tex/.pdf`). |
| [`paper/`](paper/) | Canonical paper LaTeX + Supplementary Information PDF. |
| [`web/eml-tree-builder/`](web/eml-tree-builder/) | Interactive in-browser EML tree compiler. Live at <https://nasqret.github.io/eml-formalization/>. |
| [`slides/ghostday_post_submission/`](slides/ghostday_post_submission/) | Post-submission deck reflecting today's sealed status. |
| [`eagle_scripts/`](eagle_scripts/) | PCSS Eagle HPC SLURM scripts. |
| [`process_archive/`](process_archive/) | Provenance: Aristotle chunks, GPT Pro consult bundles, superseded decks, pre-release audit, legacy planning notes. Not part of the verified artefact, kept for traceability. |

## Pull-request flow

The project follows a standard fork-and-PR model.

1. Fork the repo.
2. Create a feature branch off `main`: `feat/<short-description>` for code, `docs/<topic>` for documentation-only changes.
3. Commit with descriptive messages — the convention is `<area>: <imperative-summary>` followed by a body explaining the *why* (not the *what*; `git diff` shows that).
4. Run `make build` locally; the CI workflow will re-run it on the PR.
5. Open the PR against `main`. The PR body should include a one-paragraph summary, a test-plan checklist, and links to any related issues.
6. **Don't merge stray commits to `main` directly** — use the PR-driven flow so the CI gate fires.

## Code style

### Lean

- Default to **`set_option linter.unusedSimpArgs true`** (the project default). If a `simp` invocation needs unused arguments for clarity or to avoid a name collision, scope `set_option linter.unusedSimpArgs false in` to that one declaration.
- **No `sorry`** in any module reachable from the `EML` root. Pre-flight your changes with `grep -E '\bsorry\b' EML/` before pushing.
- **No `axiom` declarations** outside of testing scaffolds. The artefact relies only on Mathlib's standard noncomputable axioms (classical choice, function/propositional extensionality).
- Witness theorems live in `EML/Framework/PaperClaims.lean` (EML) or `EML/Framework/Sheffer.lean` (Sheffer cousins). Helpers and macros live in `EML/Framework/Complex/{Closures,Builders}/`.
- Prefer **identity-driven witness restructuring** over branch-cut bookkeeping (this is the lesson from Path C′).

### Python (CLI scaffolding)

- Format with `black`/`ruff`. The package follows PEP 8 + 88-column lines.
- The CLI lives in `lambda_lab/lab/commands/`; submit a chunk via `python -m lambda_lab.lab.commands.eml submit <chunk-id>`.

### Markdown

- Tables for status / scoreboards.
- Code fences with language tags (` ```lean`, ` ```bash`, etc.).
- Internal links should resolve from the file's own directory.

## Working with chunks

Chunks (under `process_archive/chunks/`) are atomic theorem statements that were submitted independently to the Aristotle proof-search service during development. They are kept as provenance, not as part of the verified artefact. Each chunk is a directory with:

- `chunk.md` — human-readable description (what's the target, why, dependencies).
- `meta.json` — machine-readable metadata (id, status, dependencies, Aristotle project id).
- `target.lean` — the theorem statement with `sorry`.
- `result.lean` — the Aristotle-returned proof, *if* the chunk was sealed via Aristotle. Hand-coded chunks lift directly into the framework and don't need this file.

To re-submit a chunk (e.g. when iterating an open frontier item):

```bash
cd process_archive/chunks/<chunk-id>
aristotle submit "Prove the theorem in target.lean. <strategy hints>" --project-dir .
```

To fetch a completed chunk:

```bash
aristotle result <project-id> --destination /tmp/result.tar.gz
tar -xzf /tmp/result.tar.gz -C /tmp/result/
cp /tmp/result/project_aristotle/target.lean <chunk-dir>/result.lean
```

Then update `meta.json` to mark `status: complete` and record the `aristotle_project_id`.

## Reporting issues

Open issues at https://github.com/nasqret/eml-formalization/issues. Useful templates:

- **Bug report:** include `lake build` output, the exact failing identity, the file/line, and the expected behaviour.
- **Counter-example:** include the input that breaks a paper claim, the expected vs actual evaluation, and which `paper_claim_*` is affected.
- **Build issue:** include OS, Lean toolchain (`lean --version`), Mathlib commit, and the full lake output.

## Reviewer expectations

The maintainer reviews PRs with a focus on:

1. **Correctness**: `lake build` passes; no new `sorry`s; no axiom additions.
2. **Compositionality**: new lemmas should fit the existing `Framework/` layering, not introduce a parallel construction.
3. **Documentation**: every new public theorem has a docstring citing the paper line / SI section / Aristotle chunk that justifies it.
4. **Naming**: paper-faithful (`edl_paper_claim_*`, `negEml_paper_claim_*`, etc.). Don't introduce ad-hoc names.

Turnaround is typically 1–3 days for routine changes, longer for architectural shifts.

## Licence

Contributions are accepted under the project's dual licence: Apache
License 2.0 for code, CC BY-SA 4.0 for documentation. See
[`LICENSING.md`](LICENSING.md) for the per-file rules, [`LICENSE`](LICENSE)
for the Apache text, and [`LICENSE-DOCS`](LICENSE-DOCS) for the CC
text. By submitting a contribution you agree to license it under the
applicable file's licence.

## Acknowledgements

See the README's "Authors and acknowledgements" section for the contributor list. Contributions are credited via co-author lines in commit messages.
