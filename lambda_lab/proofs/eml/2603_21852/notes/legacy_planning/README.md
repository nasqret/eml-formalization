# Legacy planning documents

This directory archives planning documents that were originally drafted alongside the Lean modules they describe, before the corresponding `.lean` proofs were sealed. They are kept for traceability and to record the intermediate design reasoning.

| File | Originally lived at | Status |
|---|---|---|
| `Periodicity_plan.md` | `EML/Framework/Complex/Periodicity.md` | Path C′ design notes; the corresponding `Periodicity.lean` is now sealed and supersedes the planning text. |
| `Sheffer_PaperSourcing.md` | `EML/Framework/Sheffer/PaperSourcing.md` | Plan D / E provenance notes; superseded by the Aristotle chunks under `chunks/084`–`089` and by the sealed `Sheffer.lean`. |

These files contain `sorry` markers inside pseudocode blocks. They are **not part of the build** and were moved out of `EML/` so that `grep -r sorry EML/` returns zero hits, matching the project's sorry-free public-API claim.
