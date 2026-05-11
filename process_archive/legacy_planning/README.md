# Legacy planning documents

This directory archives planning documents from earlier project phases, kept
for traceability. They are **historical** — current status is tracked in
`OPEN_QUESTIONS.md` (open items) and `First_run.md` (scoreboard).

| File | Originally lived at | Status |
|---|---|---|
| `PLAN_v1_setup.md` | `lambda_lab/proofs/eml/2603_21852/PLAN.md` | The original workspace-setup plan from project genesis (Phases A–E: chunk decomposition, REPL command, Aristotle waves, combine). All phases shipped; the document is a snapshot of the original orchestration design. |
| `PATH_C_PRIME_TASKS.md` | `lambda_lab/proofs/eml/2603_21852/PATH_C_PRIME_TASKS.md` | The Path C′ task slate (chunks 071–083). All 13 chunks ✅ sealed. Plan D/E sections inside this file are pre-structural-ceiling estimates and are superseded by the final findings recorded in `OPEN_QUESTIONS.md`. |
| `Periodicity_plan.md` | `EML/Framework/Complex/Periodicity.md` | Path C′ design notes; the corresponding `Periodicity.lean` is now sealed and supersedes the planning text. |
| `Sheffer_PaperSourcing.md` | `EML/Framework/Sheffer/PaperSourcing.md` | Plan D / E provenance notes; superseded by the Aristotle chunks under `chunks/084`–`089` and by the sealed `Sheffer.lean`. |

The `Periodicity_plan.md` and `Sheffer_PaperSourcing.md` files contain
`sorry` markers inside pseudocode blocks. They are **not part of the
build** and were moved out of `EML/` so that `grep -r sorry EML/` returns
zero hits, matching the project's sorry-free public-API claim.
