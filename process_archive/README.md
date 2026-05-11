# process_archive/

> **Provenance, not artefact.** Nothing in this directory is part of
> the verified EML formalisation. The verified artefact lives in
> `lambda_lab/proofs/eml/2603_21852/lean_workspace/` and is described
> in the top-level `README.md`, `DASHBOARD.md`, and `AUTHOR_SUMMARY.md`.
>
> This folder is kept so that anyone reviewing **how the proof was
> built** — including the role of AI tooling — can audit the trail
> end-to-end. If you only want to verify the math, you can ignore
> everything here.

## What lives here

| Path | What it is |
|---|---|
| [`chunks/`](chunks/) | Per-statement decomposition of the formalisation. Each numbered directory is a single theorem statement (`target.lean`, `chunk.md` description, `meta.json`) that was either hand-proved or submitted to Harmonic AI's Aristotle proof-search service (`result.lean` when sealed by Aristotle). Many chunks are obsolete because their content has been folded into `EML/Framework/*.lean`. |
| [`gpt_pro_bundle/`](gpt_pro_bundle/) | Three independent-context reviews by GPT Pro (separate sessions, no shared scratchpad), each with prompt + verbatim response + code excerpts: <br>• `trig_widening/` — Path C′ recommendation (range-reduction by substitution). <br>• `frontier_questions/` — research-grade directions (SI §1.5 #5, §G boundary, Plan D ceiling, polynomial-binary impossibility). <br>• `pre_announcement_review/` — SHIP-WITH-FIXES verdict + 9-item punch list executed on 2026-05-11. |
| [`legacy_planning/`](legacy_planning/) | Earlier planning documents (`PLAN.md`, `PATH_C_PRIME_TASKS.md`, `Sheffer_PaperSourcing.md`, `Periodicity_plan.md`) consolidated into `OPEN_QUESTIONS.md` after the frontier sprint. Kept for the audit trail. |
| [`EML_review_bundle/`](EML_review_bundle/) | The bundle assembled for the first GPT Pro review (technical report .tex/.pdf, hybrid report .md/.pdf, presentation .pdf, manifest.json). Working scaffolding; the canonical paper LaTeX it once held has been extracted to top-level [`paper/`](../paper/). |
| [`slides_eml_presentation/`](slides_eml_presentation/) | Original EML deck. Superseded by `slides/ghostday_post_submission/`. |
| [`slides_ghostday/`](slides_ghostday/) | GhostDay deck as delivered. Superseded by `slides/ghostday_post_submission/` (which reflects today's sealed status). |
| [`First_run.md`](First_run.md) | Bootstrap recipe for fresh Claude Code sessions opened in a clone of this repo. Useful if you're using an AI coding assistant to navigate the project. |
| [`AUDIT_REPORT.md`](AUDIT_REPORT.md) | Pre-release engineering audit (dated 2026-05-10). Historical snapshot. |
| [`GPT_PRO_REVIEW_PACKAGE.md`](GPT_PRO_REVIEW_PACKAGE.md) | Earliest GPT Pro review packet (pre-dates the three current bundles in `gpt_pro_bundle/`). |
| [`old_report.{md,html,pdf}`](.) | Earlier write-up of the formalisation. The current write-up lives in `lambda_lab/proofs/eml/2603_21852/report/`. |
| [`paper_decomposition.md`](paper_decomposition.md), [`paper_extracted.md`](paper_extracted.md) | Working extracts of the paper used during the formalisation. The canonical paper sits at [`paper/EML.tex`](../paper/EML.tex). |

## Why keep this rather than delete it?

Three reasons:

1. **Reproducibility of the *process*.** The same way an experimental
   physics paper benefits from raw data alongside the analysed result,
   an AI-assisted formalisation benefits from showing the chunked
   theorem statements and the proof-search returns. Future researchers
   studying AI-assisted theorem proving can compare statement → search
   → integrated proof end-to-end.
2. **Honesty about AI involvement.** The artefact is verified by the
   Lean kernel and does not depend on any AI output — but the *path*
   to the artefact relied on Aristotle proof search and on three GPT
   Pro architectural consults. Keeping the consult transcripts and the
   chunk dumps lets a reader see exactly where AI was used and where
   it was not.
3. **Recoverable if needed.** If a frontier item (e.g. SI §1.5 #5
   d=3 canonical-grammar port) gets picked up later, the chunk
   directories already have the targets and the Aristotle-returned
   simplified-grammar proofs — they're the natural starting point.
