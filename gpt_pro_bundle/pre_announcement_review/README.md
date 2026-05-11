# GPT Pro pre-announcement review bundle

## What's in here

| File | Purpose |
|---|---|
| [`PROMPT.md`](PROMPT.md) | The actual prompt for GPT Pro. Self-contained verification request covering mathematical correctness, Lean architecture honesty, public-announcement readiness, and explicit concerns we have flagged ourselves. |
| [`CODE_EXCERPTS.md`](CODE_EXCERPTS.md) | Lean source of every new public theorem added during the post-submission frontier sprint (6 new modules), with file:line references. |
| [`PROJECT_SCOREBOARD.md`](PROJECT_SCOREBOARD.md) | Headline numbers Pro can use to sanity-check claims in the prompt against the actual artefact: 100 public theorems, 8062 lake jobs, sorry-free, etc. |
| [`RESPONSE.md`](RESPONSE.md) | Empty placeholder. Paste Pro's verbatim reply here once we have it. |

## How to use

This bundle follows the pattern of the previous two consult bundles
(`trig_widening/` from 2026-05-08 and `frontier_questions/` from
2026-05-10):

1. Open ChatGPT (Pro tier).
2. Start a new conversation.
3. Paste the **contents** of `PROMPT.md` first.
4. Immediately follow with the **contents** of `CODE_EXCERPTS.md` and `PROJECT_SCOREBOARD.md`.
5. Pro will respond with a pre-announcement review. Drop the reply into `RESPONSE.md`.

## What we want from Pro

A **double-check before the public announcement**. The artefact is at
8062 jobs, sorry-free, with 100 public theorems. We want Pro to flag:

- **Mathematical concerns** — anything in the new modules whose
  statement doesn't faithfully formalize the underlying paper claim.
- **Lean-style concerns** — anything that might draw fire from the
  formal-methods community (e.g., a typeclass without an instance,
  a `Prop` def standing in for a theorem, witness-family quantifier
  flips that aren't acknowledged).
- **Honesty / over-claiming** — anywhere we say "sealed" but the
  thing in main is weaker than that.
- **Embarrassment risk** — anything that, if pointed out by the
  source paper's author or a reviewer, would look bad.
- **Public-API correctness** — confirmation that the headline
  numbers (100 theorems, 8062 jobs, 0 sorry) line up with what
  `import EML` actually exposes.

A "ship it" verdict is welcome but not the goal — the goal is to
catch anything that would cost more to fix after the announcement
than before.

## Context for Pro

Pro has already audited this artefact twice:

1. **2026-05-08** — `trig_widening/`. Recommended Path~C′
   (range-reduction by substitution) to widen the trig family to
   full real domains. Sealed in `paper_claim_{sin_full, arctan_full,
   tan_full}` (March 2026 commits).

2. **2026-05-10** — `frontier_questions/`. Ranked four research-grade
   directions; recommended specific Lean targets and Mathlib lemmas
   for each. All four directions now have substantive Lean content
   on `main`.

This third pass is a sanity check on the assembly, not a fresh
direction-setting consult.
