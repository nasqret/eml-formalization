# GPT Pro consult bundle — four frontier directions

## What's in here

| File | Purpose |
|---|---|
| [`PROMPT.md`](PROMPT.md) | The actual prompt for GPT Pro. Self-contained problem statement for the four research-grade directions still open in the artefact, with three Q1/Q2/Q3 sub-questions per direction. |
| [`CODE_EXCERPTS.md`](CODE_EXCERPTS.md) | All Lean source Pro needs: the three term grammars (`EMLTermℂ`, `EDLTerm`, `NegEMLTerm`/`NegEMLTermE`), their `eval?` rules, the structural compiler `ELExpr.compile`, the §G boundary lemmas, the universal-minimality corollaries, and the SI §1.5 verbatim list. |
| [`RESPONSE.md`](RESPONSE.md) | Empty placeholder. Paste Pro's verbatim reply here, dated. |

## How to use

1. Open ChatGPT (Pro tier, GPT-5 or whichever Pro model is current).
2. Start a new conversation.
3. Paste the **contents** of `PROMPT.md` first, then immediately follow
   with the **contents** of `CODE_EXCERPTS.md`. (Two messages in one
   conversation, in that order.)
4. Pro will respond with a per-direction recommendation. Drop the
   reply into `RESPONSE.md` for reference.

## Why this consult

`OPEN_QUESTIONS.md` ("Frontier" table, ~line 35) lists four
research-grade directions that are *not* within-reach engineering and
that the artefact will not seal without external mathematical input:

1. **Schanuel-style structural ceiling for Plan D / E.** Formalising
   the informal Aristotle analysis (chunk 085) that exact constants
   like `−1`, `2`, `½` are unreachable from closed EDL terms paired
   with `{1, e}`, conditional on Schanuel's conjecture.
2. **The three §G structural boundary points.** Whether
   `√0`, `arcosh 1`, `hypot(0, 0)` can be sealed by switching to an
   EReal grammar (the chunk-088 pilot grammar `NegEMLTermE` already
   exists for the −EML cousin) or whether the junk-value collision
   re-emerges.
3. **Universal minimality of EML** (paper §5, line 533). The paper
   conjectures `{1, eml}` is the minimal Sheffer system but offers
   no proof. The artefact has two trivial corollaries; the full
   conjecture is paper-open.
4. **The seven SI §1.5 open questions.** The author's own list of
   research questions about the operator landscape itself: taxonomy,
   canonical-form enumeration, constant-free Sheffer, leaf-only
   evaluation, variable-transplant depths, real-only Sheffer,
   `−∞` elimination.

We want Pro's independent triage on each direction:
- which can be made into a Lean-checkable theorem within the existing
  artefact's framework,
- which require external mathematical results we should treat as
  axioms / hypotheses (e.g. Schanuel),
- which are fundamentally open mathematical problems where formalisation
  is premature.

## What we expect back

A markdown reply (≤ 4 pages, one section per direction):

For each of (1)–(4):
1. **Verdict** — one of {tractable now, tractable conditional on X,
   premature, fundamentally open}.
2. **Recommended target lemma** in Lean syntax (or pseudocode) if
   tractable, or the headline mathematical obstruction if not.
3. **Mathlib infrastructure pointers** — which existing Mathlib
   modules are most useful (e.g. `Mathlib.NumberTheory.Transcendental.Schanuel`
   if it exists, `Mathlib.Data.Real.EReal`, etc.).
4. **Cross-direction notes** if any of (1)–(4) share machinery
   (e.g. `NegEMLTermE`'s EReal trick may apply to direction 2 *and*
   direction 4's `−∞` elimination question).

Followed by an overall ranking: which direction is the highest-value
next consult target if we run out of within-reach engineering items.

## After the consult

Drop Pro's response into `RESPONSE.md` in this directory and notify
the assistant. Each direction's verdict updates the corresponding
row of `OPEN_QUESTIONS.md`'s Frontier table.
