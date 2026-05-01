# EML decomposition strategy — arXiv:2603.21852

> Companion to `paper_extracted.md` and `PLAN.md`. This document explains
> *why* the paper was sliced the way it was, what was deferred, and which
> chunks are expected to remain `sorry`-bound forever.

## Overview

The paper makes one philosophical claim ("a single binary operator suffices
for all elementary calculator functions") supported by:

1. A handful of small algebraic identities that are essentially exercises in
   `exp` / `log` rewriting.
2. A discovery chain (Wolfram → Calc 3 → Calc 2 → Calc 1 → Calc 0 → EML)
   reducing primitive operator counts.
3. An exhaustive-search catalogue of EML expressions for the 36 starting
   primitives.
4. A symbolic-regression / training methodology for recovering EML circuits
   from numerical data.

We formalize (1) and (2) in full, (3) partially (constructively for the
short trees, non-constructively / `sorry`-stubbed for the long ones), and
skip (4) entirely — it is a learning method, not a theorem.

The result is **45 chunks** clustered into 9 groups.

## Group rationale

### Group 1 — Foundations (chunks 001–005, difficulty 1)

The basic objects: `def eml`, `inductive EMLTerm`, `def eval`, plus the
two variant operators (`edl`, `-eml ∘ swap`). These are pure definitions;
Aristotle just needs to type-check them.

### Group 2 — Trivial identities (chunks 006–010, difficulty 1–2)

`eml(1,1) = e`, `eml(x,1) = exp x`, etc. Single-rewrite proofs that exercise
`Real.log_one`, `sub_zero`, `Real.exp_pos`. Essentially a sanity check that
our `eml` definition matches the paper's narrative.

### Group 3 — Composite identities (chunks 011–016, difficulty 2–3)

Identity 5 (`ln z` via three nested `eml` calls) is the centrepiece here.
We split the Identity 1 (Exp-Log reduction) into the multiplicative and
additive halves so each is a separate Aristotle target. Most of these
require positivity side conditions on inputs.

### Group 4 — Successor / negation (chunks 017–019, difficulty 2–3)

The "successor" identity `1/(1/(1/x+1)−1) + 1 = −x` (mentioned in passing
in the paper) is a one-shot `field_simp; ring` target. We include it both
because it is one of the few completely closed-form identities in the
paper, and because the same algebra appears inside the longer
"−x in calc-3" chunk.

### Group 5 — Term grammar (chunks 020–023, difficulty 2–3)

`EMLTerm.size` and `size_pos` are arithmetic on the inductive. The
"witness" chunks (022, 023) build small `EMLTerm` values for `e` and
`exp x` and prove their `eval` matches the closed-form. Note: chunk 023
required a grammar tweak — to express `exp x` as an `EMLTerm`, the term
type needs an `x` leaf. We add a parameterized variant `EMLTerm₁` with a
single distinguished variable; the original `EMLTerm` (constants only) is
preserved for the constant-witness chunks.

### Group 6 — Calculator equivalence (chunks 024–029, difficulty 3–4)

One chunk per row pair of Table 2. Each says "anything expressible with
the operator set in row N is expressible with the operator set in
row N+1". The proofs are tedious case-analyses over the unary/binary
primitives in row N; we expect Aristotle to handle the small cases
(`Calc 0 → EML`) and to need extensive `sorry`s for `Wolfram → Calc 3`.

### Group 7 — Completeness sub-cases (chunks 030–042, difficulty 4–5)

For each of the 36 starting primitives, we state "there exists an
`EMLTerm` `t` with `eval t = …`". Constructively we can supply the term
for short entries (e.g. `eml(1,1)` for `e`, K=3); for entries like π (K=193)
or `sqrt` (K=139) we leave a `sorry` and a reference to the
Supplementary Information of the paper. The complex constant `i` and
`sqrt` are flagged as **defer permanently** — formalizing them requires
copying out 100+ literal tree nodes by hand from the paper's
Supplementary, which is beyond the budget of this auto-formalization
pass.

### Group 8 — Master formula counting (chunks 043–044, difficulty 2)

Pure arithmetic / combinatorics. Chunk 043 is `5 · 2^n − 6` parameter
count at level n. Chunk 044 says the number of size-n full-binary
EMLTerms equals the n-th Catalan number — Mathlib has
`Nat.catalan` so this should reduce to a structural induction.

### Group 9 — Wrap-up (chunk 045, difficulty 5)

The umbrella theorem: "for every `f` in the 36-primitive starting basis,
there is an `EMLTerm` whose `eval` matches `f`". This is the disjunction
of chunks 030–042 and is `sorry`-stubbed until they all land.

## Sentences NOT formalized (and why)

- **Section 4.3 (symbolic regression)** — describes a training procedure
  (Gumbel-Softmax, gradient descent over EML coefficients). This is an
  algorithm, not a theorem; nothing to prove.
- **Section 2 (numeric bootstrapping)** — describes a verification
  methodology (substitute Euler-Mascheroni γ, compare to Inverse Symbolic
  Calculator). Also algorithmic.
- **Identity 2 (Euler's formula)** — already formalized in `Mathlib`
  (`Complex.exp_pi_mul_I` etc.); cited in passing in the paper, no new
  content to formalize.
- **Historical / motivational paragraphs** — Sections 1 (Introduction)
  and 5 (Conclusions) are prose; chunked only when they assert a concrete
  mathematical claim.

## Chunks expected to stay `sorry` permanently

| ID  | Reason                                                        |
|-----|---------------------------------------------------------------|
| 034 | π via 193-instruction tree — too long to transcribe by hand   |
| 035 | i via 131-instruction tree — same; also requires `Complex`    |
| 039 | √x via 139-instruction tree — same                            |
| 045 | Master completeness — depends on the above                    |

Other deferred entries (e.g. 0, −1, 2, 1/2, −x, 1/x, x², x+y, x−y, x×y,
x/y, x^y) have K ≤ 105 and we will attempt them; if Aristotle can fit a
literal tree of that size we keep it constructive, otherwise we fall
back to the existential statement plus `sorry`.

## Approximate Aristotle wave plan

- Wave 1 (10 chunks, low risk): 001–010 — definitions and trivial
  identities.
- Wave 2 (12 chunks, medium): 011–023 minus 022/023 if they need term-
  grammar work — composite identities, successor, term arithmetic.
- Wave 3 (15 chunks, medium-hard): 024–029 (calc equivalence) +
  small-K completeness witnesses.
- Wave 4 (8 chunks, hard, accept failures): the long-K completeness
  witnesses + master theorem.

Total: ~45 submissions across four waves, in line with the PLAN.md
budget of "≤30 in the first three waves" since wave 4 is opt-in.
