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

## Round 2: missing primitives (chunks 050-070)

After sealing the original 45 chunks, this round captures the remaining
claims of the paper's Supplementary Table S2 (steps 12-32 of the
discovery chain) plus three scope-extension chunks. The 45-chunk Round 1
covered: the EML grammar (001-005), basic identities (006-018), the
calculator-reduction chain (024-029), term arithmetic (020-021,
043-044), constant witnesses (022, 030-035), unary witnesses (036-039),
binary witnesses (040-042), and the eleven-conjunct umbrella (045).
Round 2 fills the remaining S2 entries — the "stepping stones" the
paper builds on top of the EML core to recover the standard 36-button
calculator: division, average, half, log_x, hypot, sigmoid, the three
hyperbolics and their inverses, and the six circular trig functions.

### Why these were deferred

Round 1 stopped at primitives whose witness recipes did not require
already-built primitives from Round 1 itself. The Table S2 entries
beyond step 12 all exhibit non-trivial dependencies on prior witnesses
(e.g. `cosh = avg(exp x, exp(-x))` needs `avg` from step 14, which
itself needs `half` and `add`). Decomposing them in a second pass keeps
each chunk's `depends_on` list small and makes the wave-submission
schedule cleaner.

### Group structure (21 new chunks)

- **Group A — real-domain stepping stones (050-055, 6 chunks).**
  `x/y, avg, half, log_x y, hypot, σ(sigmoid)`. All built directly
  on top of Round-1 chunks 011/036/037/038/040/041 plus chunks
  050 and 052 within the group itself. Difficulty 4.

- **Group B — hyperbolic functions (056-058, 3 chunks).**
  `cosh, sinh, tanh`. Recipes from Table S2 are direct EML macros
  (`cosh = avg(exp x, exp(-x))`, `sinh = eml(x, e^{cosh x})`,
  `tanh = sinh/cosh`). Difficulty 4.

- **Group C — inverse hyperbolic functions (059-061, 3 chunks).**
  `arsinh, arcosh, artanh`. Two of the three (arcosh, artanh) deviate
  from the paper's exact S2 recipe to avoid routing through complex
  arguments — see decisions section below. Difficulty 4.

- **Group D — circular trig via complex EML (062-064, 3 chunks).**
  `cos, sin, tan`. Introduces `EMLTermℂ₁` (one-variable complex EML
  grammar, modelled on chunks 034/035). The `Real.cos x` identity is
  recovered via `Re(cosh(i·x))`. Difficulty 5.

- **Group E — inverse circular trig via complex EML (065-067, 3 chunks).**
  `arctan, arcsin, arccos`. arctan via the standard
  `(1/(2i)) ln((1+ix)/(1-ix))`; arcsin and arccos route around the
  paper's circular dependency (see below). Difficulty 5.

- **Group F — scope extensions (068-070, 3 chunks).**
  `068_wolfram_pow_complex` generalises chunk 024 to ℂ admitting full
  `pow`. `069_universal_minimality` strengthens chunk 029 with the
  general 2-primitive impossibility result. `070_main_completeness_full`
  is the 29-conjunct umbrella replacing chunk 045. Difficulty 5.

### Recipe adjustments (deviations from Table S2)

- **Chunk 060 (arcosh).** Paper writes `arcosh(x) = arsinh(hypot(x,
  √(-1)))`. The literal recipe uses an imaginary `hypot` argument; for
  the strictly-real Lean grammar (`EMLTerm₁`) we instead use the
  textbook form `arcosh x = ln(x + √(x²-1))` for `x ≥ 1`.

- **Chunk 061 (artanh).** Paper writes
  `artanh = arsinh(1/tan(arccos(x)))`. We use the textbook
  `artanh x = (1/2) ln((1+x)/(1-x))` to avoid the trig detour.

- **Chunk 066 (arcsin) and 067 (arccos).** Paper has arccos at S2 step
  29 and arcsin at step 31, with `arcsin = π/2 − arccos` and
  `arccos = arcosh(cos(arcosh(x)))`. The latter requires extending
  arcosh outside its real domain `[1, ∞)`. We invert the order in our
  Lean chain: arcsin is built first via `arctan(x/√(1−x²))`, then
  arccos as `π/2 − arcsin` (chunk 067). This keeps every sub-witness
  on its certified real domain and breaks the supplement's circular
  dependency, which is also flagged in §1.3 of the supplement under
  "flaky witnesses".

### Permanent-sorry inheritance

Several Round-2 chunks transitively depend on the Round-1 permanent
sorries (chunks 034 π, 035 i, 039 √x). Specifically:
- chunks 054, 059, 060 depend on chunk 039 (√x);
- chunks 062-067 depend on chunks 034 (π) and 035 (i).

These will not be sealed until the paper's Supplementary trees are
machine-transcribed. We track this as a known limitation rather than
a defect.

### Updated wave plan

- **Wave 5 (8 chunks, low-medium).** 050, 051, 052, 053, 055,
  056, 057, 058 — Group A (excluding hypot) and Group B. All depend
  only on already-sealed Round-1 chunks plus internal forward
  references; ordering ensures every chunk's deps are met when
  submitted.
- **Wave 6 (3 chunks, medium).** 059, 060, 061 — Group C. arcosh
  depends on arsinh (within wave); artanh is independent.
- **Wave 7 (5 chunks, medium-hard).** 054 (hypot — high risk because
  of √x), 062, 063, 064 — Group D + hypot. Inherits chunks 034/035/039
  permanent-sorry risk; we may submit the existential statement and
  accept failure.
- **Wave 8 (5 chunks, hard).** 065, 066, 067, 068, 069 — Groups E and
  F (sans the umbrella). 068 (Wolfram → Calc 3 ℂ) is genuinely new
  algebra; 069 is mostly induction on a tiny grammar.
- **Wave 9 (1 chunk, opt-in).** 070 — full umbrella. Submit only after
  the eight underlying Round-2 witnesses land.

Total: 21 new submissions across five waves; combined with the
original 45, the project now covers **66 chunks**.
