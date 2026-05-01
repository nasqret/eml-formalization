# EMLTerm₁ realising the function x² — 038_emlterm_for_sq_x

**Paper section**: §3 Results, EML expression catalog (x², K=75 / K=17 direct)
**Difficulty**: 5/5
**Status**: pending (resubmitted after reformulation; see notes)

## Source quote
> x²: K = 75 (compiler) / K = 17 (direct search).

## Informal (PL)
Istnieje term EMLTerm₁ ewaluujący do x² dla każdego dodatniego x.
Reformułowane dla dziedziny x > 0: dla x ≤ 0 Real.log zwraca wartość
śmieciową 0, więc konstrukcja exp(2·log x) nie zachodzi. Bound K=17
(direct search) z paper'a odpowiada ~9 węzłom drzewa.

## Informal (EN)
There exists an `EMLTerm₁` whose evaluation equals `x²` for every
positive real `x`. Reformulated for the positive domain: for `x ≤ 0`,
`Real.log` returns its junk value `0`, so the natural construction
`exp(2·log x)` breaks. The paper's `K=17` (direct-search) bound matches
roughly nine tree nodes — well inside Aristotle's reach.

## Formal target

```lean
theorem emlterm1_for_sq_x_pos :
    ∃ t : EMLTerm₁, ∀ x : ℝ, 0 < x → EMLTerm₁.eval x t = x ^ 2 := by sorry
```

## Dependencies
023_emlterm_exp_x_witness

## History
1. **Original spec**: `∀ x : ℝ, eval x t = x²` — too strong; cannot hold uniformly because a single term can't switch on the sign of `x`.
2. **First Aristotle attempt** (project `ab66ad12-…`): returned `FAILED` — Harmonic infrastructure error: *"Project failed due to an internal error. The team at Harmonic has been notified; please try again."* Not a mathematical limitation.
3. **Reformulated** to `∀ x > 0`. Resubmitting.

## Aristotle status
pending (project_id: null after reformulation)
