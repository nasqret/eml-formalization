# Period-π reduction for tan — 079_tan_period_reduction

**Paper section**: Path C′ Plan (post-paper, GPT Pro recommendation)
**Difficulty**: 3/5
**Status**: pending

## Source

GPT Pro consult `gpt_pro_bundle/trig_widening/RESPONSE.md` §4. Range-
reduction step for the `tan_full` witness: every `x : ℝ` with `cos x ≠ 0`
admits an integer `k` such that `x − kπ` falls in the fundamental
strip `(−π/2, π/2)` and `tan x = tan(x − kπ)`.

## Informal (EN)

For `cos x ≠ 0`, take `k = ⌊x/π + 1/2⌋ : ℤ` (the nearest integer
multiple of π). Then `x − kπ ∈ [−π/2, π/2]`. The endpoints `±π/2` are
excluded by the `cos x ≠ 0` hypothesis (since `cos(±π/2 + kπ) = 0`).
Periodicity: `Real.tan_periodic` gives `tan(x − kπ) = tan x`.

## Formal target

```lean
theorem tan_period_reduction (x : ℝ) (hx : Real.cos x ≠ 0) :
    ∃ k : ℤ, x - (k : ℝ) * Real.pi ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) ∧
             Real.tan x = Real.tan (x - (k : ℝ) * Real.pi)
```

## Dependencies

None (Mathlib only). Likely uses:
- `Int.floor_add_one_div_two`, `Int.floor_le`, `Int.lt_floor_add_one`
- `Real.tan_periodic` or `Real.tan_int_mul_pi`
- `Real.cos_eq_zero_iff` for the endpoint exclusion

## Aristotle status

pending (project_id: null)
