import Mathlib

/-!
# Period-π reduction for tan

Auxiliary lemma supporting the Path C′ `tan_full` witness: for every
real `x` with `cos x ≠ 0`, there exists an integer `k` such that
`x − kπ` lies in `(−π/2, π/2)` and `tan x = tan (x − kπ)`. This is the
range-reduction step that lets the existing `tanCoreTermℂ` /
`tanCoreTermℂ_neg` (which work on `(-π/2, π/2) ∖ {0}`) cover all of
the natural `tan` domain.

Mathlib facts used:
- `Real.tan_periodic : Function.Periodic Real.tan Real.pi`
- `Int.fract`, `Int.floor` for the integer-part extraction
-/

theorem tan_period_reduction (x : ℝ) (hx : Real.cos x ≠ 0) :
    ∃ k : ℤ, x - (k : ℝ) * Real.pi ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) ∧
             Real.tan x = Real.tan (x - (k : ℝ) * Real.pi) := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, x - k * Real.pi ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2) := by
    use ⌊(x + Real.pi / 2) / Real.pi⌋;
    constructor;
    · contrapose! hx;
      rw [ Real.cos_eq_zero_iff ];
      exact ⟨ ⌊ ( x + Real.pi / 2 ) / Real.pi⌋ - 1, by push_cast; nlinarith [ Int.floor_le ( ( x + Real.pi / 2 ) / Real.pi ), Int.lt_floor_add_one ( ( x + Real.pi / 2 ) / Real.pi ), Real.pi_pos, mul_div_cancel₀ ( x + Real.pi / 2 ) Real.pi_ne_zero ] ⟩;
    · nlinarith [ Int.lt_floor_add_one ( ( x + Real.pi / 2 ) / Real.pi ), Real.pi_pos, mul_div_cancel₀ ( x + Real.pi / 2 ) Real.pi_ne_zero ];
  exact ⟨ k, ⟨ by linarith [ hk.1 ], by linarith [ hk.2 ] ⟩, by simp +decide [ Real.tan_sub_int_mul_pi ] ⟩