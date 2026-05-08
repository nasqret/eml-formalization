import Mathlib

/-!
# `x / √(1 + x²) ∈ (-1, 1)` for all real x

Auxiliary lemma supporting the Path C′ `arctanViaArcsin` witness:
proving that the arctan-via-arcsin argument always lies in `arcsin`'s
natural domain `(-1, 1)`.

This is a pure Mathlib real-analysis fact. The proof uses
`|x| < √(1 + x²)` (since `x² < 1 + x²`) plus standard division/
sqrt manipulations.
-/

theorem atanArg_in_Ioo (x : ℝ) :
    x / Real.sqrt (1 + x^2) ∈ Set.Ioo (-1 : ℝ) 1 := by
  exact ⟨ by rw [ lt_div_iff₀ ( by positivity ) ] ; nlinarith [ Real.sqrt_nonneg ( 1 + x ^ 2 ), Real.sq_sqrt ( by positivity : 0 ≤ 1 + x ^ 2 ) ], by rw [ div_lt_iff₀ ( by positivity ) ] ; nlinarith [ Real.sqrt_nonneg ( 1 + x ^ 2 ), Real.sq_sqrt ( by positivity : 0 ≤ 1 + x ^ 2 ) ] ⟩