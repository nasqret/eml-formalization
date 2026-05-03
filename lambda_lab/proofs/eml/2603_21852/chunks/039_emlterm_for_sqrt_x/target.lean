import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace EML

inductive EMLTerm₁ : Type
  | one : EMLTerm₁
  | var : EMLTerm₁
  | eml : EMLTerm₁ → EMLTerm₁ → EMLTerm₁
  deriving Repr

noncomputable def EMLTerm₁.eval (x : ℝ) : EMLTerm₁ → ℝ
  | .one => 1
  | .var => x
  | .eml t u => Real.exp (EMLTerm₁.eval x t) - Real.log (EMLTerm₁.eval x u)

/-
Resealed for the FULL positive domain (`0 < x`, replacing the previous `1 < x`).

Construction (the `pow_term` substitution trick from chunk 054 hypot):

  1. Lift in chunk 042's `pow_term : EMLTerm₂` (two variables x, y), which
     evaluates to `x^y` for `0 < x ∧ 0 < y`.
  2. Build a closed `half_term : EMLTerm₁` that evaluates to `1/2` (chunk 033).
  3. Define `proj : EMLTerm₂ → EMLTerm₁ → EMLTerm₁ → EMLTerm₁` substituting
     `varX ↦ A`, `varY ↦ B`, with the corresponding eval lemma.
  4. Set `sqrt_term := proj pow_term .var half_term`.

Then `eval x sqrt_term = pow_term @ (x, 1/2) = exp((1/2) log x) = x^(1/2) = √x`
for any `0 < x`, since both `pow_term` arguments stay strictly positive.

This sidesteps the iterated-log construction (which required `log(log x)` to
be well-defined, hence `x > 1`). The key Mathlib bridges are
`Real.sqrt_eq_rpow` and `Real.rpow_def_of_pos`.
-/
theorem emlterm1_for_sqrt_x_pos :
    ∃ t : EMLTerm₁, ∀ x : ℝ, 0 < x → EMLTerm₁.eval x t = Real.sqrt x := by
  sorry

end EML
