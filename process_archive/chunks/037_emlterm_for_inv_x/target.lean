import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

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
Reformulated for the positive domain only (x > 0).

The original target was `∀ x, x ≠ 0 → eval x t = 1/x`. A single
`EMLTerm₁` cannot branch on the sign of x — `Real.log` returns its
junk value 0 for non-positive inputs, so any construction that uses
`log x` only behaves correctly for positive x. The paper's K = 65
direct-search bound corresponds to roughly 33 nodes and is well
within Aristotle's reach when restricted to x > 0.

Hint for the synthesiser: 1/x = exp(-log x) = exp(0 - log x). Build
`-log x` via the same trick used in `038_emlterm_for_sq_x`:
  * x - (x - log x) = log x  is already EML-computable
  * negate by composing with `0 - log x` using the zero term
-/
theorem emlterm1_for_inv_x_pos :
    ∃ t : EMLTerm₁, ∀ x : ℝ, 0 < x → EMLTerm₁.eval x t = 1 / x := by
  sorry

end EML
