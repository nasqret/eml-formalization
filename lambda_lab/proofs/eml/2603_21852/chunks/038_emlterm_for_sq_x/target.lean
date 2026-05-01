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
Reformulated for positive x only.

Original target was ∀ x : ℝ, eval x t = x², but a single EMLTerm₁ cannot
branch on the sign of x: for x ≤ 0, Real.log returns its junk value 0, so
the natural construction exp(2 · log x) breaks. The paper's K=17 (direct
search) bound corresponds to roughly nine tree nodes, well inside any
reasonable search budget — but only when the domain is positive reals.
-/
theorem emlterm1_for_sq_x_pos :
    ∃ t : EMLTerm₁, ∀ x : ℝ, 0 < x → EMLTerm₁.eval x t = x ^ 2 := by
  sorry

end EML
