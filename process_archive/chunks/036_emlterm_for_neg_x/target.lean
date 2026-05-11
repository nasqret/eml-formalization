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
HINT (resolves an earlier 'unprovable' partial):

The witness is built around the identity
    exp(log(exp(x) - x)) - exp(x) = (exp(x) - x) - exp(x) = -x
which holds for every real x because exp(x) - x > 0 always (this is
just `Real.add_one_le_exp x` / `linarith`).

Construction:
    w     := eml var (eml var one)        -- evaluates to exp(x) - x
    logw  := eml one (eml (eml one w) one)  -- evaluates to log(exp(x) - x)
    expx  := eml var one                  -- evaluates to exp(x)
    neg_x := eml logw (eml expx one)      -- evaluates to -x

The full identity
    EMLTerm₁.eval x neg_x = -x
holds for ALL x : ℝ — no positivity hypothesis needed.
-/
theorem emlterm1_for_neg_x :
    ∃ t : EMLTerm₁, ∀ x : ℝ, EMLTerm₁.eval x t = -x := by
  sorry

end EML
