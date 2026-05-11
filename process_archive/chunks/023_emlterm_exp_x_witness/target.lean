import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace EML

/-- EML term grammar with a single distinguished variable `x`. -/
inductive EMLTerm₁ : Type
  | one : EMLTerm₁
  | var : EMLTerm₁
  | eml : EMLTerm₁ → EMLTerm₁ → EMLTerm₁
  deriving Repr

/-- Evaluation of a parameterised EML term at value `x`. -/
def EMLTerm₁.eval (x : ℝ) : EMLTerm₁ → ℝ
  | .one => 1
  | .var => x
  | .eml t u => Real.exp (EMLTerm₁.eval x t) - Real.log (EMLTerm₁.eval x u)

theorem emlterm1_exp_x_witness (x : ℝ) :
    EMLTerm₁.eval x (.eml .var .one) = Real.exp x := by
  sorry

end EML
