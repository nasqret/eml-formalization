import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace EML

inductive EMLTerm : Type
  | one : EMLTerm
  | eml : EMLTerm → EMLTerm → EMLTerm
  deriving Repr

noncomputable def EMLTerm.eval : EMLTerm → ℝ
  | .one => 1
  | .eml t u => Real.exp (EMLTerm.eval t) - Real.log (EMLTerm.eval u)

theorem emlterm_for_zero : ∃ t : EMLTerm, EMLTerm.eval t = 0 := by
  -- Witness: eml one (eml (eml one one) one)
  -- eval = exp(1) - log(exp(exp(1) - log(1)))
  --      = exp(1) - log(exp(exp(1) - 0))
  --      = exp(1) - log(exp(exp(1)))
  --      = exp(1) - exp(1) = 0
  exact ⟨.eml .one (.eml (.eml .one .one) .one), by
    simp [EMLTerm.eval, Real.log_one, sub_zero, Real.log_exp, sub_self]⟩

end EML
