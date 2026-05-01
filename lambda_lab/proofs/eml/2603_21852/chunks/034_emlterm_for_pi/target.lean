import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace EML

inductive EMLTerm : Type
  | one : EMLTerm
  | eml : EMLTerm → EMLTerm → EMLTerm
  deriving Repr

def EMLTerm.eval : EMLTerm → ℝ
  | .one => 1
  | .eml t u => Real.exp (EMLTerm.eval t) - Real.log (EMLTerm.eval u)

/-- Existential statement that π is reachable as an EML term.
LIKELY PERMANENT SORRY: a 193-node literal tree is in the paper's Supplementary
and is beyond the budget of this pass to transcribe. -/
theorem emlterm_for_pi : ∃ t : EMLTerm, EMLTerm.eval t = Real.pi := by
  sorry

end EML
