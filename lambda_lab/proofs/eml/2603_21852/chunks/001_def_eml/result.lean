import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace EML

/-- The EML (Exp-Minus-Log) binary operator on the reals.
Equation 3 in Odrzywołek (arXiv:2603.21852). -/
def eml (x y : ℝ) : ℝ := Real.exp x - Real.log y

end EML
