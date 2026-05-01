import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace EML

/-- The negated-EML variant: `-eml(y, x) = ln(x) - exp(y)`.
Identity 4c in Odrzywołek (arXiv:2603.21852). -/
def negEml (x y : ℝ) : ℝ := Real.log x - Real.exp y

end EML
