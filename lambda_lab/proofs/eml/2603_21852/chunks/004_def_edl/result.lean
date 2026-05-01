import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace EML

/-- The EDL (Exp Divided by Log) variant of EML.
Identity 4b in Odrzywołek (arXiv:2603.21852). Constant: `e`. -/
def edl (x y : ℝ) : ℝ := Real.exp x / Real.log y

end EML
