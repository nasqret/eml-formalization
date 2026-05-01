import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace EML

def eml (x y : ℝ) : ℝ := Real.exp x - Real.log y

theorem eml_one_y (y : ℝ) (hy : 0 < y) : eml 1 y = Real.exp 1 - Real.log y := by
  sorry

end EML
