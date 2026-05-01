import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace EML

def eml (x y : ℝ) : ℝ := Real.exp x - Real.log y

theorem eml_x_e (x : ℝ) : eml x (Real.exp 1) = Real.exp x - 1 := by
  sorry

end EML
