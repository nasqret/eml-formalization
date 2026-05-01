import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace EML

def eml (x y : ℝ) : ℝ := Real.exp x - Real.log y

theorem exp_via_eml (x : ℝ) : Real.exp x = eml x 1 := by
  sorry

end EML
