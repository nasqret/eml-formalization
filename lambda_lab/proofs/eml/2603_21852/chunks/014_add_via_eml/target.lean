import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace EML

theorem add_via_exp_log (x y : ℝ) :
    x + y = Real.log (Real.exp x * Real.exp y) := by
  sorry

end EML
