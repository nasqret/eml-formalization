import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace EML

theorem add_eq_log_mul_exp (x y : ℝ) :
    x + y = Real.log (Real.exp x) + Real.log (Real.exp y) := by
  sorry

end EML
