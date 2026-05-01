import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace EML

theorem mul_via_exp_log (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x * y = Real.exp (Real.log x + Real.log y) := by
  sorry

end EML
