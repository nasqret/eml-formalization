import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace EML

def eml (x y : ℝ) : ℝ := Real.exp x - Real.log y

theorem sub_via_eml (x y : ℝ) (hx : 0 < x) :
    x - y = eml (Real.log x) (Real.exp y) := by
  sorry

end EML
