import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace EML

noncomputable def eml (x y : ℝ) : ℝ := Real.exp x - Real.log y

theorem sub_via_eml (x y : ℝ) (hx : 0 < x) :
    x - y = eml (Real.log x) (Real.exp y) := by
  unfold eml; rw [ Real.exp_log hx, Real.log_exp ] ;

end EML
