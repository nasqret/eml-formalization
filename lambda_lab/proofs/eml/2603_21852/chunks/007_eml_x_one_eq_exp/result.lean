import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace EML

noncomputable def eml (x y : ℝ) : ℝ := Real.exp x - Real.log y

theorem eml_x_one (x : ℝ) : eml x 1 = Real.exp x := by
  unfold eml; norm_num;

end EML