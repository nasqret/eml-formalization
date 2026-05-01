import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace EML

noncomputable def eml (x y : ℝ) : ℝ := Real.exp x - Real.log y

theorem ln_via_eml (z : ℝ) (hz : 0 < z) :
    Real.log z = eml 1 (eml (eml 1 z) 1) := by
  unfold eml at *;
  norm_num +zetaDelta at *

end EML
