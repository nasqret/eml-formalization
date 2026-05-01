import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace EML

noncomputable def eml (x y : ℝ) : ℝ := Real.exp x - Real.log y

theorem exp_via_eml (x : ℝ) : Real.exp x = eml x 1 := by
  simp [eml, Real.log_one]

end EML
