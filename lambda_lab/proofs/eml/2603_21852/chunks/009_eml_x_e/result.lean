import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace EML

noncomputable def eml (x y : ℝ) : ℝ := Real.exp x - Real.log y

theorem eml_x_e (x : ℝ) : eml x (Real.exp 1) = Real.exp x - 1 := by
  -- By definition of eml, we have eml x (Real.exp 1) = Real.exp x - Real.log (Real.exp 1).
  simp [eml]

end EML