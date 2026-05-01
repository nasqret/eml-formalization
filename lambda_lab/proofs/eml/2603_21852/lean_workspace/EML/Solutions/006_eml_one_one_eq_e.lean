import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace EML

noncomputable def eml (x y : ℝ) : ℝ := Real.exp x - Real.log y

theorem eml_one_one : eml 1 1 = Real.exp 1 := by
  -- By definition of eml, we have eml 1 1 = Real.exp 1 - Real.log 1.
  simp [eml]

end EML