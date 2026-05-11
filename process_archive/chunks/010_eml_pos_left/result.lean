import Mathlib.Analysis.SpecialFunctions.Exp

namespace EML

theorem eml_left_pos (x y : ℝ) : 0 < Real.exp x := by
  positivity

end EML