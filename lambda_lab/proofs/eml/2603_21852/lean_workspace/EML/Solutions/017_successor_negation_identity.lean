import Mathlib

namespace EML

theorem successor_negation_identity (x : ℝ) (hx : x ≠ 0) (hx1 : x ≠ -1) :
    1 / (1 / (1 / x + 1) - 1) + 1 = -x := by
  grind

end EML