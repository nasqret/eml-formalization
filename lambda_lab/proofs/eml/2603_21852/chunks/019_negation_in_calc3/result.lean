import Mathlib

namespace EML

theorem neg_via_calc3 (x : ℝ) (hx : x ≠ 0) (hx1 : x ≠ -1) :
    -x = 1 / (1 / (1 / x + 1) - 1) + 1 := by
  grind

end EML
