import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace EML

theorem neg_via_calc3 (x : ℝ) (hx : x ≠ 0) (hx1 : x ≠ -1) :
    -x = 1 / (1 / (1 / x + 1) - 1) + 1 := by
  sorry

end EML
