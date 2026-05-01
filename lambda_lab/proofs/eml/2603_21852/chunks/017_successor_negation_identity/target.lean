import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace EML

theorem successor_negation_identity (x : ℝ) (hx : x ≠ 0) (hx1 : x ≠ -1) :
    1 / (1 / (1 / x + 1) - 1) + 1 = -x := by
  sorry

end EML
