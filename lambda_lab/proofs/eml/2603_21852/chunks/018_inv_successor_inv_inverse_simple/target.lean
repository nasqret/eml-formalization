import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace EML

theorem inv_successor_inv (x : ℝ) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    1 / (1 / x + 1) = x / (1 + x) := by
  sorry

end EML
