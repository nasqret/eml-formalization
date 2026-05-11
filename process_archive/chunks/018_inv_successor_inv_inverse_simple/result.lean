import Mathlib

namespace EML

theorem inv_successor_inv (x : ℝ) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    1 / (1 / x + 1) = x / (1 + x) := by
  have h1x : 1 + x ≠ 0 := by rw [add_comm]; exact hx1
  field_simp

end EML
