import Mathlib.Algebra.GroupPower.Basic

namespace EML

/-- Total parameter count of the level-n EML master formula:
`5 · 2^n − 6` (Section 4.3). -/
def masterParamCount (n : ℕ) : ℤ := 5 * 2 ^ n - 6

example : masterParamCount 1 = 4 := by sorry
example : masterParamCount 2 = 14 := by sorry
example : masterParamCount 3 = 34 := by sorry

end EML
