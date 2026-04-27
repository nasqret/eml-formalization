import Mathlib.Tactic

example (n : Nat) : 0 * n = 0 := by
  rw [Nat.zero_mul]
