import Mathlib.Tactic

example (n : Nat) : 1 * n = n := by
  rw [Nat.one_mul]
