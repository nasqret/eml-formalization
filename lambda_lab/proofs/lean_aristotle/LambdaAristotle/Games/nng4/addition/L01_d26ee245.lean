import Mathlib.Tactic

example (n : Nat) : 0 + n = n := by
  rw [Nat.zero_add]
