import Mathlib.Tactic

example (a b : Nat) : a + b = b + a := by
  rw [Nat.add_comm]
