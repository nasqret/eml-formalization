import Mathlib.Tactic

example (a b c : Nat) : (a + b) + c = a + (b + c) := by
  rw [Nat.add_assoc]
