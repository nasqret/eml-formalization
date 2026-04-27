import Mathlib.Tactic

example (a b : Nat) (h : a = b) : b + 1 = a + 1 := by
  rw [h]
