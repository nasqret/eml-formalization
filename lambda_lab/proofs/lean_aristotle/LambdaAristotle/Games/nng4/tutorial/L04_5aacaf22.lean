import Mathlib.Tactic

example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1,h2]
