import Mathlib.Tactic

example (a b : Nat) : (a + b) + (a + b) = 2 * a + 2 * b := by
  ring
