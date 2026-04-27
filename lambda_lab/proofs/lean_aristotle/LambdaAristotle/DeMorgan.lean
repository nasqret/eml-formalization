-- Celowany import: ok. 1.9 s zamiast 13.8 s dla pełnego `Mathlib.Tactic`.
import Mathlib.Tactic.Tauto

namespace LambdaAristotle

/-- Klasyczne prawo De Morgana — pierwszy dowód zamówiony u Aristotle'a. -/
theorem demorgan_and (a b : Prop) : ¬ (a ∧ b) ↔ ¬ a ∨ ¬ b := by
  tauto

end LambdaAristotle
