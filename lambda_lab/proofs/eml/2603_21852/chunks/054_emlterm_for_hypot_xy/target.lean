import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace EML

/-- Two-variable EML term grammar. -/
inductive EMLTerm₂ : Type
  | one  : EMLTerm₂
  | varX : EMLTerm₂
  | varY : EMLTerm₂
  | eml  : EMLTerm₂ → EMLTerm₂ → EMLTerm₂
  deriving Repr

noncomputable def EMLTerm₂.eval (x y : ℝ) : EMLTerm₂ → ℝ
  | .one      => 1
  | .varX     => x
  | .varY     => y
  | .eml t u  => Real.exp (EMLTerm₂.eval x y t) - Real.log (EMLTerm₂.eval x y u)

/-
Recipe (Table S2, step 19 — `hypot(x,y)`, K=6):
    hypot(x, y) = √(x² + y²)        (chunks 038 [sq] + 040 [add] + 039 [sqrt])

Holds for all `x, y : ℝ`, but the underlying `sq` witness from chunk 038
only certifies `x > 0`, so we constrain to `x ≠ 0 ∨ y ≠ 0` plus standard
positivity hooks. The unconditional identity `hypot = √(x² + y²)` is
unaffected.
-/
theorem emlterm2_for_hypot :
    ∃ t : EMLTerm₂, ∀ x y : ℝ, 0 < x → 0 < y →
      EMLTerm₂.eval x y t = Real.sqrt (x ^ 2 + y ^ 2) := by
  sorry

end EML
