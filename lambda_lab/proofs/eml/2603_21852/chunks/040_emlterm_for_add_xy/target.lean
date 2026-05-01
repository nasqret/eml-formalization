import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace EML

/-- Two-variable EML term grammar. -/
inductive EMLTerm₂ : Type
  | one : EMLTerm₂
  | varX : EMLTerm₂
  | varY : EMLTerm₂
  | eml : EMLTerm₂ → EMLTerm₂ → EMLTerm₂
  deriving Repr

/-- Evaluation of a two-variable EML term at (x, y). -/
def EMLTerm₂.eval (x y : ℝ) : EMLTerm₂ → ℝ
  | .one => 1
  | .varX => x
  | .varY => y
  | .eml t u => Real.exp (EMLTerm₂.eval x y t) - Real.log (EMLTerm₂.eval x y u)

theorem emlterm2_for_add :
    ∃ t : EMLTerm₂, ∀ x y : ℝ, EMLTerm₂.eval x y t = x + y := by
  sorry

end EML
