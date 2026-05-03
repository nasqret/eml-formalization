import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

namespace EML

inductive EMLTerm₁ : Type
  | one : EMLTerm₁
  | var : EMLTerm₁
  | eml : EMLTerm₁ → EMLTerm₁ → EMLTerm₁
  deriving Repr

noncomputable def EMLTerm₁.eval (x : ℝ) : EMLTerm₁ → ℝ
  | .one      => 1
  | .var      => x
  | .eml t u  => Real.exp (EMLTerm₁.eval x t) - Real.log (EMLTerm₁.eval x u)

/-
Recipe (Table S2, step 27 — `arsinh(x)`, K=6):
    arsinh(x) = ln(x + hypot(x, 1)) = ln(x + √(x² + 1))     (chunks 040, 054, 011)

Holds for every `x : ℝ` since `x + √(x² + 1) > 0` always. The chunk-054
hypot witness assumes positive arguments; we therefore restrict to `x > 0`
in the formal statement and leave the unconditional version to a later
extension. Mathlib's `Real.arsinh` matches.
-/
theorem emlterm1_for_arsinh :
    ∃ t : EMLTerm₁, ∀ x : ℝ, 0 < x → EMLTerm₁.eval x t = Real.arsinh x := by
  sorry

end EML
