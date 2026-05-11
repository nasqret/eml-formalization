import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace EML

/-- One-variable EML term grammar (lifted from chunk 023). -/
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
Recipe (Table S2, step 13 — `x/2`, K=2):
    half(x)  =  x · (1/2)

Constructively the witness is `mul(varX, halfTerm)` where `halfTerm` is
chunk 033's constant-`1/2` EMLTerm. Positivity of `x` is required by the
underlying chunk-041 multiplication; the unconditional identity matches
the paper's Table S2 entry.
-/
theorem emlterm1_for_half :
    ∃ t : EMLTerm₁, ∀ x : ℝ, 0 < x → EMLTerm₁.eval x t = x / 2 := by
  sorry

end EML
