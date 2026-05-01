import Mathlib

namespace EML

/-- Two-variable EML term grammar. -/
inductive EMLTerm₂ : Type
  | one : EMLTerm₂
  | varX : EMLTerm₂
  | varY : EMLTerm₂
  | eml : EMLTerm₂ → EMLTerm₂ → EMLTerm₂
  deriving Repr

/-- Evaluation of a two-variable EML term at (x, y). -/
noncomputable def EMLTerm₂.eval (x y : ℝ) : EMLTerm₂ → ℝ
  | .one => 1
  | .varX => x
  | .varY => y
  | .eml t u => Real.exp (EMLTerm₂.eval x y t) - Real.log (EMLTerm₂.eval x y u)

/-
exp(x) - x is always positive.
-/
lemma exp_sub_self_pos (x : ℝ) : 0 < Real.exp x - x := by
  linarith [ Real.add_one_le_exp x ]

theorem emlterm2_for_add :
    ∃ t : EMLTerm₂, ∀ x y : ℝ, EMLTerm₂.eval x y t = x + y := by
  refine ⟨.eml
    (.eml .one (.eml (.eml .one (.eml .varX .one)) .one))
    (.eml
      (.eml (.eml .one (.eml (.eml .one (.eml .varX (.eml .varX .one))) .one))
            (.eml .varY .one))
      .one), ?_⟩
  intro x y
  simp only [EMLTerm₂.eval, Real.log_one, sub_zero, Real.log_exp]
  have h1 : Real.exp 1 - (Real.exp 1 - x) = x := by ring
  have h2 : Real.exp 1 - (Real.exp 1 - Real.log (Real.exp x - x)) =
    Real.log (Real.exp x - x) := by ring
  rw [h1, h2, Real.exp_log (exp_sub_self_pos x)]
  ring

end EML
