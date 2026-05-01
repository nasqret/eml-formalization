import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace EML

inductive EMLTerm : Type
  | one : EMLTerm
  | eml : EMLTerm → EMLTerm → EMLTerm
  deriving Repr

noncomputable def EMLTerm.eval : EMLTerm → ℝ
  | .one => 1
  | .eml t u => Real.exp (EMLTerm.eval t) - Real.log (EMLTerm.eval u)

-- The witness term, built bottom-up for clarity
private def t₂ : EMLTerm := .eml .one .one                                -- eval = e
private def t₃ : EMLTerm := .eml .one t₂                                  -- eval = e - 1
private def t₄ : EMLTerm := .eml .one t₃                                  -- eval = e - log(e-1)
private def t₅ : EMLTerm := .eml t₄ .one                                  -- eval = exp(e - log(e-1))
private def t₆ : EMLTerm := .eml .one t₅                                  -- eval = log(e-1)
private def t₇ : EMLTerm := .eml t₆ t₂                                    -- eval = e - 2
private def t₈ : EMLTerm := .eml t₇ .one                                  -- eval = exp(e-2)
private def witness : EMLTerm := .eml .one t₈                              -- eval = 2

private lemma eval_t₂' : EMLTerm.eval t₂ = Real.exp 1 := by
  simp [t₂, EMLTerm.eval, Real.log_one]

private lemma eval_t₃ : EMLTerm.eval t₃ = Real.exp 1 - 1 := by
  simp [t₃, EMLTerm.eval, eval_t₂', Real.log_exp]

private lemma eval_t₄ : EMLTerm.eval t₄ = Real.exp 1 - Real.log (Real.exp 1 - 1) := by
  simp [t₄, EMLTerm.eval, eval_t₃]

private lemma eval_t₅ : EMLTerm.eval t₅ = Real.exp (Real.exp 1 - Real.log (Real.exp 1 - 1)) := by
  simp [t₅, EMLTerm.eval, eval_t₄, Real.log_one]

private lemma eval_t₆ : EMLTerm.eval t₆ = Real.log (Real.exp 1 - 1) := by
  simp [t₆, EMLTerm.eval, eval_t₅, Real.log_exp]

private lemma e_minus_one_pos : (0 : ℝ) < Real.exp 1 - 1 := by
  have h0 : Real.exp 0 = 1 := Real.exp_zero
  have h1 : Real.exp 0 < Real.exp 1 := Real.exp_strictMono (by norm_num)
  linarith

private lemma eval_t₇ : EMLTerm.eval t₇ = Real.exp 1 - 2 := by
  simp only [t₇, EMLTerm.eval, eval_t₆, eval_t₂']
  rw [Real.exp_log e_minus_one_pos]
  linarith [Real.log_exp 1]

private lemma eval_t₈ : EMLTerm.eval t₈ = Real.exp (Real.exp 1 - 2) := by
  simp [t₈, EMLTerm.eval, eval_t₇, Real.log_one]

private lemma eval_witness : EMLTerm.eval witness = 2 := by
  simp only [witness, EMLTerm.eval, eval_t₈]
  rw [Real.log_exp]
  ring

theorem emlterm_for_two : ∃ t : EMLTerm, EMLTerm.eval t = 2 :=
  ⟨witness, eval_witness⟩

end EML
