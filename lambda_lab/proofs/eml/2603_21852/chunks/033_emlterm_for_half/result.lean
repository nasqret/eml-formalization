import Mathlib

namespace EML

inductive EMLTerm : Type
  | one : EMLTerm
  | eml : EMLTerm → EMLTerm → EMLTerm
  deriving Repr

noncomputable def EMLTerm.eval : EMLTerm → ℝ
  | .one => 1
  | .eml t u => Real.exp (EMLTerm.eval t) - Real.log (EMLTerm.eval u)

open EMLTerm

/-- Zero term: evaluates to 0 -/
private def Z : EMLTerm := eml one (eml (eml one one) one)

/-- Log construction: if eval t > 0 then eval (Lg t) = log (eval t) -/
private def Lg (t : EMLTerm) : EMLTerm := eml Z (eml (eml Z t) one)

-- Building blocks
private def e1 : EMLTerm := eml one (eml one one)
private def log_e1 : EMLTerm := Lg e1
private def e2 : EMLTerm := eml log_e1 (eml one one)
private def exp_e2 : EMLTerm := eml e2 one
private def two_ : EMLTerm := eml one exp_e2
private def eml2 : EMLTerm := eml one two_
private def log_eml2 : EMLTerm := Lg eml2
private def neg_log2 : EMLTerm := eml log_eml2 (eml (eml one one) one)
private def half_term : EMLTerm := eml neg_log2 one

-- Evaluation lemmas
private lemma eval_Z : Z.eval = 0 := by
  simp [Z, EMLTerm.eval, Real.log_one, Real.log_exp]

private lemma eval_Lg {t : EMLTerm} (_ : 0 < t.eval) :
    (Lg t).eval = Real.log t.eval := by
  simp only [Lg, EMLTerm.eval, eval_Z, Real.exp_zero, Real.log_exp, Real.log_one, sub_zero]
  ring

private lemma eval_e1 : e1.eval = Real.exp 1 - 1 := by
  simp [e1, EMLTerm.eval, Real.log_one, Real.log_exp]

private lemma exp_one_sub_one_pos : (0 : ℝ) < Real.exp 1 - 1 := by
  linarith [Real.add_one_le_exp (1:ℝ)]

private lemma eval_log_e1 : log_e1.eval = Real.log (Real.exp 1 - 1) := by
  simp only [log_e1]
  rw [eval_Lg (by rw [eval_e1]; exact exp_one_sub_one_pos), eval_e1]

private lemma eval_e2 : e2.eval = Real.exp 1 - 2 := by
  simp only [e2, EMLTerm.eval, eval_log_e1, Real.exp_log exp_one_sub_one_pos,
    Real.log_one, sub_zero, Real.log_exp]
  ring

private lemma eval_exp_e2 : exp_e2.eval = Real.exp (Real.exp 1 - 2) := by
  simp only [exp_e2, EMLTerm.eval, eval_e2, Real.log_one, sub_zero]

private lemma eval_two : two_.eval = 2 := by
  simp only [two_, EMLTerm.eval, eval_exp_e2, Real.log_exp]; ring

private lemma eval_eml2 : eml2.eval = Real.exp 1 - Real.log 2 := by
  simp only [eml2, EMLTerm.eval, eval_two]

private lemma log_two_le_one : Real.log 2 ≤ 1 := by
  rw [show (1:ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
  exact Real.log_le_log (by norm_num) (by linarith [Real.add_one_le_exp (1:ℝ)])

private lemma exp_one_sub_log_two_pos : (0 : ℝ) < Real.exp 1 - Real.log 2 := by
  linarith [exp_one_sub_one_pos, log_two_le_one]

private lemma eval_log_eml2 : log_eml2.eval = Real.log (Real.exp 1 - Real.log 2) := by
  simp only [log_eml2]
  rw [eval_Lg (by rw [eval_eml2]; exact exp_one_sub_log_two_pos), eval_eml2]

private lemma eval_neg_log2 : neg_log2.eval = -Real.log 2 := by
  simp only [neg_log2, EMLTerm.eval, eval_log_eml2, Real.log_exp,
    Real.exp_log exp_one_sub_log_two_pos, Real.log_one, sub_zero]
  ring

private lemma eval_half : half_term.eval = 1 / 2 := by
  simp only [half_term, EMLTerm.eval, eval_neg_log2, Real.log_one, sub_zero,
    Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
  norm_num

theorem emlterm_for_half : ∃ t : EMLTerm, EMLTerm.eval t = 1/2 :=
  ⟨half_term, eval_half⟩

end EML
