import Mathlib

namespace EML

inductive EMLTerm₁ : Type
  | one : EMLTerm₁
  | var : EMLTerm₁
  | eml : EMLTerm₁ → EMLTerm₁ → EMLTerm₁
  deriving Repr

noncomputable def EMLTerm₁.eval (x : ℝ) : EMLTerm₁ → ℝ
  | .one => 1
  | .var => x
  | .eml t u => Real.exp (EMLTerm₁.eval x t) - Real.log (EMLTerm₁.eval x u)

/-
Key helper: exp(x) - x > 0 for all real x
-/
lemma exp_sub_x_pos (x : ℝ) : Real.exp x - x > 0 := by
  linarith [ Real.add_one_le_exp x ]

/-
Key helper: log(exp(e) / a) = e - log(a) when a > 0
-/
lemma log_exp_div (e : ℝ) (a : ℝ) (ha : a > 0) :
    Real.log (Real.exp e / a) = e - Real.log a := by
      rw [ Real.log_div ( by positivity ) ( by positivity ), Real.log_exp ]

-- The witness term and its evaluation
-- w     := eml var (eml var one)           -- exp(x) - log(exp(x) - log(1)) = exp(x) - x
-- expx  := eml var one                     -- exp(x) - log(1) = exp(x)
-- eml one w := exp(1) - log(exp(x) - x)
-- eml (eml one w) one := exp(exp(1) - log(exp(x) - x)) - log(1)
--                       = exp(exp(1) - log(exp(x) - x))
--                       = exp(exp(1)) / (exp(x) - x)
-- logw  := eml one (eml (eml one w) one)   -- exp(1) - log(exp(exp(1))/(exp(x)-x))
--                                          = exp(1) - (exp(1) - log(exp(x)-x))
--                                          = log(exp(x) - x)
-- eml expx one := exp(exp(x)) - log(1) = exp(exp(x))
-- neg_x := eml logw (eml expx one)        -- exp(log(exp(x)-x)) - log(exp(exp(x)))
--                                          = (exp(x) - x) - exp(x) = -x

private def w : EMLTerm₁ := .eml .var (.eml .var .one)
private def expx : EMLTerm₁ := .eml .var .one
private def logw : EMLTerm₁ := .eml .one (.eml (.eml .one w) .one)
private def neg_x_term : EMLTerm₁ := .eml logw (.eml expx .one)

lemma eval_w (x : ℝ) : EMLTerm₁.eval x w = Real.exp x - x := by
  simp [w, EMLTerm₁.eval, Real.log_one, Real.log_exp]

lemma eval_expx (x : ℝ) : EMLTerm₁.eval x expx = Real.exp x := by
  simp [expx, EMLTerm₁.eval, Real.log_one]

lemma eval_eml_one_w (x : ℝ) :
    EMLTerm₁.eval x (.eml .one w) = Real.exp 1 - Real.log (Real.exp x - x) := by
  simp [EMLTerm₁.eval, eval_w]

lemma eval_eml_eml_one_w_one (x : ℝ) :
    EMLTerm₁.eval x (.eml (.eml .one w) .one) =
    Real.exp (Real.exp 1 - Real.log (Real.exp x - x)) := by
  simp [EMLTerm₁.eval, eval_w, Real.log_one]

lemma eval_logw (x : ℝ) : EMLTerm₁.eval x logw = Real.log (Real.exp x - x) := by
  unfold logw; simp +decide [ EMLTerm₁.eval ] ;
  rw [ eval_w ]

lemma eval_eml_expx_one (x : ℝ) :
    EMLTerm₁.eval x (.eml expx .one) = Real.exp (Real.exp x) := by
  simp [expx, EMLTerm₁.eval, Real.log_one]

lemma eval_neg_x (x : ℝ) : EMLTerm₁.eval x neg_x_term = -x := by
  -- By definition of $neg_x_term$, we have $neg_x_term = .eml logw (.eml expx .one)$.
  have h_neg_x_term : EMLTerm₁.eval x neg_x_term = Real.exp (EMLTerm₁.eval x logw) - Real.log (EMLTerm₁.eval x (.eml expx .one)) := by
    rfl;
  rw [ h_neg_x_term, eval_logw, eval_eml_expx_one, Real.exp_log ( by linarith [ exp_sub_x_pos x ] ), Real.log_exp ] ; ring

theorem emlterm1_for_neg_x :
    ∃ t : EMLTerm₁, ∀ x : ℝ, EMLTerm₁.eval x t = -x := by
  exact ⟨neg_x_term, eval_neg_x⟩

end EML
