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

-- The key subterms
/-- log(x) for x > 0 -/
noncomputable def logTerm : EMLTerm₁ := .eml .one (.eml (.eml .one .var) .one)

/-- x - log(x) for x > 0 -/
noncomputable def xMinusLogTerm : EMLTerm₁ := .eml logTerm .var

/-- log(x - log(x)) for x > 0 -/
noncomputable def logXMinusLogTerm : EMLTerm₁ := .eml .one (.eml (.eml .one xMinusLogTerm) .one)

/-- -log(x) for x > 0 -/
noncomputable def negLogTerm : EMLTerm₁ := .eml logXMinusLogTerm (.eml .var .one)

/-- 1/x for x > 0 -/
noncomputable def invTerm : EMLTerm₁ := .eml negLogTerm .one

/-
Helper: x - log(x) > 0 for x > 0
-/
lemma sub_log_pos {x : ℝ} (hx : 0 < x) : 0 < x - Real.log x := by
  linarith [ Real.log_le_sub_one_of_pos hx ]

-- Step 1: logTerm evaluates to log(x)
lemma eval_logTerm {x : ℝ} (_hx : 0 < x) :
    EMLTerm₁.eval x logTerm = Real.log x := by
  simp only [logTerm, EMLTerm₁.eval, Real.log_one, sub_zero, Real.log_exp]
  ring

-- Step 2: xMinusLogTerm evaluates to x - log(x)
lemma eval_xMinusLogTerm {x : ℝ} (hx : 0 < x) :
    EMLTerm₁.eval x xMinusLogTerm = x - Real.log x := by
  simp only [xMinusLogTerm, EMLTerm₁.eval, eval_logTerm hx, Real.exp_log hx]

-- Step 3: logXMinusLogTerm evaluates to log(x - log(x))
lemma eval_logXMinusLogTerm {x : ℝ} (hx : 0 < x) :
    EMLTerm₁.eval x logXMinusLogTerm = Real.log (x - Real.log x) := by
  simp only [logXMinusLogTerm, EMLTerm₁.eval, eval_xMinusLogTerm hx, Real.log_one, sub_zero,
    Real.log_exp]
  ring

-- Step 4: negLogTerm evaluates to -log(x)
lemma eval_negLogTerm {x : ℝ} (hx : 0 < x) :
    EMLTerm₁.eval x negLogTerm = -Real.log x := by
  simp only [negLogTerm, EMLTerm₁.eval, eval_logXMinusLogTerm hx,
    Real.exp_log (sub_log_pos hx), Real.log_one, sub_zero, Real.log_exp]
  ring

-- Step 5: invTerm evaluates to 1/x
lemma eval_invTerm {x : ℝ} (hx : 0 < x) :
    EMLTerm₁.eval x invTerm = 1 / x := by
  simp only [invTerm, EMLTerm₁.eval, eval_negLogTerm hx, Real.log_one, sub_zero]
  rw [Real.exp_neg, Real.exp_log hx, one_div]

theorem emlterm1_for_inv_x_pos :
    ∃ t : EMLTerm₁, ∀ x : ℝ, 0 < x → EMLTerm₁.eval x t = 1 / x := by
  exact ⟨invTerm, fun x hx => eval_invTerm hx⟩

end EML
