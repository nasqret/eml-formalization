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

-- Building blocks
private def zeroTerm : EMLTerm₁ := .eml .one (.eml (.eml .one .one) .one)
private def logTerm : EMLTerm₁ := .eml zeroTerm (.eml (.eml zeroTerm .var) .one)
private def xMinusLogTerm : EMLTerm₁ := .eml logTerm .var
private def logXMinusLogTerm : EMLTerm₁ :=
  .eml zeroTerm (.eml (.eml zeroTerm xMinusLogTerm) .one)
private def xMinus2LogTerm : EMLTerm₁ :=
  .eml logXMinusLogTerm (.eml logTerm .one)
private def twoLogTerm : EMLTerm₁ :=
  .eml logTerm (.eml xMinus2LogTerm .one)
private def sqTerm : EMLTerm₁ := .eml twoLogTerm .one

/-
Helper: x - log x > 0 for x > 0
-/
private lemma x_minus_log_pos (x : ℝ) (hx : 0 < x) : 0 < x - Real.log x := by
  linarith [ Real.log_le_sub_one_of_pos hx ]

/-
Step-by-step evaluation lemmas
-/
private lemma eval_zeroTerm (x : ℝ) : zeroTerm.eval x = 0 := by
  simp [zeroTerm, EMLTerm₁.eval]

private lemma eval_logTerm (x : ℝ) (_hx : 0 < x) : logTerm.eval x = Real.log x := by
  unfold logTerm; simp +decide [ *, EMLTerm₁.eval ] ;

private lemma eval_xMinusLogTerm (x : ℝ) (hx : 0 < x) :
    xMinusLogTerm.eval x = x - Real.log x := by
      convert congr_arg₂ ( · - · ) ( Real.exp_log hx ) rfl using 1;
      convert congr_arg₂ ( · - · ) ( congr_arg Real.exp ( eval_logTerm x hx ) ) rfl using 1

private lemma eval_logXMinusLogTerm (x : ℝ) (hx : 0 < x) :
    logXMinusLogTerm.eval x = Real.log (x - Real.log x) := by
      unfold logXMinusLogTerm;
      -- We'll use the fact that $zeroTerm.eval x = 0$ and $xMinusLogTerm.eval x = x - \log x$.
      have h_eval : zeroTerm.eval x = 0 ∧ xMinusLogTerm.eval x = x - Real.log x := by
        exact ⟨ eval_zeroTerm x, eval_xMinusLogTerm x hx ⟩
      simp [h_eval, EMLTerm₁.eval]

private lemma eval_xMinus2LogTerm (x : ℝ) (hx : 0 < x) :
    xMinus2LogTerm.eval x = x - 2 * Real.log x := by
      convert congr_arg₂ ( · - · ) ( Real.exp_log ( x_minus_log_pos x hx ) ) ( Real.log_exp ( Real.log x ) ) using 1;
      · rw [ show xMinus2LogTerm = .eml logXMinusLogTerm (.eml logTerm .one) from rfl, show logXMinusLogTerm = .eml zeroTerm (.eml (.eml zeroTerm xMinusLogTerm) .one) from rfl, show logTerm = .eml zeroTerm (.eml (.eml zeroTerm .var) .one) from rfl, show zeroTerm = .eml .one (.eml (.eml .one .one) .one) from rfl ] ; simp +decide [ EMLTerm₁.eval ] ;
        rw [ eval_xMinusLogTerm x hx ];
      · ring

private lemma eval_twoLogTerm (x : ℝ) (hx : 0 < x) :
    twoLogTerm.eval x = 2 * Real.log x := by
      unfold twoLogTerm;
      -- Apply the definitions of `logTerm` and `xMinus2LogTerm` to simplify the expression.
      simp [logTerm, xMinus2LogTerm, EMLTerm₁.eval];
      rw [ eval_logXMinusLogTerm x hx, Real.exp_log ( x_minus_log_pos x hx ) ] ; ring;
      rw [ Real.exp_log hx, sub_self, zero_add ]

private lemma eval_sqTerm (x : ℝ) (hx : 0 < x) :
    sqTerm.eval x = x ^ 2 := by
      -- Simplify $sqTerm$ using the results of $twoLogTerm$ and basic properties of exponentiation.
      have h_exp_simplified :
          Real.exp (2 * Real.log x) = x ^ 2 := by
            rw [ mul_comm, Real.exp_mul, Real.exp_log ] <;> norm_cast;
      convert h_exp_simplified using 1
      unfold EMLTerm₁.eval
      simp [sqTerm];
      rw [ eval_twoLogTerm x hx, show EMLTerm₁.eval x EMLTerm₁.one = 1 from by rfl, Real.log_one, sub_zero ]

theorem emlterm1_for_sq_x_pos :
    ∃ t : EMLTerm₁, ∀ x : ℝ, 0 < x → EMLTerm₁.eval x t = x ^ 2 := by
  exact ⟨sqTerm, eval_sqTerm⟩

end EML
