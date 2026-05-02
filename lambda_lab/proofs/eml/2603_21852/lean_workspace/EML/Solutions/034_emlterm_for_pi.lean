import Mathlib

/-!
# Chunk 034 — EMLTermℂ witness for π

We extend the EML term grammar to complex evaluation and produce an explicit
`t : EMLTermℂ` with `t.eval = (Real.pi : ℂ)`.

Strategy.

The paper (Table S2, step 18) writes `π = √(−(ln(−1))²)`.  Mathlib's
principal-branch `Complex.log` evaluates `log(−1) = π · I`, so its square is
`−π²` and the square root recovers `π`.  However, formalising
`exp(log·…+log·…)` style multiplication runs into a thicket of branch-cut
hypotheses.  We sidestep that by using the *cancellation* identity

```
  log(LogN1) − log(NegI) = (log π − iπ/2) − (−iπ/2) = log π   (real),
```

so `π = exp(log(LogN1) − log(NegI))`.  Concretely:

1. Build `0`, `2`, `−1` (real-valued, branch-safe).
2. `LogN1 := Lg(−1)` evaluates to `−πI` (the macro flips the sign because
   `1 − log(−1) = 1 − πI` lies on the boundary of the principal strip and
   `exp` maps it to `−e`, whose log is `1 + πI`).
3. `Halve(LogN1) := exp(log(LogN1) − log 2) = (LogN1)/2 = −iπ/2`.
4. `NegI := exp(−iπ/2) = −i`.
5. `Lg(NegI)` evaluates to `−iπ/2` (cleanly, since `(−i).im = −1 ∈ (−π, π]`).
6. `Sub(Lg LogN1, Lg NegI)` evaluates to `(log π − iπ/2) − (−iπ/2) = log π`.
7. `pi_term := Exp(Sub(Lg LogN1, Lg NegI))`, whose eval is `exp(log π) = π`.
-/

namespace EML

/-- Complex-valued EML term grammar. -/
inductive EMLTermℂ : Type
  | one : EMLTermℂ
  | eml : EMLTermℂ → EMLTermℂ → EMLTermℂ
  deriving Repr

/-- Evaluation over ℂ (principal branch of `Complex.log`). -/
noncomputable def EMLTermℂ.eval : EMLTermℂ → ℂ
  | .one => 1
  | .eml t u => Complex.exp (eval t) - Complex.log (eval u)

open Complex

/-! ### Cast helpers -/

private lemma log_ofReal_pos {r : ℝ} (hr : 0 < r) :
    Complex.log ((r : ℝ) : ℂ) = ((Real.log r : ℝ) : ℂ) :=
  (Complex.ofReal_log hr.le).symm

private lemma exp_ofReal' (r : ℝ) :
    Complex.exp ((r : ℝ) : ℂ) = ((Real.exp r : ℝ) : ℂ) :=
  (Complex.ofReal_exp r).symm

private lemma cone_eq : (1 : ℂ) = ((1 : ℝ) : ℂ) := by push_cast; rfl

private lemma ctwo_eq : (2 : ℂ) = ((2 : ℝ) : ℂ) := by push_cast; rfl

/-! ### Tree for `0` -/

private def Zt : EMLTermℂ := .eml .one (.eml (.eml .one .one) .one)

private lemma eval_Zt : Zt.eval = 0 := by
  show Complex.exp (1 : ℂ) -
      Complex.log (Complex.exp (Complex.exp (1 : ℂ) - Complex.log (1 : ℂ)) -
        Complex.log (1 : ℂ)) = 0
  rw [Complex.log_one, sub_zero, sub_zero, cone_eq, exp_ofReal', exp_ofReal',
      log_ofReal_pos (Real.exp_pos _), Real.log_exp]
  push_cast; ring

/-! ### Tree for `2` (lifted from chunk 032) -/

private def t₂ : EMLTermℂ := .eml .one .one
private def t₃ : EMLTermℂ := .eml .one t₂
private def t₄ : EMLTermℂ := .eml .one t₃
private def t₅ : EMLTermℂ := .eml t₄ .one
private def t₆ : EMLTermℂ := .eml .one t₅
private def t₇ : EMLTermℂ := .eml t₆ t₂
private def t₈ : EMLTermℂ := .eml t₇ .one
private def TwoT : EMLTermℂ := .eml .one t₈

private lemma e_minus_one_pos : (0 : ℝ) < Real.exp 1 - 1 := by
  have := Real.add_one_le_exp (1 : ℝ); linarith

private lemma eval_t₂ : t₂.eval = ((Real.exp 1 : ℝ) : ℂ) := by
  show Complex.exp (1 : ℂ) - Complex.log (1 : ℂ) = _
  rw [Complex.log_one, sub_zero, cone_eq, exp_ofReal']

private lemma eval_t₃ : t₃.eval = ((Real.exp 1 - 1 : ℝ) : ℂ) := by
  show Complex.exp (1 : ℂ) - Complex.log t₂.eval = _
  rw [eval_t₂, log_ofReal_pos (Real.exp_pos 1), Real.log_exp, cone_eq, exp_ofReal']
  push_cast; ring

private lemma eval_t₄ : t₄.eval = ((Real.exp 1 - Real.log (Real.exp 1 - 1) : ℝ) : ℂ) := by
  show Complex.exp (1 : ℂ) - Complex.log t₃.eval = _
  rw [eval_t₃, log_ofReal_pos e_minus_one_pos, cone_eq, exp_ofReal']
  push_cast; ring

private lemma eval_t₅ :
    t₅.eval = ((Real.exp (Real.exp 1 - Real.log (Real.exp 1 - 1)) : ℝ) : ℂ) := by
  show Complex.exp t₄.eval - Complex.log (1 : ℂ) = _
  rw [eval_t₄, Complex.log_one, sub_zero, exp_ofReal']

private lemma eval_t₆ : t₆.eval = ((Real.log (Real.exp 1 - 1) : ℝ) : ℂ) := by
  show Complex.exp (1 : ℂ) - Complex.log t₅.eval = _
  rw [eval_t₅, log_ofReal_pos (Real.exp_pos _), Real.log_exp, cone_eq, exp_ofReal']
  push_cast; ring

private lemma eval_t₇ : t₇.eval = ((Real.exp 1 - 2 : ℝ) : ℂ) := by
  show Complex.exp t₆.eval - Complex.log t₂.eval = _
  rw [eval_t₆, eval_t₂, exp_ofReal', Real.exp_log e_minus_one_pos,
      log_ofReal_pos (Real.exp_pos 1), Real.log_exp]
  push_cast; ring

private lemma eval_t₈ : t₈.eval = ((Real.exp (Real.exp 1 - 2) : ℝ) : ℂ) := by
  show Complex.exp t₇.eval - Complex.log (1 : ℂ) = _
  rw [eval_t₇, Complex.log_one, sub_zero, exp_ofReal']

private lemma eval_TwoT : TwoT.eval = (2 : ℂ) := by
  show Complex.exp (1 : ℂ) - Complex.log t₈.eval = _
  rw [eval_t₈, log_ofReal_pos (Real.exp_pos _), Real.log_exp, cone_eq, exp_ofReal']
  push_cast; ring

/-! ### Tree for `−1` -/

private def NegOneT : EMLTermℂ := .eml Zt (.eml TwoT .one)

private lemma eval_NegOneT : NegOneT.eval = (-1 : ℂ) := by
  show Complex.exp Zt.eval - Complex.log (Complex.exp TwoT.eval - Complex.log (1 : ℂ)) = _
  rw [eval_Zt, Complex.exp_zero, eval_TwoT, Complex.log_one, sub_zero,
      ctwo_eq, exp_ofReal', log_ofReal_pos (Real.exp_pos 2), Real.log_exp]
  push_cast; ring

/-! ### `Lg`, `ExpT`, `Sub` macros -/

private def Lg (t : EMLTermℂ) : EMLTermℂ := .eml Zt (.eml (.eml Zt t) .one)

private lemma eval_Lg_of_arg_lt_pi {t : EMLTermℂ}
    (h : Complex.arg t.eval < Real.pi) :
    (Lg t).eval = Complex.log t.eval := by
  show Complex.exp Zt.eval -
        Complex.log (Complex.exp (Complex.exp Zt.eval - Complex.log t.eval) -
          Complex.log (1 : ℂ)) = _
  rw [eval_Zt, Complex.exp_zero, Complex.log_one, sub_zero]
  rw [Complex.log_exp ?_ ?_]
  · ring
  · rw [Complex.sub_im, Complex.one_im, Complex.log_im, zero_sub]; linarith
  · rw [Complex.sub_im, Complex.one_im, Complex.log_im, zero_sub]
    linarith [Complex.neg_pi_lt_arg t.eval]

private def ExpT (t : EMLTermℂ) : EMLTermℂ := .eml t .one

private lemma eval_ExpT (t : EMLTermℂ) : (ExpT t).eval = Complex.exp t.eval := by
  show Complex.exp t.eval - Complex.log (1 : ℂ) = _
  rw [Complex.log_one, sub_zero]

private def Sub (a b : EMLTermℂ) : EMLTermℂ := .eml (Lg a) (ExpT b)

private lemma eval_Sub_of_safe
    {a b : EMLTermℂ}
    (hLg : (Lg a).eval = Complex.log a.eval)
    (ha_ne : a.eval ≠ 0)
    (hb₁ : -Real.pi < b.eval.im)
    (hb₂ : b.eval.im ≤ Real.pi) :
    (Sub a b).eval = a.eval - b.eval := by
  show Complex.exp (Lg a).eval - Complex.log (ExpT b).eval = _
  rw [hLg, eval_ExpT, Complex.exp_log ha_ne, Complex.log_exp hb₁ hb₂]

/-! ### `LogN1 := Lg(−1)`, eval = `−πI` -/

private def LogN1 : EMLTermℂ := Lg NegOneT

private lemma eval_LogN1 : LogN1.eval = -((Real.pi : ℝ) : ℂ) * I := by
  show Complex.exp Zt.eval -
        Complex.log (Complex.exp (Complex.exp Zt.eval - Complex.log NegOneT.eval) -
          Complex.log (1 : ℂ)) = _
  rw [eval_Zt, Complex.exp_zero, eval_NegOneT, Complex.log_neg_one, Complex.log_one, sub_zero]
  have h_exp : Complex.exp ((1 : ℂ) - (Real.pi : ℂ) * I) = -((Real.exp 1 : ℝ) : ℂ) := by
    rw [show (1 - (Real.pi : ℂ) * I : ℂ) = (1 : ℂ) + (-((Real.pi : ℂ) * I)) from by ring,
        Complex.exp_add, Complex.exp_neg, Complex.exp_pi_mul_I, cone_eq, Complex.ofReal_exp]
    push_cast; field_simp
  rw [h_exp]
  have h_log : Complex.log (-((Real.exp 1 : ℝ) : ℂ)) = (1 : ℂ) + (Real.pi : ℂ) * I := by
    have h_rewrite : -((Real.exp 1 : ℝ) : ℂ) = ((Real.exp 1 : ℝ) : ℂ) * (-1 : ℂ) := by ring
    rw [h_rewrite,
        Complex.log_ofReal_mul (Real.exp_pos 1) (by norm_num : (-1 : ℂ) ≠ 0),
        Real.log_exp, Complex.log_neg_one]
    push_cast; ring
  rw [h_log]; ring

private lemma logN1_ne : LogN1.eval ≠ 0 := by
  rw [eval_LogN1]
  intro h
  have h_im := congrArg Complex.im h
  simp [Real.pi_pos.ne'] at h_im

/-! ### `Halve(LogN1)` evaluating to `−iπ/2` (= LogN1/2) -/

private lemma log_neg_pi_I :
    Complex.log (-((Real.pi : ℝ) : ℂ) * I) = ((Real.log Real.pi : ℝ) : ℂ) - (Real.pi : ℂ) / 2 * I := by
  rw [show -((Real.pi : ℝ) : ℂ) * I = ((Real.pi : ℝ) : ℂ) * (-I) from by ring,
      Complex.log_ofReal_mul Real.pi_pos (by simpa using Complex.I_ne_zero),
      Complex.log_neg_I]
  push_cast; ring

private lemma arg_LogN1_lt_pi : Complex.arg LogN1.eval < Real.pi := by
  rw [eval_LogN1]
  apply Complex.arg_lt_pi_iff.mpr
  left
  simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]

private lemma eval_Lg_LogN1 : (Lg LogN1).eval =
    ((Real.log Real.pi : ℝ) : ℂ) - (Real.pi : ℂ) / 2 * I := by
  rw [eval_Lg_of_arg_lt_pi arg_LogN1_lt_pi, eval_LogN1, log_neg_pi_I]

private lemma eval_Lg_TwoT : (Lg TwoT).eval = ((Real.log 2 : ℝ) : ℂ) := by
  rw [eval_Lg_of_arg_lt_pi (by
    rw [eval_TwoT]
    apply Complex.arg_lt_pi_iff.mpr
    left
    simp), eval_TwoT, ctwo_eq, log_ofReal_pos (by norm_num : (0:ℝ) < 2)]

private lemma im_Lg_TwoT : (Lg TwoT).eval.im = 0 := by
  rw [eval_Lg_TwoT, Complex.ofReal_im]

private lemma Lg_LogN1_ne : (Lg LogN1).eval ≠ 0 := by
  rw [eval_Lg_LogN1]
  intro h
  have h_re := congrArg Complex.re h
  have h_log_pi_pos : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  have key : (((Real.log Real.pi : ℝ) : ℂ) - (Real.pi : ℂ) / 2 * I).re = Real.log Real.pi := by
    rw [show (Real.pi : ℂ) / 2 * I = ((Real.pi / 2 : ℝ) : ℂ) * I from by push_cast; ring]
    simp
  rw [key, Complex.zero_re] at h_re
  linarith

private lemma arg_Lg_LogN1_lt_pi : Complex.arg (Lg LogN1).eval < Real.pi := by
  rw [eval_Lg_LogN1]
  apply Complex.arg_lt_pi_iff.mpr
  left
  have h_log_pi_pos : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  have key : (((Real.log Real.pi : ℝ) : ℂ) - (Real.pi : ℂ) / 2 * I).re = Real.log Real.pi := by
    rw [show (Real.pi : ℂ) / 2 * I = ((Real.pi / 2 : ℝ) : ℂ) * I from by push_cast; ring]
    simp
  rw [key]; linarith

private def Halve : EMLTermℂ := ExpT (Sub (Lg LogN1) (Lg TwoT))

private lemma eval_Halve : Halve.eval = -((Real.pi : ℝ) : ℂ) / 2 * I := by
  rw [show Halve = ExpT (Sub (Lg LogN1) (Lg TwoT)) from rfl, eval_ExpT,
      eval_Sub_of_safe (a := Lg LogN1) (b := Lg TwoT)
        (eval_Lg_of_arg_lt_pi arg_Lg_LogN1_lt_pi) Lg_LogN1_ne ?_ ?_]
  · rw [eval_Lg_LogN1, eval_Lg_TwoT]
    have hsub : ((Real.log Real.pi : ℝ) : ℂ) - (Real.pi : ℂ) / 2 * I - ((Real.log 2 : ℝ) : ℂ) =
        ((Real.log (Real.pi / 2) : ℝ) : ℂ) + (-(Real.pi : ℂ) / 2 * I) := by
      have h := Real.log_div Real.pi_pos.ne' (by norm_num : (2 : ℝ) ≠ 0)
      push_cast [h]; ring
    rw [hsub, Complex.exp_add, exp_ofReal',
        Real.exp_log (by linarith [Real.pi_pos] : (0:ℝ) < Real.pi / 2)]
    have hexp_neg : Complex.exp (-(Real.pi : ℂ) / 2 * I) = -I := by
      rw [show (-(Real.pi : ℂ) / 2 * I) = (-(Real.pi : ℝ) / 2 : ℂ) * I from by push_cast; ring]
      exact Complex.exp_neg_pi_div_two_mul_I
    rw [hexp_neg]
    push_cast; ring
  · rw [im_Lg_TwoT]; linarith [Real.pi_pos]
  · rw [im_Lg_TwoT]; linarith [Real.pi_pos]

/-! ### `NegI := ExpT(Halve)`, eval = `−i` -/

private def NegI : EMLTermℂ := ExpT Halve

private lemma eval_NegI : NegI.eval = -I := by
  rw [show NegI = ExpT Halve from rfl, eval_ExpT, eval_Halve]
  rw [show (-((Real.pi : ℝ) : ℂ) / 2 * I) = (-(Real.pi : ℝ) / 2 : ℂ) * I from by push_cast; ring]
  exact Complex.exp_neg_pi_div_two_mul_I

/-! ### `Lg(NegI)` evaluating to `−iπ/2` -/

private lemma negI_im : NegI.eval.im = -1 := by
  rw [eval_NegI]; simp

private lemma negI_ne : NegI.eval ≠ 0 := by
  rw [eval_NegI]; exact neg_ne_zero.mpr Complex.I_ne_zero

private lemma arg_NegI_lt_pi : Complex.arg NegI.eval < Real.pi := by
  rw [eval_NegI]
  apply Complex.arg_lt_pi_iff.mpr
  left
  simp

private lemma eval_Lg_NegI : (Lg NegI).eval = -((Real.pi : ℝ) : ℂ) / 2 * I := by
  rw [eval_Lg_of_arg_lt_pi arg_NegI_lt_pi, eval_NegI, Complex.log_neg_I]
  push_cast
  ring

/-! ### Final: `pi_term := Exp(Sub(Lg LogN1, Lg NegI))` -/

private def pi_term : EMLTermℂ := ExpT (Sub (Lg LogN1) (Lg NegI))

private lemma im_Lg_NegI : (Lg NegI).eval.im = -(Real.pi / 2) := by
  rw [eval_Lg_NegI]
  simp [Complex.mul_im, Complex.I_im, Complex.I_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
        neg_div]

private lemma eval_pi_term : pi_term.eval = (Real.pi : ℂ) := by
  show (ExpT (Sub (Lg LogN1) (Lg NegI))).eval = _
  rw [eval_ExpT,
      eval_Sub_of_safe (a := Lg LogN1) (b := Lg NegI)
        (eval_Lg_of_arg_lt_pi arg_Lg_LogN1_lt_pi) Lg_LogN1_ne ?_ ?_]
  · -- Sub.eval = log(LogN1) - log(NegI) = (log π - iπ/2) - (-iπ/2) = log π.
    rw [eval_Lg_LogN1, eval_Lg_NegI]
    have hsub : ((Real.log Real.pi : ℝ) : ℂ) - (Real.pi : ℂ) / 2 * I - (-((Real.pi : ℝ) : ℂ) / 2 * I) =
        ((Real.log Real.pi : ℝ) : ℂ) := by
      push_cast; ring
    rw [hsub, exp_ofReal', Real.exp_log Real.pi_pos]
  · rw [im_Lg_NegI]; linarith [Real.pi_pos]
  · rw [im_Lg_NegI]; linarith [Real.pi_pos]

theorem emlterm_for_pi : ∃ t : EMLTermℂ, t.eval = (Real.pi : ℂ) :=
  ⟨pi_term, eval_pi_term⟩

end EML
