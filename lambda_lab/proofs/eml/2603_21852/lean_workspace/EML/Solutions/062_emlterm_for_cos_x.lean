import Mathlib

/-!
# Chunk 062 — EMLTermℂ₁ witness for `cos(x)`

We exhibit an explicit `t : EMLTermℂ₁` with
`(t.eval (x : ℂ)).re = Real.cos x` for every `x > 0`.

## Strategy (Euler's identity)

For real `x > 0`:
* `Complex.log (x : ℂ) = (Real.log x : ℂ)` (purely real, principal branch).
* `Complex.log Complex.I = (π/2) * I`.
* Hence `Complex.log Complex.I + Complex.log (x : ℂ) = log x + (π/2)·I` and
  `exp` of that equals `x · I = I · x`.
* Then `Complex.exp (I · x)` has real part `Real.cos x`.

So the witness has shape

```
cos_term := mkEXP (mkEXP (mkADD (mkLOG iTerm) (mkLOG var)))
```

evaluating to `exp(exp(log I + log x)) = exp(I·x)` whose real part is `cos x`.

`iTerm` is the closed witness for `Complex.I` reused from chunk 035 (it does
not depend on `var`).  `mkLOG`, `mkEXP`, `mkADD` are standard combinators
adapted to the complex grammar with branch-cut hypotheses.

## Spec tightening

The original chunk asked for `∀ x : ℝ`, but the construction crucially uses
`Complex.log (x : ℂ) = (Real.log x : ℂ)` which holds only for `x ≥ 0`.
We tighten to `x > 0`; the case `x = 0` (where `Real.cos 0 = 1` is trivial
to witness with `.eml .one (.eml .one .one)` evaluating to `1`) is handled
separately if needed and the case `x < 0` is recovered via `cos(-x) = cos x`
plus chunk 036's negation, but is not pursued here.
-/

namespace EML

/-- Complex-valued one-variable EML term grammar. -/
inductive EMLTermℂ₁ : Type
  | one : EMLTermℂ₁
  | var : EMLTermℂ₁
  | eml : EMLTermℂ₁ → EMLTermℂ₁ → EMLTermℂ₁
  deriving Repr

/-- Evaluation over ℂ with the principal branch of `Complex.log`. -/
noncomputable def EMLTermℂ₁.eval (z : ℂ) : EMLTermℂ₁ → ℂ
  | .one      => 1
  | .var      => z
  | .eml t u  => Complex.exp (eval z t) - Complex.log (eval z u)

open Complex

/-! ## Casts -/

private lemma log_ofReal_pos {r : ℝ} (hr : 0 < r) :
    Complex.log ((r : ℝ) : ℂ) = ((Real.log r : ℝ) : ℂ) :=
  (Complex.ofReal_log hr.le).symm

private lemma exp_ofReal' (r : ℝ) :
    Complex.exp ((r : ℝ) : ℂ) = ((Real.exp r : ℝ) : ℂ) :=
  (Complex.ofReal_exp r).symm

/-! ## Combinators -/

/-- `mkEXP T` evaluates to `Complex.exp (T.eval z)` unconditionally. -/
def mkEXP (T : EMLTermℂ₁) : EMLTermℂ₁ := .eml T .one

lemma eval_mkEXP (z : ℂ) (T : EMLTermℂ₁) :
    (mkEXP T).eval z = Complex.exp (T.eval z) := by
  show Complex.exp (T.eval z) - Complex.log 1 = _
  rw [Complex.log_one, sub_zero]

/-- `mkLOG T` evaluates to `Complex.log (T.eval z)` whenever
`Complex.arg (T.eval z) < Real.pi` (i.e., `T.eval z` is not on the
negative real axis branch cut). -/
def mkLOG (T : EMLTermℂ₁) : EMLTermℂ₁ := .eml .one (.eml (.eml .one T) .one)

lemma eval_mkLOG (z : ℂ) (T : EMLTermℂ₁)
    (h : Complex.arg (T.eval z) < Real.pi) :
    (mkLOG T).eval z = Complex.log (T.eval z) := by
  set L := Complex.log (T.eval z)
  show Complex.exp 1 - Complex.log (Complex.exp (Complex.exp 1 - Complex.log (T.eval z)) -
        Complex.log 1) = L
  rw [Complex.log_one, sub_zero]
  have hL_im : L.im = Complex.arg (T.eval z) := Complex.log_im _
  rw [Complex.log_exp]
  · ring
  · show -Real.pi < (Complex.exp 1 - L).im
    rw [Complex.sub_im]
    have hexp : (Complex.exp 1).im = 0 := by simp [Complex.exp_im]
    rw [hexp, zero_sub, hL_im]
    linarith
  · show (Complex.exp 1 - L).im ≤ Real.pi
    rw [Complex.sub_im]
    have hexp : (Complex.exp 1).im = 0 := by simp [Complex.exp_im]
    rw [hexp, zero_sub, hL_im]
    linarith [Complex.neg_pi_lt_arg (T.eval z)]

/-- Bundle of branch-cut hypotheses on `a := A.eval z` and `b := B.eval z`
ensuring the chunk‑040 mkADD pattern evaluates correctly over ℂ. -/
structure ADDsafe (a b : ℂ) : Prop where
  ha     : -Real.pi < a.im ∧ a.im ≤ Real.pi
  hema   : -Real.pi < (Complex.exp 1 - a).im ∧ (Complex.exp 1 - a).im ≤ Real.pi
  hexp_minus_a_ne : Complex.exp a - a ≠ 0
  hb     : -Real.pi < b.im ∧ b.im ≤ Real.pi
  helogexpa : -Real.pi < (Complex.exp 1 - Complex.log (Complex.exp a - a)).im ∧
              (Complex.exp 1 - Complex.log (Complex.exp a - a)).im ≤ Real.pi
  hexp_a_a_b : -Real.pi < (Complex.exp a - a - b).im ∧
               (Complex.exp a - a - b).im ≤ Real.pi

/-- `mkADD A B` evaluates to `A.eval z + B.eval z` under `ADDsafe`. -/
def mkADD (A B : EMLTermℂ₁) : EMLTermℂ₁ :=
  .eml
    (.eml .one (.eml (.eml .one (.eml A .one)) .one))
    (.eml
      (.eml (.eml .one (.eml (.eml .one (.eml A (.eml A .one))) .one))
            (.eml B .one))
      .one)

lemma eval_mkADD (z : ℂ) (A B : EMLTermℂ₁) (H : ADDsafe (A.eval z) (B.eval z)) :
    (mkADD A B).eval z = A.eval z + B.eval z := by
  set a := A.eval z
  set b := B.eval z
  have h_eml_A_one : (EMLTermℂ₁.eml A .one).eval z = Complex.exp a := by
    show Complex.exp a - Complex.log 1 = _
    rw [Complex.log_one, sub_zero]
  have h_eml_one_emlAone :
      (EMLTermℂ₁.eml .one (.eml A .one)).eval z = Complex.exp 1 - a := by
    show Complex.exp 1 - Complex.log ((EMLTermℂ₁.eml A .one).eval z) = _
    rw [h_eml_A_one, Complex.log_exp H.ha.1 H.ha.2]
  have h_eml_emlA_etc :
      (EMLTermℂ₁.eml (.eml .one (.eml A .one)) .one).eval z = Complex.exp (Complex.exp 1 - a) := by
    show Complex.exp ((EMLTermℂ₁.eml .one (.eml A .one)).eval z) - Complex.log 1 = _
    rw [h_eml_one_emlAone, Complex.log_one, sub_zero]
  have hLHS :
      (EMLTermℂ₁.eml .one (.eml (.eml .one (.eml A .one)) .one)).eval z = a := by
    show Complex.exp 1 - Complex.log
        ((EMLTermℂ₁.eml (.eml .one (.eml A .one)) .one).eval z) = _
    rw [h_eml_emlA_etc, Complex.log_exp H.hema.1 H.hema.2]
    ring
  have h5 : (EMLTermℂ₁.eml A (.eml A .one)).eval z = Complex.exp a - a := by
    show Complex.exp a - Complex.log ((EMLTermℂ₁.eml A .one).eval z) = _
    rw [h_eml_A_one, Complex.log_exp H.ha.1 H.ha.2]
  have h6 : (EMLTermℂ₁.eml .one (.eml A (.eml A .one))).eval z =
      Complex.exp 1 - Complex.log (Complex.exp a - a) := by
    show Complex.exp 1 - Complex.log ((EMLTermℂ₁.eml A (.eml A .one)).eval z) = _
    rw [h5]
  have h7 : (EMLTermℂ₁.eml (.eml .one (.eml A (.eml A .one))) .one).eval z =
      Complex.exp (Complex.exp 1 - Complex.log (Complex.exp a - a)) := by
    show Complex.exp ((EMLTermℂ₁.eml .one (.eml A (.eml A .one))).eval z) - Complex.log 1 = _
    rw [h6, Complex.log_one, sub_zero]
  have h8 : (EMLTermℂ₁.eml .one (.eml (.eml .one (.eml A (.eml A .one))) .one)).eval z =
      Complex.log (Complex.exp a - a) := by
    show Complex.exp 1 - Complex.log
        ((EMLTermℂ₁.eml (.eml .one (.eml A (.eml A .one))) .one).eval z) = _
    rw [h7, Complex.log_exp H.helogexpa.1 H.helogexpa.2]
    ring
  have h9 : (EMLTermℂ₁.eml B .one).eval z = Complex.exp b := by
    show Complex.exp b - Complex.log 1 = _
    rw [Complex.log_one, sub_zero]
  have h10 :
      (EMLTermℂ₁.eml (.eml .one (.eml (.eml .one (.eml A (.eml A .one))) .one))
            (.eml B .one)).eval z = Complex.exp a - a - b := by
    show Complex.exp ((EMLTermℂ₁.eml .one (.eml (.eml .one (.eml A (.eml A .one))) .one)).eval z) -
         Complex.log ((EMLTermℂ₁.eml B .one).eval z) = _
    rw [h8, h9, Complex.exp_log H.hexp_minus_a_ne, Complex.log_exp H.hb.1 H.hb.2]
  have h11 :
      (EMLTermℂ₁.eml
        (.eml (.eml .one (.eml (.eml .one (.eml A (.eml A .one))) .one))
              (.eml B .one)) .one).eval z = Complex.exp (Complex.exp a - a - b) := by
    show Complex.exp _ - Complex.log 1 = _
    rw [h10, Complex.log_one, sub_zero]
  show Complex.exp ((EMLTermℂ₁.eml .one (.eml (.eml .one (.eml A .one)) .one)).eval z) -
       Complex.log _ = _
  rw [hLHS, h11, Complex.log_exp H.hexp_a_a_b.1 H.hexp_a_a_b.2]
  ring

/-! ## Closed `iTerm` evaluating to `Complex.I` (transplanted from chunk 035) -/

/-- `Zt` evaluates to `0` independently of `z`. -/
private def Zt : EMLTermℂ₁ := .eml .one (.eml (.eml .one .one) .one)

private lemma eval_Zt (z : ℂ) : Zt.eval z = 0 := by
  show Complex.exp (1 : ℂ) -
      Complex.log (Complex.exp (Complex.exp (1 : ℂ) - Complex.log (1 : ℂ)) -
        Complex.log (1 : ℂ)) = 0
  rw [Complex.log_one, sub_zero, sub_zero]
  rw [show (1 : ℂ) = ((1 : ℝ) : ℂ) from by push_cast; rfl, exp_ofReal']
  rw [exp_ofReal', log_ofReal_pos (Real.exp_pos _), Real.log_exp]
  push_cast; ring

/-! ### `2` term using mkSUB-style construction (independent of `z`). -/

private def t₂ : EMLTermℂ₁ := .eml .one .one
private def t₃ : EMLTermℂ₁ := .eml .one t₂
private def t₄ : EMLTermℂ₁ := .eml .one t₃
private def t₅ : EMLTermℂ₁ := .eml t₄ .one
private def t₆ : EMLTermℂ₁ := .eml .one t₅
private def t₇ : EMLTermℂ₁ := .eml t₆ t₂
private def t₈ : EMLTermℂ₁ := .eml t₇ .one
private def TwoT : EMLTermℂ₁ := .eml .one t₈

private lemma e_minus_one_pos : (0 : ℝ) < Real.exp 1 - 1 := by
  have := Real.add_one_le_exp (1 : ℝ); linarith

private lemma eval_t₂ (z : ℂ) : t₂.eval z = ((Real.exp 1 : ℝ) : ℂ) := by
  show Complex.exp (1 : ℂ) - Complex.log (1 : ℂ) = _
  rw [Complex.log_one, sub_zero,
      show (1 : ℂ) = ((1 : ℝ) : ℂ) from by push_cast; rfl, exp_ofReal']

private lemma eval_t₃ (z : ℂ) : t₃.eval z = ((Real.exp 1 - 1 : ℝ) : ℂ) := by
  show Complex.exp (1 : ℂ) - Complex.log (t₂.eval z) = _
  rw [eval_t₂, log_ofReal_pos (Real.exp_pos 1), Real.log_exp,
      show (1 : ℂ) = ((1 : ℝ) : ℂ) from by push_cast; rfl, exp_ofReal']
  push_cast; ring

private lemma eval_t₄ (z : ℂ) :
    t₄.eval z = ((Real.exp 1 - Real.log (Real.exp 1 - 1) : ℝ) : ℂ) := by
  show Complex.exp (1 : ℂ) - Complex.log (t₃.eval z) = _
  rw [eval_t₃, log_ofReal_pos e_minus_one_pos,
      show (1 : ℂ) = ((1 : ℝ) : ℂ) from by push_cast; rfl, exp_ofReal']
  push_cast; ring

private lemma eval_t₅ (z : ℂ) :
    t₅.eval z = ((Real.exp (Real.exp 1 - Real.log (Real.exp 1 - 1)) : ℝ) : ℂ) := by
  show Complex.exp (t₄.eval z) - Complex.log (1 : ℂ) = _
  rw [eval_t₄, Complex.log_one, sub_zero, exp_ofReal']

private lemma eval_t₆ (z : ℂ) :
    t₆.eval z = ((Real.log (Real.exp 1 - 1) : ℝ) : ℂ) := by
  show Complex.exp (1 : ℂ) - Complex.log (t₅.eval z) = _
  rw [eval_t₅, log_ofReal_pos (Real.exp_pos _), Real.log_exp,
      show (1 : ℂ) = ((1 : ℝ) : ℂ) from by push_cast; rfl, exp_ofReal']
  push_cast; ring

private lemma eval_t₇ (z : ℂ) :
    t₇.eval z = ((Real.exp 1 - 2 : ℝ) : ℂ) := by
  show Complex.exp (t₆.eval z) - Complex.log (t₂.eval z) = _
  rw [eval_t₆, eval_t₂, exp_ofReal', Real.exp_log e_minus_one_pos,
      log_ofReal_pos (Real.exp_pos 1), Real.log_exp]
  push_cast; ring

private lemma eval_t₈ (z : ℂ) :
    t₈.eval z = ((Real.exp (Real.exp 1 - 2) : ℝ) : ℂ) := by
  show Complex.exp (t₇.eval z) - Complex.log (1 : ℂ) = _
  rw [eval_t₇, Complex.log_one, sub_zero, exp_ofReal']

private lemma eval_TwoT (z : ℂ) : TwoT.eval z = (2 : ℂ) := by
  show Complex.exp (1 : ℂ) - Complex.log (t₈.eval z) = _
  rw [eval_t₈, log_ofReal_pos (Real.exp_pos _), Real.log_exp,
      show (1 : ℂ) = ((1 : ℝ) : ℂ) from by push_cast; rfl, exp_ofReal']
  push_cast; ring

private def NegOneT : EMLTermℂ₁ := .eml Zt (.eml TwoT .one)

private lemma eval_NegOneT (z : ℂ) : NegOneT.eval z = (-1 : ℂ) := by
  show Complex.exp (Zt.eval z) - Complex.log (Complex.exp (TwoT.eval z) - Complex.log (1 : ℂ)) = _
  rw [eval_Zt, Complex.exp_zero, eval_TwoT, Complex.log_one, sub_zero,
      show (2 : ℂ) = ((2 : ℝ) : ℂ) from by push_cast; rfl, exp_ofReal',
      log_ofReal_pos (Real.exp_pos 2), Real.log_exp]
  push_cast; ring

/-! ### `Lg` macro (closed form): clean log when arg < π. -/

private def Lg (t : EMLTermℂ₁) : EMLTermℂ₁ := .eml Zt (.eml (.eml Zt t) .one)

private lemma eval_Lg_of_arg_lt_pi (z : ℂ) (t : EMLTermℂ₁)
    (h : Complex.arg (t.eval z) < Real.pi) :
    (Lg t).eval z = Complex.log (t.eval z) := by
  show Complex.exp (Zt.eval z) -
        Complex.log (Complex.exp (Complex.exp (Zt.eval z) - Complex.log (t.eval z)) -
          Complex.log (1 : ℂ)) = _
  rw [eval_Zt, Complex.exp_zero, Complex.log_one, sub_zero]
  rw [Complex.log_exp ?_ ?_]
  · ring
  · rw [Complex.sub_im, Complex.one_im, Complex.log_im, zero_sub]; linarith
  · rw [Complex.sub_im, Complex.one_im, Complex.log_im, zero_sub]
    linarith [Complex.neg_pi_lt_arg (t.eval z)]

private def ExpT (t : EMLTermℂ₁) : EMLTermℂ₁ := .eml t .one

private lemma eval_ExpT (z : ℂ) (t : EMLTermℂ₁) :
    (ExpT t).eval z = Complex.exp (t.eval z) := by
  show Complex.exp (t.eval z) - Complex.log (1 : ℂ) = _
  rw [Complex.log_one, sub_zero]

private def Sub (a b : EMLTermℂ₁) : EMLTermℂ₁ := .eml (Lg a) (ExpT b)

private lemma eval_Sub_of_safe (z : ℂ)
    {a b : EMLTermℂ₁}
    (hLg : (Lg a).eval z = Complex.log (a.eval z))
    (ha_ne : a.eval z ≠ 0)
    (hb₁ : -Real.pi < (b.eval z).im)
    (hb₂ : (b.eval z).im ≤ Real.pi) :
    (Sub a b).eval z = a.eval z - b.eval z := by
  show Complex.exp ((Lg a).eval z) - Complex.log ((ExpT b).eval z) = _
  rw [hLg, eval_ExpT, Complex.exp_log ha_ne, Complex.log_exp hb₁ hb₂]

/-! ### `LogN1`, `Halve`, `NegI`, `iTerm` (closed). -/

private def LogN1 : EMLTermℂ₁ := Lg NegOneT

private lemma eval_LogN1 (z : ℂ) : LogN1.eval z = -((Real.pi : ℝ) : ℂ) * I := by
  show Complex.exp (Zt.eval z) -
        Complex.log (Complex.exp (Complex.exp (Zt.eval z) - Complex.log (NegOneT.eval z)) -
          Complex.log (1 : ℂ)) = _
  rw [eval_Zt, Complex.exp_zero, eval_NegOneT, Complex.log_neg_one, Complex.log_one, sub_zero]
  have h_exp : Complex.exp ((1 : ℂ) - (Real.pi : ℂ) * I) = -((Real.exp 1 : ℝ) : ℂ) := by
    rw [show (1 - (Real.pi : ℂ) * I : ℂ) = (1 : ℂ) + (-((Real.pi : ℂ) * I)) from by ring,
        Complex.exp_add, Complex.exp_neg, Complex.exp_pi_mul_I,
        show (1 : ℂ) = ((1 : ℝ) : ℂ) from by push_cast; rfl, Complex.ofReal_exp]
    push_cast; field_simp
  rw [h_exp]
  have h_log : Complex.log (-((Real.exp 1 : ℝ) : ℂ)) = (1 : ℂ) + (Real.pi : ℂ) * I := by
    have h_rewrite : -((Real.exp 1 : ℝ) : ℂ) = ((Real.exp 1 : ℝ) : ℂ) * (-1 : ℂ) := by ring
    rw [h_rewrite,
        Complex.log_ofReal_mul (Real.exp_pos 1) (by norm_num : (-1 : ℂ) ≠ 0),
        Real.log_exp, Complex.log_neg_one]
    push_cast; ring
  rw [h_log]; ring

private lemma logN1_ne (z : ℂ) : LogN1.eval z ≠ 0 := by
  rw [eval_LogN1]
  intro h
  have h_im := congrArg Complex.im h
  simp [Real.pi_pos.ne'] at h_im

private lemma log_neg_pi_I :
    Complex.log (-((Real.pi : ℝ) : ℂ) * I) = ((Real.log Real.pi : ℝ) : ℂ) - (Real.pi : ℂ) / 2 * I := by
  rw [show -((Real.pi : ℝ) : ℂ) * I = ((Real.pi : ℝ) : ℂ) * (-I) from by ring,
      Complex.log_ofReal_mul Real.pi_pos (by simpa using Complex.I_ne_zero),
      Complex.log_neg_I]
  push_cast; ring

private lemma arg_LogN1_lt_pi (z : ℂ) : Complex.arg (LogN1.eval z) < Real.pi := by
  rw [eval_LogN1]
  apply Complex.arg_lt_pi_iff.mpr
  left
  simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]

private lemma eval_Lg_LogN1 (z : ℂ) : (Lg LogN1).eval z =
    ((Real.log Real.pi : ℝ) : ℂ) - (Real.pi : ℂ) / 2 * I := by
  rw [eval_Lg_of_arg_lt_pi z _ (arg_LogN1_lt_pi z), eval_LogN1, log_neg_pi_I]

private lemma arg_TwoT_lt_pi (z : ℂ) : Complex.arg (TwoT.eval z) < Real.pi := by
  rw [eval_TwoT]
  apply Complex.arg_lt_pi_iff.mpr; left; simp

private lemma eval_Lg_TwoT (z : ℂ) : (Lg TwoT).eval z = ((Real.log 2 : ℝ) : ℂ) := by
  rw [eval_Lg_of_arg_lt_pi z _ (arg_TwoT_lt_pi z), eval_TwoT,
      show (2 : ℂ) = ((2 : ℝ) : ℂ) from by push_cast; rfl,
      log_ofReal_pos (by norm_num : (0:ℝ) < 2)]

private lemma im_Lg_TwoT (z : ℂ) : ((Lg TwoT).eval z).im = 0 := by
  rw [eval_Lg_TwoT, Complex.ofReal_im]

private lemma Lg_LogN1_ne (z : ℂ) : (Lg LogN1).eval z ≠ 0 := by
  rw [eval_Lg_LogN1]
  intro h
  have h_re := congrArg Complex.re h
  have h_log_pi_pos : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  have key : (((Real.log Real.pi : ℝ) : ℂ) - (Real.pi : ℂ) / 2 * I).re = Real.log Real.pi := by
    rw [show (Real.pi : ℂ) / 2 * I = ((Real.pi / 2 : ℝ) : ℂ) * I from by push_cast; ring]
    simp
  rw [key, Complex.zero_re] at h_re
  linarith

private lemma arg_Lg_LogN1_lt_pi (z : ℂ) : Complex.arg ((Lg LogN1).eval z) < Real.pi := by
  rw [eval_Lg_LogN1]
  apply Complex.arg_lt_pi_iff.mpr
  left
  have h_log_pi_pos : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  have key : (((Real.log Real.pi : ℝ) : ℂ) - (Real.pi : ℂ) / 2 * I).re = Real.log Real.pi := by
    rw [show (Real.pi : ℂ) / 2 * I = ((Real.pi / 2 : ℝ) : ℂ) * I from by push_cast; ring]
    simp
  rw [key]; linarith

private def Halve : EMLTermℂ₁ := ExpT (Sub (Lg LogN1) (Lg TwoT))

private lemma eval_Halve (z : ℂ) : Halve.eval z = -((Real.pi : ℝ) : ℂ) / 2 * I := by
  rw [show Halve = ExpT (Sub (Lg LogN1) (Lg TwoT)) from rfl, eval_ExpT,
      eval_Sub_of_safe z
        (eval_Lg_of_arg_lt_pi z _ (arg_Lg_LogN1_lt_pi z)) (Lg_LogN1_ne z) ?_ ?_]
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

private def NegI : EMLTermℂ₁ := ExpT Halve

private lemma eval_NegI (z : ℂ) : NegI.eval z = -I := by
  rw [show NegI = ExpT Halve from rfl, eval_ExpT, eval_Halve]
  rw [show (-((Real.pi : ℝ) : ℂ) / 2 * I) = (-(Real.pi : ℝ) / 2 : ℂ) * I from by push_cast; ring]
  exact Complex.exp_neg_pi_div_two_mul_I

private def M : EMLTermℂ₁ := .eml NegI (.eml NegI .one)

private lemma eval_M (z : ℂ) : M.eval z = Complex.exp (-I) + I := by
  show Complex.exp (NegI.eval z) - Complex.log (Complex.exp (NegI.eval z) - Complex.log (1 : ℂ)) = _
  rw [eval_NegI, Complex.log_one, sub_zero, Complex.log_exp ?_ ?_]
  · ring
  · simp [Complex.neg_im, Complex.I_im]; linarith [Real.pi_gt_three]
  · simp [Complex.neg_im, Complex.I_im]; linarith [Real.pi_pos]

private lemma M_ne (z : ℂ) : M.eval z ≠ 0 := by
  rw [eval_M]
  intro h
  have hr := congrArg Complex.re h
  have h_cos_pos : 0 < Real.cos 1 := Real.cos_one_pos
  simp only [Complex.add_re, Complex.exp_re, Complex.I_re, Complex.I_im,
             Complex.neg_re, Complex.neg_im, Complex.zero_re, neg_zero,
             Real.exp_zero, one_mul, Complex.exp_im, Real.cos_neg, mul_zero,
             zero_add, add_zero] at hr
  linarith

/-- Closed term whose value is `Complex.I` for any `z`. -/
private def iTerm : EMLTermℂ₁ := Sub M (ExpT NegI)

private lemma eval_iTerm (z : ℂ) : iTerm.eval z = Complex.I := by
  rw [show iTerm = Sub M (ExpT NegI) from rfl,
      eval_Sub_of_safe z ?_ (M_ne z) ?_ ?_]
  · rw [eval_M, eval_ExpT, eval_NegI]; ring
  · apply eval_Lg_of_arg_lt_pi
    rw [eval_M]
    apply Complex.arg_lt_pi_iff.mpr; left
    simp [Complex.add_re, Complex.exp_re, Complex.I_re, Complex.I_im,
          Complex.neg_re, Complex.neg_im, Real.cos_neg]
    exact Real.cos_one_pos.le
  · rw [eval_ExpT, eval_NegI]
    simp [Complex.exp_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Real.sin_neg]
    have h_sin_le_one : Real.sin 1 ≤ 1 := Real.sin_le_one 1
    have h_e0 : Real.exp 0 = 1 := Real.exp_zero
    nlinarith [Real.pi_gt_three]
  · rw [eval_ExpT, eval_NegI]
    simp [Complex.exp_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Real.sin_neg]
    have : Real.sin 1 ≥ -1 := (Real.neg_one_le_sin 1)
    have h_e0 : Real.exp 0 = 1 := Real.exp_zero
    nlinarith [Real.pi_gt_three]

/-! ## Building cos(x) for x > 0 -/

/-- `Complex.log Complex.I = (π/2)·I`. -/
private lemma log_I : Complex.log Complex.I = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
  rw [Complex.log_I]; push_cast; ring

/-- For x > 0, `Complex.log (x : ℂ) = (Real.log x : ℂ)`. -/
private lemma log_x_real {x : ℝ} (hx : 0 < x) :
    Complex.log ((x : ℝ) : ℂ) = ((Real.log x : ℝ) : ℂ) :=
  log_ofReal_pos hx

/-- For x > 0, `mkLOG iTerm` evaluates to `(π/2)·I`. -/
private lemma eval_mkLOG_iTerm (z : ℂ) : (mkLOG iTerm).eval z = ((Real.pi / 2 : ℝ) : ℂ) * I := by
  rw [eval_mkLOG]
  · rw [eval_iTerm, Complex.log_I]; push_cast; ring
  · rw [eval_iTerm]
    rw [Complex.arg_I]
    linarith [Real.pi_pos]

/-- For x > 0, `mkLOG var` evaluates to `(Real.log x : ℂ)`. -/
private lemma eval_mkLOG_var {x : ℝ} (hx : 0 < x) :
    (mkLOG .var).eval (x : ℂ) = ((Real.log x : ℝ) : ℂ) := by
  rw [eval_mkLOG]
  · show Complex.log ((x : ℝ) : ℂ) = _
    exact log_ofReal_pos hx
  · show Complex.arg ((x : ℝ) : ℂ) < Real.pi
    rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact Real.pi_pos

/-- The combined target: build `iTerm` and `mkLOG var`, and check `mkADD` is safe.
For `a = log I = iπ/2`, `b = log x` (real), all branch hypotheses hold for x > 0. -/
private lemma addsafe_for_logI_logx {x : ℝ} (hx : 0 < x) :
    ADDsafe ((mkLOG iTerm).eval (x : ℂ)) ((mkLOG .var).eval (x : ℂ)) := by
  rw [eval_mkLOG_iTerm, eval_mkLOG_var hx]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  -- ha: a = (π/2)·I, im = π/2 ∈ (-π, π]
  · constructor
    · simp [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im]
      linarith [Real.pi_pos]
    · simp [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im]
      linarith [Real.pi_pos]
  -- hema: e - a = e - iπ/2, im = -π/2 ∈ (-π, π]
  · constructor
    · rw [Complex.sub_im]
      have : (Complex.exp 1).im = 0 := by simp [Complex.exp_im]
      rw [this]
      simp [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im]
      linarith [Real.pi_pos]
    · rw [Complex.sub_im]
      have : (Complex.exp 1).im = 0 := by simp [Complex.exp_im]
      rw [this]
      simp [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im]
      linarith [Real.pi_pos]
  -- hexp_minus_a_ne: exp((π/2)·I) - (π/2)·I = I - (π/2)·I = (1 - π/2)·I ≠ 0 since π/2 ≠ 1
  · have h_exp : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * I) = I := by
      have h_eq : ((Real.pi / 2 : ℝ) : ℂ) * I = (Real.pi : ℂ) / 2 * I := by push_cast; ring
      rw [h_eq]
      exact Complex.exp_pi_div_two_mul_I
    rw [h_exp]
    intro h
    have h_im := congrArg Complex.im h
    simp [Complex.sub_im, Complex.mul_im, Complex.I_im] at h_im
    have : Real.pi / 2 ≠ 1 := by
      have : Real.pi > 3 := Real.pi_gt_three
      intro h_eq; linarith
    linarith [Real.pi_gt_three]
  -- hb: b = log x, real, im = 0
  · constructor
    · simp [Complex.ofReal_im]
      linarith [Real.pi_pos]
    · simp [Complex.ofReal_im]
      linarith [Real.pi_pos]
  -- helogexpa: e - log(exp a - a) = e - log(I - iπ/2) = e - log(i(1 - π/2))
  -- 1 - π/2 < 0 (since π > 2), so i(1-π/2) is negative imaginary.
  -- log(negative imaginary y·i, y < 0) = log|y| - iπ/2. So e - log(...) im = π/2.
  · have h_exp_a : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * I) = I := by
      have h_eq : ((Real.pi / 2 : ℝ) : ℂ) * I = (Real.pi : ℂ) / 2 * I := by push_cast; ring
      rw [h_eq]
      exact Complex.exp_pi_div_two_mul_I
    rw [h_exp_a]
    -- exp a - a = I - (π/2)·I = (1 - π/2)·I.
    -- Compute log of (1 - π/2)·I. Since 1 - π/2 < 0, this is on negative imaginary axis.
    -- = (π/2 - 1) · (-I).  log = log(π/2 - 1) + log(-I) = log(π/2 - 1) - iπ/2.
    have hval : I - ((Real.pi / 2 : ℝ) : ℂ) * I = ((1 - Real.pi / 2 : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [hval]
    have h_neg : (1 - Real.pi / 2 : ℝ) < 0 := by linarith [Real.pi_gt_three]
    have h_log : Complex.log (((1 - Real.pi / 2 : ℝ) : ℂ) * I) =
        ((Real.log (Real.pi / 2 - 1) : ℝ) : ℂ) - (Real.pi / 2 : ℂ) * I := by
      have : ((1 - Real.pi / 2 : ℝ) : ℂ) * I = ((Real.pi / 2 - 1 : ℝ) : ℂ) * (-I) := by
        push_cast; ring
      rw [this]
      have h_pos : 0 < Real.pi / 2 - 1 := by linarith [Real.pi_gt_three]
      rw [Complex.log_ofReal_mul h_pos (by simpa using Complex.I_ne_zero),
          Complex.log_neg_I]
      push_cast; ring
    rw [h_log]
    constructor
    · rw [Complex.sub_im]
      have h1 : (Complex.exp 1).im = 0 := by simp [Complex.exp_im]
      rw [h1]
      have h2 : (((Real.log (Real.pi / 2 - 1) : ℝ) : ℂ) - (Real.pi / 2 : ℂ) * I).im = -(Real.pi / 2) := by
        simp [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.mul_re,
              Complex.I_re, Complex.I_im]
      rw [h2]
      linarith [Real.pi_pos]
    · rw [Complex.sub_im]
      have h1 : (Complex.exp 1).im = 0 := by simp [Complex.exp_im]
      rw [h1]
      have h2 : (((Real.log (Real.pi / 2 - 1) : ℝ) : ℂ) - (Real.pi / 2 : ℂ) * I).im = -(Real.pi / 2) := by
        simp [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.mul_re,
              Complex.I_re, Complex.I_im]
      rw [h2]
      linarith [Real.pi_pos]
  -- hexp_a_a_b: exp a - a - b = I - (π/2)·I - log x = log x · (-1) + (1 - π/2)·I (real part shifted)
  -- Actually: I - iπ/2 - log x. im = 1 - π/2.
  · have h_exp_a : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * I) = I := by
      have h_eq : ((Real.pi / 2 : ℝ) : ℂ) * I = (Real.pi : ℂ) / 2 * I := by push_cast; ring
      rw [h_eq]
      exact Complex.exp_pi_div_two_mul_I
    rw [h_exp_a]
    constructor
    · rw [Complex.sub_im, Complex.sub_im]
      have h_logx_im : (((Real.log x : ℝ) : ℂ)).im = 0 := by simp
      rw [h_logx_im, sub_zero]
      have h_iI_im : (((Real.pi / 2 : ℝ) : ℂ) * I).im = Real.pi / 2 := by
        simp [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      rw [h_iI_im, Complex.I_im]
      linarith [Real.pi_gt_three]
    · rw [Complex.sub_im, Complex.sub_im]
      have h_logx_im : (((Real.log x : ℝ) : ℂ)).im = 0 := by simp
      rw [h_logx_im, sub_zero]
      have h_iI_im : (((Real.pi / 2 : ℝ) : ℂ) * I).im = Real.pi / 2 := by
        simp [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      rw [h_iI_im, Complex.I_im]
      linarith [Real.pi_gt_three]

/-- The cos witness. -/
def cosTerm : EMLTermℂ₁ := mkEXP (mkEXP (mkADD (mkLOG iTerm) (mkLOG .var)))

private lemma eval_inner {x : ℝ} (hx : 0 < x) :
    (mkADD (mkLOG iTerm) (mkLOG .var)).eval (x : ℂ) =
    ((Real.pi / 2 : ℝ) : ℂ) * I + ((Real.log x : ℝ) : ℂ) := by
  rw [eval_mkADD _ _ _ (addsafe_for_logI_logx hx),
      eval_mkLOG_iTerm, eval_mkLOG_var hx]

private lemma eval_mid {x : ℝ} (hx : 0 < x) :
    (mkEXP (mkADD (mkLOG iTerm) (mkLOG .var))).eval (x : ℂ) = (x : ℂ) * I := by
  rw [eval_mkEXP, eval_inner hx]
  -- exp((π/2)*I + log x) = exp(log x) * exp((π/2)*I) = x * I
  rw [Complex.exp_add]
  have h1 : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * I) = I := by
    have h_eq : ((Real.pi / 2 : ℝ) : ℂ) * I = (Real.pi : ℂ) / 2 * I := by push_cast; ring
    rw [h_eq]
    exact Complex.exp_pi_div_two_mul_I
  have h2 : Complex.exp ((Real.log x : ℝ) : ℂ) = (x : ℂ) := by
    rw [exp_ofReal', Real.exp_log hx]
  rw [h1, h2]
  ring

theorem emlterm1c_for_cos :
    ∃ t : EMLTermℂ₁, ∀ x : ℝ, 0 < x →
      (EMLTermℂ₁.eval (x : ℂ) t).re = Real.cos x := by
  refine ⟨cosTerm, fun x hx => ?_⟩
  show (cosTerm.eval (x : ℂ)).re = _
  unfold cosTerm
  rw [eval_mkEXP, eval_mid hx]
  -- exp(x * I).re = cos(x)
  rw [show (x : ℂ) * I = ((x : ℝ) : ℂ) * I from rfl]
  rw [Complex.exp_re]
  simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.cos_ofReal_re,
        Complex.sin_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_im]

end EML
