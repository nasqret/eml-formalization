import EML.Framework.Complex.Realization
import Mathlib

/-!
# Complex EML closed-term realizations for `π` and `i`

This module ports the closed-term witnesses of chunks
`034_emlterm_for_pi` and `035_emlterm_for_i` into the
`EMLRealizationℂ` framework.

The chunks define their own local `EMLTermℂ` (without `var`) and prove
`∃ t : EMLTermℂ, t.eval = …` over a TOTAL evaluator. Here we

* re-state the same closed witness term using the framework's
  `EMLTermℂ` (which has a `var` constructor; both witnesses use only
  `.one` and `.eml`, so they port directly), and
* re-run the chunk proofs in the partial-eval (`eval?`) setting,
  threading `EMLTermℂ.eval?_eml_of_ne` and explicit non-zero proofs at
  every `eml(_, b)` step.

The witnesses are environment-independent, so each helper lemma holds
for every `env : Nat → ℂ`. Final realizations are
`realizeℂ_pi` and `realizeℂ_i` at the end of the namespace.
-/

namespace EML

namespace EMLRealizationℂ

/-! ## Real-coercion helpers (verbatim from chunks 034/035) -/

private lemma log_ofReal_pos {r : ℝ} (hr : 0 < r) :
    Complex.log ((r : ℝ) : ℂ) = ((Real.log r : ℝ) : ℂ) :=
  (Complex.ofReal_log hr.le).symm

private lemma exp_ofReal' (r : ℝ) :
    Complex.exp ((r : ℝ) : ℂ) = ((Real.exp r : ℝ) : ℂ) :=
  (Complex.ofReal_exp r).symm

private lemma cone_eq : (1 : ℂ) = ((1 : ℝ) : ℂ) := by push_cast; rfl

private lemma ctwo_eq : (2 : ℂ) = ((2 : ℝ) : ℂ) := by push_cast; rfl

private lemma e_minus_one_pos : (0 : ℝ) < Real.exp 1 - 1 := by
  have := Real.add_one_le_exp (1 : ℝ); linarith

/-! ## Closed sub-terms -/

private def Zt : EMLTermℂ := .eml .one (.eml (.eml .one .one) .one)

private def t₂ : EMLTermℂ := .eml .one .one
private def t₃ : EMLTermℂ := .eml .one t₂
private def t₄ : EMLTermℂ := .eml .one t₃
private def t₅ : EMLTermℂ := .eml t₄ .one
private def t₆ : EMLTermℂ := .eml .one t₅
private def t₇ : EMLTermℂ := .eml t₆ t₂
private def t₈ : EMLTermℂ := .eml t₇ .one
private def TwoT : EMLTermℂ := .eml .one t₈

private def NegOneT : EMLTermℂ := .eml Zt (.eml TwoT .one)

/-- The `Lg` macro: `Lg t` evaluates to `log t.eval` when
`(1 - log t.eval).im ∈ (-π, π]`, i.e. `arg t.eval ∈ (-π, π)`. -/
private def Lg (t : EMLTermℂ) : EMLTermℂ := .eml Zt (.eml (.eml Zt t) .one)

/-- The `ExpT` macro. -/
private def ExpT (t : EMLTermℂ) : EMLTermℂ := .eml t .one

/-- The `Sub` macro. -/
private def Sub (a b : EMLTermℂ) : EMLTermℂ := .eml (Lg a) (ExpT b)

/-! ## Partial-eval helpers for the closed sub-terms

Each helper unfolds its `private def` first so the `eval?_eml_of_ne`
output and the goal are syntactically aligned. -/

private lemma h1' (env : Nat → ℂ) :
    (EMLTermℂ.one : EMLTermℂ).eval? env = some 1 := rfl

private lemma eval?_t₂ (env : Nat → ℂ) :
    t₂.eval? env = some ((Real.exp 1 : ℝ) : ℂ) := by
  show (EMLTermℂ.eml .one .one).eval? env = _
  have h := EMLTermℂ.eval?_eml_of_ne (h1' env) (h1' env) one_ne_zero
  rw [h]
  congr 1
  rw [Complex.log_one, sub_zero, cone_eq, exp_ofReal']

private lemma eval?_t₃ (env : Nat → ℂ) :
    t₃.eval? env = some ((Real.exp 1 - 1 : ℝ) : ℂ) := by
  show (EMLTermℂ.eml .one t₂).eval? env = _
  have hne : ((Real.exp 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.exp_pos 1).ne'
  have h := EMLTermℂ.eval?_eml_of_ne (h1' env) (eval?_t₂ env) hne
  rw [h]
  congr 1
  rw [log_ofReal_pos (Real.exp_pos 1), Real.log_exp, cone_eq, exp_ofReal']
  push_cast; ring

private lemma eval?_t₄ (env : Nat → ℂ) :
    t₄.eval? env =
      some ((Real.exp 1 - Real.log (Real.exp 1 - 1) : ℝ) : ℂ) := by
  show (EMLTermℂ.eml .one t₃).eval? env = _
  have hne : ((Real.exp 1 - 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast e_minus_one_pos.ne'
  have h := EMLTermℂ.eval?_eml_of_ne (h1' env) (eval?_t₃ env) hne
  rw [h]
  congr 1
  rw [log_ofReal_pos e_minus_one_pos, cone_eq, exp_ofReal']
  push_cast; ring

private lemma eval?_t₅ (env : Nat → ℂ) :
    t₅.eval? env =
      some ((Real.exp (Real.exp 1 - Real.log (Real.exp 1 - 1)) : ℝ) : ℂ) := by
  show (EMLTermℂ.eml t₄ .one).eval? env = _
  have h := EMLTermℂ.eval?_eml_of_ne (eval?_t₄ env) (h1' env) one_ne_zero
  rw [h]
  congr 1
  rw [Complex.log_one, sub_zero, exp_ofReal']

private lemma eval?_t₆ (env : Nat → ℂ) :
    t₆.eval? env = some ((Real.log (Real.exp 1 - 1) : ℝ) : ℂ) := by
  show (EMLTermℂ.eml .one t₅).eval? env = _
  have hne :
      ((Real.exp (Real.exp 1 - Real.log (Real.exp 1 - 1)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.exp_pos _).ne'
  have h := EMLTermℂ.eval?_eml_of_ne (h1' env) (eval?_t₅ env) hne
  rw [h]
  congr 1
  rw [log_ofReal_pos (Real.exp_pos _), Real.log_exp, cone_eq, exp_ofReal']
  push_cast; ring

private lemma eval?_t₇ (env : Nat → ℂ) :
    t₇.eval? env = some ((Real.exp 1 - 2 : ℝ) : ℂ) := by
  show (EMLTermℂ.eml t₆ t₂).eval? env = _
  have hne : ((Real.exp 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.exp_pos 1).ne'
  have h := EMLTermℂ.eval?_eml_of_ne (eval?_t₆ env) (eval?_t₂ env) hne
  rw [h]
  congr 1
  rw [exp_ofReal', Real.exp_log e_minus_one_pos,
      log_ofReal_pos (Real.exp_pos 1), Real.log_exp]
  push_cast; ring

private lemma eval?_t₈ (env : Nat → ℂ) :
    t₈.eval? env = some ((Real.exp (Real.exp 1 - 2) : ℝ) : ℂ) := by
  show (EMLTermℂ.eml t₇ .one).eval? env = _
  have h := EMLTermℂ.eval?_eml_of_ne (eval?_t₇ env) (h1' env) one_ne_zero
  rw [h]
  congr 1
  rw [Complex.log_one, sub_zero, exp_ofReal']

private lemma eval?_TwoT (env : Nat → ℂ) :
    TwoT.eval? env = some (2 : ℂ) := by
  show (EMLTermℂ.eml .one t₈).eval? env = _
  have hne : ((Real.exp (Real.exp 1 - 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.exp_pos _).ne'
  have h := EMLTermℂ.eval?_eml_of_ne (h1' env) (eval?_t₈ env) hne
  rw [h]
  congr 1
  rw [log_ofReal_pos (Real.exp_pos _), Real.log_exp, cone_eq, exp_ofReal']
  push_cast; ring

private lemma eval?_inner_Zt (env : Nat → ℂ) :
    (EMLTermℂ.eml (.eml .one .one) .one).eval? env =
      some ((Real.exp (Real.exp 1) : ℝ) : ℂ) := by
  -- this is `eml(t₂, 1)` essentially — but we want it spelled with raw constructors.
  have h := EMLTermℂ.eval?_eml_of_ne (eval?_t₂ env) (h1' env) one_ne_zero
  -- h has shape `(eml t₂ .one).eval? env = some (exp ↑(Real.exp 1) - log 1)`.
  -- But the goal is `(eml (eml .one .one) .one).eval? env`. These are defequal
  -- since t₂ unfolds to `eml .one .one`. We can use `show`.
  show (EMLTermℂ.eml t₂ .one).eval? env = _
  rw [h]
  congr 1
  rw [Complex.log_one, sub_zero, exp_ofReal']

private lemma eval?_Zt (env : Nat → ℂ) : Zt.eval? env = some (0 : ℂ) := by
  show (EMLTermℂ.eml .one (.eml (.eml .one .one) .one)).eval? env = _
  have hne : ((Real.exp (Real.exp 1) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.exp_pos _).ne'
  have h := EMLTermℂ.eval?_eml_of_ne (h1' env) (eval?_inner_Zt env) hne
  rw [h]
  congr 1
  rw [log_ofReal_pos (Real.exp_pos _), Real.log_exp, cone_eq, exp_ofReal']
  push_cast; ring

private lemma eval?_inner_NegOneT (env : Nat → ℂ) :
    (EMLTermℂ.eml TwoT .one).eval? env = some ((Real.exp 2 : ℝ) : ℂ) := by
  have h := EMLTermℂ.eval?_eml_of_ne (eval?_TwoT env) (h1' env) one_ne_zero
  rw [h]
  congr 1
  rw [Complex.log_one, sub_zero, ctwo_eq, exp_ofReal']

private lemma eval?_NegOneT (env : Nat → ℂ) :
    NegOneT.eval? env = some (-1 : ℂ) := by
  show (EMLTermℂ.eml Zt (.eml TwoT .one)).eval? env = _
  have hne : ((Real.exp 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.exp_pos _).ne'
  have h :=
    EMLTermℂ.eval?_eml_of_ne (eval?_Zt env) (eval?_inner_NegOneT env) hne
  rw [h]
  congr 1
  rw [Complex.exp_zero, log_ofReal_pos (Real.exp_pos 2), Real.log_exp]
  push_cast; ring

/-! ## `Lg`, `ExpT`, `Sub` evaluator macros (partial form) -/

private lemma eval?_Lg_of_arg_lt_pi {t : EMLTermℂ} {v : ℂ}
    (env : Nat → ℂ) (ht : t.eval? env = some v)
    (hne : v ≠ 0)
    (h_arg : Complex.arg v < Real.pi) :
    (Lg t).eval? env = some (Complex.log v) := by
  show (EMLTermℂ.eml Zt (.eml (.eml Zt t) .one)).eval? env = _
  -- step a: `eml(Zt, t)`
  have ha := EMLTermℂ.eval?_eml_of_ne (eval?_Zt env) ht hne
  -- step b: `eml((eml Zt t), 1)`
  have hb : (EMLTermℂ.eml (.eml Zt t) .one).eval? env =
      some (Complex.exp ((1 : ℂ) - Complex.log v)) := by
    have hb' := EMLTermℂ.eval?_eml_of_ne ha (h1' env) one_ne_zero
    rw [hb']
    congr 1
    rw [Complex.log_one, sub_zero, Complex.exp_zero]
  -- step c: outer `eml(Zt, hb)`. Need exp(1 - log v) ≠ 0.
  have hc_ne : Complex.exp ((1 : ℂ) - Complex.log v) ≠ 0 := Complex.exp_ne_zero _
  have hc := EMLTermℂ.eval?_eml_of_ne (eval?_Zt env) hb hc_ne
  -- now compute the outer value.
  rw [hc]
  congr 1
  -- Goal: `Complex.exp 0 - Complex.log (Complex.exp (1 - Complex.log v)) = Complex.log v`.
  have h_im₁ : -Real.pi < ((1 : ℂ) - Complex.log v).im := by
    rw [Complex.sub_im, Complex.one_im, Complex.log_im, zero_sub]
    linarith
  have h_im₂ : ((1 : ℂ) - Complex.log v).im ≤ Real.pi := by
    rw [Complex.sub_im, Complex.one_im, Complex.log_im, zero_sub]
    linarith [Complex.neg_pi_lt_arg v]
  rw [Complex.exp_zero, Complex.log_exp h_im₁ h_im₂]
  ring

private lemma eval?_ExpT {t : EMLTermℂ} {v : ℂ}
    (env : Nat → ℂ) (ht : t.eval? env = some v) :
    (ExpT t).eval? env = some (Complex.exp v) := by
  show (EMLTermℂ.eml t .one).eval? env = _
  have h := EMLTermℂ.eval?_eml_of_ne ht (h1' env) one_ne_zero
  rw [h]
  congr 1
  rw [Complex.log_one, sub_zero]

private lemma eval?_Sub_of_safe {a b : EMLTermℂ} {va vb : ℂ}
    (env : Nat → ℂ)
    (h_Lg : (Lg a).eval? env = some (Complex.log va))
    (hb : b.eval? env = some vb)
    (ha_ne : va ≠ 0)
    (hb₁ : -Real.pi < vb.im)
    (hb₂ : vb.im ≤ Real.pi) :
    (Sub a b).eval? env = some (va - vb) := by
  show (EMLTermℂ.eml (Lg a) (ExpT b)).eval? env = _
  have h_ExpT : (ExpT b).eval? env = some (Complex.exp vb) :=
    eval?_ExpT env hb
  have h_ExpT_ne : Complex.exp vb ≠ 0 := Complex.exp_ne_zero _
  have h := EMLTermℂ.eval?_eml_of_ne h_Lg h_ExpT h_ExpT_ne
  rw [h]
  congr 1
  rw [Complex.exp_log ha_ne, Complex.log_exp hb₁ hb₂]

/-! ## `LogN1 := Lg(NegOneT)`, eval = `−πI` -/

private def LogN1 : EMLTermℂ := Lg NegOneT

private lemma eval?_LogN1 (env : Nat → ℂ) :
    LogN1.eval? env = some (-((Real.pi : ℝ) : ℂ) * Complex.I) := by
  show (EMLTermℂ.eml Zt (.eml (.eml Zt NegOneT) .one)).eval? env = _
  -- Step a: eml(Zt, NegOneT). NegOneT.eval = -1, ≠ 0.
  have h_neg1_ne : (-1 : ℂ) ≠ 0 := by norm_num
  have ha :=
    EMLTermℂ.eval?_eml_of_ne (eval?_Zt env) (eval?_NegOneT env) h_neg1_ne
  -- ha gives `some (exp 0 - log (-1)) = some (1 - π·I)`.
  have ha' : (EMLTermℂ.eml Zt NegOneT).eval? env =
      some ((1 : ℂ) - (Real.pi : ℂ) * Complex.I) := by
    rw [ha]; congr 1; rw [Complex.exp_zero, Complex.log_neg_one]
  -- Step b: eml(ha, 1). value = exp(1 - π·I) - log 1 = -e.
  have h_exp : Complex.exp ((1 : ℂ) - (Real.pi : ℂ) * Complex.I) =
      -((Real.exp 1 : ℝ) : ℂ) := by
    rw [show ((1 : ℂ) - (Real.pi : ℂ) * Complex.I) =
            (1 : ℂ) + (-((Real.pi : ℂ) * Complex.I)) from by ring,
        Complex.exp_add, Complex.exp_neg, Complex.exp_pi_mul_I,
        cone_eq, Complex.ofReal_exp]
    push_cast; field_simp
  have hb : (EMLTermℂ.eml (.eml Zt NegOneT) .one).eval? env =
      some (-((Real.exp 1 : ℝ) : ℂ)) := by
    have h := EMLTermℂ.eval?_eml_of_ne ha' (h1' env) one_ne_zero
    rw [h]; congr 1; rw [Complex.log_one, sub_zero, h_exp]
  -- Step c: eml(Zt, hb). value = exp 0 - log(-e) = 1 - (1 + π·I) = -π·I.
  have h_neg_e_ne : -((Real.exp 1 : ℝ) : ℂ) ≠ 0 := by
    intro h
    have h0 : ((Real.exp 1 : ℝ) : ℂ) = 0 := neg_eq_zero.mp h
    have h0r : (Real.exp 1 : ℝ) = 0 := by exact_mod_cast h0
    exact (Real.exp_pos 1).ne' h0r
  have h_log : Complex.log (-((Real.exp 1 : ℝ) : ℂ)) =
      (1 : ℂ) + (Real.pi : ℂ) * Complex.I := by
    have h_rw : -((Real.exp 1 : ℝ) : ℂ) =
        ((Real.exp 1 : ℝ) : ℂ) * (-1 : ℂ) := by ring
    rw [h_rw,
        Complex.log_ofReal_mul (Real.exp_pos 1) (by norm_num : (-1 : ℂ) ≠ 0),
        Real.log_exp, Complex.log_neg_one]
    push_cast; ring
  have hc := EMLTermℂ.eval?_eml_of_ne (eval?_Zt env) hb h_neg_e_ne
  rw [hc]
  congr 1
  rw [Complex.exp_zero, h_log]
  push_cast; ring

/-! ## Auxiliary `arg` and non-zero facts -/

private lemma logN1_value_ne :
    -((Real.pi : ℝ) : ℂ) * Complex.I ≠ 0 := by
  intro h
  have h_im := congrArg Complex.im h
  simp [Real.pi_pos.ne'] at h_im

private lemma arg_LogN1_lt_pi :
    Complex.arg (-((Real.pi : ℝ) : ℂ) * Complex.I) < Real.pi := by
  apply Complex.arg_lt_pi_iff.mpr
  left
  simp [Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]

private lemma arg_TwoT_lt_pi : Complex.arg (2 : ℂ) < Real.pi := by
  apply Complex.arg_lt_pi_iff.mpr
  left
  simp

private lemma log_neg_pi_I :
    Complex.log (-((Real.pi : ℝ) : ℂ) * Complex.I) =
      ((Real.log Real.pi : ℝ) : ℂ) - (Real.pi : ℂ) / 2 * Complex.I := by
  rw [show -((Real.pi : ℝ) : ℂ) * Complex.I =
          ((Real.pi : ℝ) : ℂ) * (-Complex.I) from by ring,
      Complex.log_ofReal_mul Real.pi_pos
        (by simpa using Complex.I_ne_zero),
      Complex.log_neg_I]
  push_cast; ring

/-! ## `eval?_Lg_LogN1` and `eval?_Lg_TwoT` -/

private lemma eval?_Lg_LogN1 (env : Nat → ℂ) :
    (Lg LogN1).eval? env =
      some (((Real.log Real.pi : ℝ) : ℂ) -
             (Real.pi : ℂ) / 2 * Complex.I) := by
  have h := eval?_Lg_of_arg_lt_pi env (eval?_LogN1 env)
              logN1_value_ne arg_LogN1_lt_pi
  rw [log_neg_pi_I] at h
  exact h

private lemma log_two_eq : Complex.log (2 : ℂ) = ((Real.log 2 : ℝ) : ℂ) := by
  have h2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := ctwo_eq
  rw [h2, log_ofReal_pos (by norm_num : (0:ℝ) < 2)]

private lemma eval?_Lg_TwoT (env : Nat → ℂ) :
    (Lg TwoT).eval? env = some ((Real.log 2 : ℝ) : ℂ) := by
  have h := eval?_Lg_of_arg_lt_pi env (eval?_TwoT env)
              (by norm_num : (2 : ℂ) ≠ 0) arg_TwoT_lt_pi
  rw [log_two_eq] at h
  exact h

private lemma Lg_LogN1_value_ne :
    (((Real.log Real.pi : ℝ) : ℂ) - (Real.pi : ℂ) / 2 * Complex.I) ≠ 0 := by
  intro h
  have h_re := congrArg Complex.re h
  have h_log_pi_pos : 0 < Real.log Real.pi :=
    Real.log_pos (by linarith [Real.pi_gt_three])
  have key :
      (((Real.log Real.pi : ℝ) : ℂ) -
        (Real.pi : ℂ) / 2 * Complex.I).re = Real.log Real.pi := by
    rw [show (Real.pi : ℂ) / 2 * Complex.I =
          ((Real.pi / 2 : ℝ) : ℂ) * Complex.I from by push_cast; ring]
    simp
  rw [key, Complex.zero_re] at h_re
  linarith

private lemma arg_Lg_LogN1_lt_pi :
    Complex.arg (((Real.log Real.pi : ℝ) : ℂ) -
                  (Real.pi : ℂ) / 2 * Complex.I) < Real.pi := by
  apply Complex.arg_lt_pi_iff.mpr
  left
  have h_log_pi_pos : 0 < Real.log Real.pi :=
    Real.log_pos (by linarith [Real.pi_gt_three])
  have key :
      (((Real.log Real.pi : ℝ) : ℂ) -
        (Real.pi : ℂ) / 2 * Complex.I).re = Real.log Real.pi := by
    rw [show (Real.pi : ℂ) / 2 * Complex.I =
          ((Real.pi / 2 : ℝ) : ℂ) * Complex.I from by push_cast; ring]
    simp
  rw [key]; linarith

private lemma im_Lg_TwoT_value : (((Real.log 2 : ℝ) : ℂ)).im = 0 :=
  Complex.ofReal_im _

/-! ## `Halve` term, eval = `−πI/2` -/

private def Halve : EMLTermℂ := ExpT (Sub (Lg LogN1) (Lg TwoT))

private lemma eval?_Halve (env : Nat → ℂ) :
    Halve.eval? env =
      some (-((Real.pi : ℝ) : ℂ) / 2 * Complex.I) := by
  -- Inner Sub: Lg LogN1 ↦ log π - π/2·I, Lg TwoT ↦ log 2.
  -- For eval?_Sub_of_safe with a := Lg LogN1, b := Lg TwoT, we need
  -- (Lg (Lg LogN1)).eval? env = some (log of Lg LogN1's value).
  have h_Lg_Lg_LogN1 : (Lg (Lg LogN1)).eval? env =
      some (Complex.log
              (((Real.log Real.pi : ℝ) : ℂ) -
                (Real.pi : ℂ) / 2 * Complex.I)) :=
    eval?_Lg_of_arg_lt_pi env (eval?_Lg_LogN1 env)
      Lg_LogN1_value_ne arg_Lg_LogN1_lt_pi
  -- Compute Sub's value:
  have hsub :=
    eval?_Sub_of_safe (a := Lg LogN1) (b := Lg TwoT)
      (va := ((Real.log Real.pi : ℝ) : ℂ) -
              (Real.pi : ℂ) / 2 * Complex.I)
      (vb := ((Real.log 2 : ℝ) : ℂ))
      env h_Lg_Lg_LogN1 (eval?_Lg_TwoT env) Lg_LogN1_value_ne
      (by rw [im_Lg_TwoT_value]; linarith [Real.pi_pos])
      (by rw [im_Lg_TwoT_value]; linarith [Real.pi_pos])
  -- Now `Halve = ExpT (Sub …)`.
  have h := eval?_ExpT env hsub
  -- Reduce the value.
  show (EMLTermℂ.eml (Sub (Lg LogN1) (Lg TwoT)) .one).eval? env = _
  rw [show (EMLTermℂ.eml (Sub (Lg LogN1) (Lg TwoT)) .one)
        = ExpT (Sub (Lg LogN1) (Lg TwoT)) from rfl]
  rw [h]
  congr 1
  -- target: Complex.exp ((log π - π/2·I) - log 2) = -π/2 · I.
  have hsub_eq :
      ((Real.log Real.pi : ℝ) : ℂ) - (Real.pi : ℂ) / 2 * Complex.I -
          ((Real.log 2 : ℝ) : ℂ) =
        ((Real.log (Real.pi / 2) : ℝ) : ℂ) +
          (-(Real.pi : ℂ) / 2 * Complex.I) := by
    have h2 := Real.log_div Real.pi_pos.ne' (by norm_num : (2 : ℝ) ≠ 0)
    push_cast [h2]; ring
  have h_exp_neg :
      Complex.exp (-(Real.pi : ℂ) / 2 * Complex.I) = -Complex.I := by
    rw [show (-(Real.pi : ℂ) / 2 * Complex.I) =
          (-(Real.pi : ℝ) / 2 : ℂ) * Complex.I from by push_cast; ring]
    exact Complex.exp_neg_pi_div_two_mul_I
  rw [hsub_eq, Complex.exp_add, exp_ofReal',
      Real.exp_log (by linarith [Real.pi_pos] : (0:ℝ) < Real.pi / 2),
      h_exp_neg]
  push_cast; ring

/-! ## `NegI := ExpT(Halve)`, eval = `−i` -/

private def NegI : EMLTermℂ := ExpT Halve

private lemma eval?_NegI (env : Nat → ℂ) :
    NegI.eval? env = some (-Complex.I) := by
  show (EMLTermℂ.eml Halve .one).eval? env = _
  rw [show (EMLTermℂ.eml Halve .one) = ExpT Halve from rfl]
  have h := eval?_ExpT env (eval?_Halve env)
  rw [h]
  congr 1
  rw [show (-((Real.pi : ℝ) : ℂ) / 2 * Complex.I) =
        (-(Real.pi : ℝ) / 2 : ℂ) * Complex.I from by push_cast; ring]
  exact Complex.exp_neg_pi_div_two_mul_I

/-! ## `Lg NegI` and pi witness -/

private lemma negI_ne : (-Complex.I : ℂ) ≠ 0 :=
  neg_ne_zero.mpr Complex.I_ne_zero

private lemma arg_NegI_lt_pi : Complex.arg (-Complex.I : ℂ) < Real.pi := by
  apply Complex.arg_lt_pi_iff.mpr
  left
  simp

private lemma eval?_Lg_NegI (env : Nat → ℂ) :
    (Lg NegI).eval? env =
      some (-((Real.pi : ℝ) : ℂ) / 2 * Complex.I) := by
  have h := eval?_Lg_of_arg_lt_pi env (eval?_NegI env) negI_ne arg_NegI_lt_pi
  rw [show Complex.log (-Complex.I) =
        -((Real.pi : ℝ) : ℂ) / 2 * Complex.I from by
        rw [Complex.log_neg_I]; push_cast; ring] at h
  exact h

private def pi_term : EMLTermℂ := ExpT (Sub (Lg LogN1) (Lg NegI))

private lemma im_Lg_NegI_value :
    (-((Real.pi : ℝ) : ℂ) / 2 * Complex.I).im = -(Real.pi / 2) := by
  simp [Complex.mul_im, Complex.I_im, Complex.I_re,
        Complex.ofReal_re, Complex.ofReal_im,
        Complex.neg_re, Complex.neg_im, neg_div]

private lemma eval?_pi_term (env : Nat → ℂ) :
    pi_term.eval? env = some ((Real.pi : ℂ)) := by
  show (EMLTermℂ.eml (Sub (Lg LogN1) (Lg NegI)) .one).eval? env = _
  rw [show (EMLTermℂ.eml (Sub (Lg LogN1) (Lg NegI)) .one)
        = ExpT (Sub (Lg LogN1) (Lg NegI)) from rfl]
  have h_Lg_Lg_LogN1 : (Lg (Lg LogN1)).eval? env =
      some (Complex.log
              (((Real.log Real.pi : ℝ) : ℂ) -
                (Real.pi : ℂ) / 2 * Complex.I)) :=
    eval?_Lg_of_arg_lt_pi env (eval?_Lg_LogN1 env)
      Lg_LogN1_value_ne arg_Lg_LogN1_lt_pi
  have hsub :=
    eval?_Sub_of_safe (a := Lg LogN1) (b := Lg NegI)
      (va := ((Real.log Real.pi : ℝ) : ℂ) -
              (Real.pi : ℂ) / 2 * Complex.I)
      (vb := -((Real.pi : ℝ) : ℂ) / 2 * Complex.I)
      env h_Lg_Lg_LogN1 (eval?_Lg_NegI env) Lg_LogN1_value_ne
      (by rw [im_Lg_NegI_value]; linarith [Real.pi_pos])
      (by rw [im_Lg_NegI_value]; linarith [Real.pi_pos])
  have h := eval?_ExpT env hsub
  rw [h]
  congr 1
  -- Goal: Complex.exp ((log π - π/2 · I) - (-π/2 · I)) = π.
  have hsub_eq :
      ((Real.log Real.pi : ℝ) : ℂ) - (Real.pi : ℂ) / 2 * Complex.I -
          (-((Real.pi : ℝ) : ℂ) / 2 * Complex.I) =
        ((Real.log Real.pi : ℝ) : ℂ) := by
    push_cast; ring
  rw [hsub_eq, exp_ofReal', Real.exp_log Real.pi_pos]

/-! ## i_term: eval = `Complex.I` -/

/-- `Mt := eml(NegI, eml(NegI, one))`. -/
private def Mt : EMLTermℂ := .eml NegI (.eml NegI .one)

private lemma eval?_Mt (env : Nat → ℂ) :
    Mt.eval? env = some (Complex.exp (-Complex.I) + Complex.I) := by
  show (EMLTermℂ.eml NegI (.eml NegI .one)).eval? env = _
  -- inner: eml(NegI, 1).
  have h_inner : (EMLTermℂ.eml NegI .one).eval? env =
      some (Complex.exp (-Complex.I)) := by
    have h := EMLTermℂ.eval?_eml_of_ne (eval?_NegI env) (h1' env) one_ne_zero
    rw [h]; congr 1; rw [Complex.log_one, sub_zero]
  -- outer: eml(NegI, h_inner). exp(-I) ≠ 0.
  have hne : Complex.exp (-Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have h := EMLTermℂ.eval?_eml_of_ne (eval?_NegI env) h_inner hne
  rw [h]
  congr 1
  -- result: exp(-I) - log(exp(-I)) = exp(-I) + I.
  have h_im₁ : -Real.pi < (-Complex.I : ℂ).im := by
    simp [Complex.neg_im, Complex.I_im]
    linarith [Real.pi_gt_three]
  have h_im₂ : (-Complex.I : ℂ).im ≤ Real.pi := by
    simp [Complex.neg_im, Complex.I_im]
    linarith [Real.pi_pos]
  rw [Complex.log_exp h_im₁ h_im₂]
  ring

private lemma Mt_value_ne :
    Complex.exp (-Complex.I) + Complex.I ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  have h_cos_pos : 0 < Real.cos 1 := Real.cos_one_pos
  simp only [Complex.add_re, Complex.exp_re, Complex.I_re, Complex.I_im,
             Complex.neg_re, Complex.neg_im, Complex.zero_re, neg_zero,
             Real.exp_zero, one_mul, Complex.exp_im, Real.cos_neg, mul_zero,
             zero_add, add_zero] at hr
  linarith

private lemma arg_Mt_value_lt_pi :
    Complex.arg (Complex.exp (-Complex.I) + Complex.I) < Real.pi := by
  apply Complex.arg_lt_pi_iff.mpr
  left
  -- (exp(-i) + i).re = exp(0) cos(-1) = cos(1) ≥ 0.
  simp [Complex.add_re, Complex.exp_re, Complex.I_re, Complex.I_im,
        Complex.neg_re, Complex.neg_im, Real.cos_neg]
  exact Real.cos_one_pos.le

private def i_term : EMLTermℂ := Sub Mt (ExpT NegI)

private lemma eval?_i_term (env : Nat → ℂ) :
    i_term.eval? env = some Complex.I := by
  have h_ExpT_NegI : (ExpT NegI).eval? env =
      some (Complex.exp (-Complex.I)) :=
    eval?_ExpT env (eval?_NegI env)
  have h_Lg_Mt : (Lg Mt).eval? env =
      some (Complex.log (Complex.exp (-Complex.I) + Complex.I)) :=
    eval?_Lg_of_arg_lt_pi env (eval?_Mt env) Mt_value_ne arg_Mt_value_lt_pi
  -- bounds on (exp(-Complex.I)).im = -sin(1) ∈ (-1, 1).
  have h_sin_le_one : Real.sin 1 ≤ 1 := Real.sin_le_one 1
  have h_sin_ge_neg_one : Real.sin 1 ≥ -1 := Real.neg_one_le_sin 1
  have h_im₁ : -Real.pi < (Complex.exp (-Complex.I)).im := by
    simp [Complex.exp_im, Complex.I_re, Complex.I_im,
          Complex.neg_re, Complex.neg_im, Real.sin_neg]
    nlinarith [Real.pi_gt_three]
  have h_im₂ : (Complex.exp (-Complex.I)).im ≤ Real.pi := by
    simp [Complex.exp_im, Complex.I_re, Complex.I_im,
          Complex.neg_re, Complex.neg_im, Real.sin_neg]
    nlinarith [Real.pi_gt_three]
  -- Apply Sub.
  have hfinal :=
    eval?_Sub_of_safe (a := Mt) (b := ExpT NegI)
      (va := Complex.exp (-Complex.I) + Complex.I)
      (vb := Complex.exp (-Complex.I))
      env h_Lg_Mt h_ExpT_NegI Mt_value_ne h_im₁ h_im₂
  -- i_term = Sub Mt (ExpT NegI).
  have h_unfold : i_term = Sub Mt (ExpT NegI) := rfl
  rw [h_unfold, hfinal]
  congr 1
  ring

/-! ## Final: `realizeℂ_pi` and `realizeℂ_i` -/

/-- Realization of the constant function `λ _ => some (Real.pi : ℂ)`. -/
noncomputable def realizeℂ_pi :
    EMLRealizationℂ (fun _ => some (Real.pi : ℂ)) where
  term := pi_term
  spec := fun env v hv => by
    have hv' : v = (Real.pi : ℂ) := (Option.some.inj hv).symm
    rw [hv']
    exact eval?_pi_term env

/-- Realization of the constant function `λ _ => some Complex.I`. -/
noncomputable def realizeℂ_i :
    EMLRealizationℂ (fun _ => some Complex.I) where
  term := i_term
  spec := fun env v hv => by
    have hv' : v = Complex.I := (Option.some.inj hv).symm
    rw [hv']
    exact eval?_i_term env

/-! ## Phase B++ II §A — additional public closed constants

Required by `EML.Framework.Complex.Builders.Trig` for the literal trig
witnesses (chunks 064, 066, 067). All four wrap already-proven private
closed terms; no new arithmetic is needed.
-/

/-- Realization of the constant function `λ _ => some (0 : ℂ)`. -/
noncomputable def realizeℂ_zero :
    EMLRealizationℂ (fun _ => some (0 : ℂ)) where
  term := Zt
  spec := fun env v hv => by
    have hv' : v = (0 : ℂ) := (Option.some.inj hv).symm
    rw [hv']
    exact eval?_Zt env

/-- Realization of the constant function `λ _ => some (2 : ℂ)`. -/
noncomputable def realizeℂ_two :
    EMLRealizationℂ (fun _ => some (2 : ℂ)) where
  term := TwoT
  spec := fun env v hv => by
    have hv' : v = (2 : ℂ) := (Option.some.inj hv).symm
    rw [hv']
    exact eval?_TwoT env

/-- Realization of the constant function `λ _ => some (-Complex.I)`. -/
noncomputable def realizeℂ_negI :
    EMLRealizationℂ (fun _ => some (-Complex.I)) where
  term := NegI
  spec := fun env v hv => by
    have hv' : v = -Complex.I := (Option.some.inj hv).symm
    rw [hv']
    exact eval?_NegI env

end EMLRealizationℂ

end EML
