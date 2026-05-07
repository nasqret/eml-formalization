import EML.Framework.Complex.Realization
import Mathlib

/-!
# Trigonometric closures (cos, sin) over ℂ

This file provides `EMLRealizationℂ` instances whose terms are the
Euler-identity witnesses transplanted from `EML/Solutions/062` and
`EML/Solutions/063`:

* `cosTermℂ` evaluates to `Complex.exp (Complex.I * env 0)` (so its real part
  is `Real.cos x` whenever `env 0 = (x : ℝ)`).
* `sinTermℂ` evaluates to `Complex.exp (Complex.I * (env 0 - π/2))` (so its
  real part is `Real.sin x` whenever `env 0 = (x : ℝ)`).

## Honest scope: not literal `Complex.cos`

A literal complex EML witness `eval? env = some (Complex.cos (env 0))`
would require synthesising the Euler decomposition
`(exp(iz) + exp(-iz)) / 2` inside the EML grammar. The grammar has no
addition or division at the top level — these would need to be built
from `eml(_, _) = exp _ − log _`.  Building `+` of two non-real
complex numbers without any positivity (a "complex `mkAdd`") and then
dividing by `2` (which ranges anywhere on the complex plane) requires
delicate branch-cut bookkeeping that explodes the witness size and is
not pursued here.

Instead this file produces:

1. `realizeℂ_exp_I_var` / `realizeℂ_exp_I_sub_pi2` — literal complex
   `EMLRealizationℂ`s for the Euler-shifted exponentials (these are
   the witnesses that the source chunks already construct).
2. `cos_re_bridge` / `sin_re_bridge` — bridges showing that the real
   part of those witnesses' values equals `Real.cos`/`Real.sin` on the
   appropriate real domains.

This is the same scope chunks 062/063 reach (they prove
`(eval z t).re = Real.cos x`); the upgrade is only the partial
`EMLTermℂ` semantics and the Nat-indexed variable convention.

The partial domain of `realizeℂ_exp_I_var` is exactly
`{env | env 0 = ((x : ℝ) : ℂ) ∧ 0 < x}` (cos), and for sin the
domain is `0 < x < π`. The forward-only spec of `EMLRealizationℂ`
makes this sound: `f` is `none` outside that domain, so the
witness's behaviour outside is irrelevant.
-/

namespace EML

open Complex
open Classical

/-! ## Casts (private helpers) -/

private lemma log_ofReal_pos {r : ℝ} (hr : 0 < r) :
    Complex.log ((r : ℝ) : ℂ) = ((Real.log r : ℝ) : ℂ) :=
  (Complex.ofReal_log hr.le).symm

private lemma exp_ofReal' (r : ℝ) :
    Complex.exp ((r : ℝ) : ℂ) = ((Real.exp r : ℝ) : ℂ) :=
  (Complex.ofReal_exp r).symm

/-! ## eval?-flavoured combinators on the framework grammar

The proofs below mirror chunks 062/063 closely but thread non-zero
proofs through the partial `eval?` rather than relying on the total
eval used in those chunks.
-/

/-- `mkExpℂ T` builds `eml(T, one)`, evaluating to `exp (T.eval)`. -/
def mkExpℂ (T : EMLTermℂ) : EMLTermℂ := .eml T .one

lemma eval?_mkExpℂ {env : Nat → ℂ} {T : EMLTermℂ} {v : ℂ}
    (hT : T.eval? env = some v) :
    (mkExpℂ T).eval? env = some (Complex.exp v) := by
  unfold mkExpℂ
  have h := EMLTermℂ.eval?_eml_of_ne hT (EMLTermℂ.eval?_one env) one_ne_zero
  rw [Complex.log_one, sub_zero] at h
  exact h

/-- `mkLogℂ T` builds the log macro `eml(one, eml(eml(one, T), one))`,
evaluating to `Complex.log (T.eval)` whenever `T.eval ≠ 0` and
`arg(T.eval) < π`. -/
def mkLogℂ (T : EMLTermℂ) : EMLTermℂ := .eml .one (.eml (.eml .one T) .one)

lemma eval?_mkLogℂ {env : Nat → ℂ} {T : EMLTermℂ} {v : ℂ}
    (hT : T.eval? env = some v) (hv : v ≠ 0)
    (harg : Complex.arg v < Real.pi) :
    (mkLogℂ T).eval? env = some (Complex.log v) := by
  unfold mkLogℂ
  -- inner: eml(one, T) = exp 1 - log v
  have h1 : (EMLTermℂ.eml .one T).eval? env =
      some (Complex.exp 1 - Complex.log v) :=
    EMLTermℂ.eval?_eml_of_ne (EMLTermℂ.eval?_one env) hT hv
  -- next: eml(eml(one, T), one) = exp(exp 1 - log v) - log 1 = exp(exp 1 - log v)
  have h2 : (EMLTermℂ.eml (.eml .one T) .one).eval? env =
      some (Complex.exp (Complex.exp 1 - Complex.log v)) := by
    have := EMLTermℂ.eval?_eml_of_ne h1 (EMLTermℂ.eval?_one env) one_ne_zero
    rw [Complex.log_one, sub_zero] at this
    exact this
  -- non-zero: exp _ ≠ 0
  have hexp_ne : Complex.exp (Complex.exp 1 - Complex.log v) ≠ 0 :=
    Complex.exp_ne_zero _
  -- outer: eml(one, ...) = exp 1 - log(exp(exp 1 - log v))
  have h3 := EMLTermℂ.eval?_eml_of_ne (EMLTermℂ.eval?_one env) h2 hexp_ne
  rw [h3]
  congr 1
  -- Compute log(exp w) = w when w.im ∈ (-π, π].
  -- w = exp 1 - log v, w.im = - (log v).im = - arg v.
  have hL_im : (Complex.log v).im = Complex.arg v := Complex.log_im v
  have hexp1_im : (Complex.exp 1).im = 0 := by simp [Complex.exp_im]
  have hw_im : (Complex.exp 1 - Complex.log v).im = -Complex.arg v := by
    rw [Complex.sub_im, hexp1_im, zero_sub, hL_im]
  rw [Complex.log_exp]
  · ring
  · rw [hw_im]; linarith
  · rw [hw_im]; linarith [Complex.neg_pi_lt_arg v]

/-! ## Closed `iTermℂ` evaluating to `Complex.I` (transplanted from chunk 035) -/

/-- `Ztℂ` evaluates to `0` independently of `env`. -/
private def Ztℂ : EMLTermℂ := .eml .one (.eml (.eml .one .one) .one)

private lemma eval?_Ztℂ (env : Nat → ℂ) : Ztℂ.eval? env = some 0 := by
  -- Step through: log 1 = 0, exp 1 - 0 = exp 1, log(exp 1) = 1 (since (exp 1).im = 0 ∈ (-π,π])
  -- (exp(1) - log 1) - log 1 = exp 1, then exp(exp 1) - log 1 = exp(exp 1)
  -- log(exp(exp 1)) = exp 1 (since (exp(exp 1)).im = 0). exp 1 - log(exp(exp 1)) = exp 1 - exp 1 = 0
  unfold Ztℂ
  -- innermost: eml(one, one) = exp 1 - log 1 = exp 1
  have e1 : (EMLTermℂ.eml (.one : EMLTermℂ) .one).eval? env = some (Complex.exp 1) := by
    have h := EMLTermℂ.eval?_eml_of_ne (EMLTermℂ.eval?_one env) (EMLTermℂ.eval?_one env) one_ne_zero
    rw [Complex.log_one, sub_zero] at h; exact h
  -- next: eml(eml(one, one), one) = exp(exp 1) - log 1 = exp(exp 1)
  have e2 : (EMLTermℂ.eml (.eml .one .one) .one).eval? env = some (Complex.exp (Complex.exp 1)) := by
    have h := EMLTermℂ.eval?_eml_of_ne e1 (EMLTermℂ.eval?_one env) one_ne_zero
    rw [Complex.log_one, sub_zero] at h; exact h
  -- outer: eml(one, eml(eml(one,one), one)) = exp 1 - log(exp(exp 1)) = exp 1 - exp 1 = 0
  have e3 : Complex.exp (Complex.exp 1) ≠ 0 := Complex.exp_ne_zero _
  have h := EMLTermℂ.eval?_eml_of_ne (EMLTermℂ.eval?_one env) e2 e3
  rw [h]
  congr 1
  -- exp 1 - log(exp(exp 1)) = 0; need (exp 1).im = 0 ∈ (-π,π].
  rw [Complex.log_exp ?_ ?_]
  · ring
  · simp [Complex.exp_im]; linarith [Real.pi_pos]
  · simp [Complex.exp_im]; linarith [Real.pi_pos]

/-! ### `2` and `-1` terms (independent of env). -/

private def t₂ℂ : EMLTermℂ := .eml .one .one
private def t₃ℂ : EMLTermℂ := .eml .one t₂ℂ
private def t₄ℂ : EMLTermℂ := .eml .one t₃ℂ
private def t₅ℂ : EMLTermℂ := .eml t₄ℂ .one
private def t₆ℂ : EMLTermℂ := .eml .one t₅ℂ
private def t₇ℂ : EMLTermℂ := .eml t₆ℂ t₂ℂ
private def t₈ℂ : EMLTermℂ := .eml t₇ℂ .one
private def TwoTℂ : EMLTermℂ := .eml .one t₈ℂ

private lemma e_minus_one_pos : (0 : ℝ) < Real.exp 1 - 1 := by
  have := Real.add_one_le_exp (1 : ℝ); linarith

private lemma eval?_t₂ℂ (env : Nat → ℂ) :
    t₂ℂ.eval? env = some ((Real.exp 1 : ℝ) : ℂ) := by
  unfold t₂ℂ
  have h := EMLTermℂ.eval?_eml_of_ne (EMLTermℂ.eval?_one env) (EMLTermℂ.eval?_one env) one_ne_zero
  rw [h]; congr 1
  rw [Complex.log_one, sub_zero,
      show (1 : ℂ) = ((1 : ℝ) : ℂ) from by push_cast; rfl, exp_ofReal']

private lemma t₂ℂ_ne (env : Nat → ℂ) :
    ((Real.exp 1 : ℝ) : ℂ) ≠ 0 := by
  have := Real.exp_pos (1 : ℝ)
  exact_mod_cast this.ne'

private lemma eval?_t₃ℂ (env : Nat → ℂ) :
    t₃ℂ.eval? env = some ((Real.exp 1 - 1 : ℝ) : ℂ) := by
  unfold t₃ℂ
  have h := EMLTermℂ.eval?_eml_of_ne (EMLTermℂ.eval?_one env) (eval?_t₂ℂ env) (t₂ℂ_ne env)
  rw [h]; congr 1
  rw [log_ofReal_pos (Real.exp_pos 1), Real.log_exp,
      show (1 : ℂ) = ((1 : ℝ) : ℂ) from by push_cast; rfl, exp_ofReal']
  push_cast; ring

private lemma t₃ℂ_ne (env : Nat → ℂ) :
    ((Real.exp 1 - 1 : ℝ) : ℂ) ≠ 0 := by
  have := e_minus_one_pos
  exact_mod_cast this.ne'

private lemma eval?_t₄ℂ (env : Nat → ℂ) :
    t₄ℂ.eval? env = some ((Real.exp 1 - Real.log (Real.exp 1 - 1) : ℝ) : ℂ) := by
  unfold t₄ℂ
  have h := EMLTermℂ.eval?_eml_of_ne (EMLTermℂ.eval?_one env) (eval?_t₃ℂ env) (t₃ℂ_ne env)
  rw [h]; congr 1
  rw [log_ofReal_pos e_minus_one_pos,
      show (1 : ℂ) = ((1 : ℝ) : ℂ) from by push_cast; rfl, exp_ofReal']
  push_cast; ring

private lemma eval?_t₅ℂ (env : Nat → ℂ) :
    t₅ℂ.eval? env = some ((Real.exp (Real.exp 1 - Real.log (Real.exp 1 - 1)) : ℝ) : ℂ) := by
  unfold t₅ℂ
  have h := EMLTermℂ.eval?_eml_of_ne (eval?_t₄ℂ env) (EMLTermℂ.eval?_one env) one_ne_zero
  rw [h]; congr 1
  rw [Complex.log_one, sub_zero, exp_ofReal']

private lemma t₅ℂ_ne (env : Nat → ℂ) :
    ((Real.exp (Real.exp 1 - Real.log (Real.exp 1 - 1)) : ℝ) : ℂ) ≠ 0 := by
  have := Real.exp_pos (Real.exp 1 - Real.log (Real.exp 1 - 1))
  exact_mod_cast this.ne'

private lemma eval?_t₆ℂ (env : Nat → ℂ) :
    t₆ℂ.eval? env = some ((Real.log (Real.exp 1 - 1) : ℝ) : ℂ) := by
  unfold t₆ℂ
  have h := EMLTermℂ.eval?_eml_of_ne (EMLTermℂ.eval?_one env) (eval?_t₅ℂ env) (t₅ℂ_ne env)
  rw [h]; congr 1
  rw [log_ofReal_pos (Real.exp_pos _), Real.log_exp,
      show (1 : ℂ) = ((1 : ℝ) : ℂ) from by push_cast; rfl, exp_ofReal']
  push_cast; ring

private lemma eval?_t₇ℂ (env : Nat → ℂ) :
    t₇ℂ.eval? env = some ((Real.exp 1 - 2 : ℝ) : ℂ) := by
  unfold t₇ℂ
  have h := EMLTermℂ.eval?_eml_of_ne (eval?_t₆ℂ env) (eval?_t₂ℂ env) (t₂ℂ_ne env)
  rw [h]; congr 1
  rw [exp_ofReal', Real.exp_log e_minus_one_pos,
      log_ofReal_pos (Real.exp_pos 1), Real.log_exp]
  push_cast; ring

private lemma eval?_t₈ℂ (env : Nat → ℂ) :
    t₈ℂ.eval? env = some ((Real.exp (Real.exp 1 - 2) : ℝ) : ℂ) := by
  unfold t₈ℂ
  have h := EMLTermℂ.eval?_eml_of_ne (eval?_t₇ℂ env) (EMLTermℂ.eval?_one env) one_ne_zero
  rw [h]; congr 1
  rw [Complex.log_one, sub_zero, exp_ofReal']

private lemma t₈ℂ_ne (env : Nat → ℂ) :
    ((Real.exp (Real.exp 1 - 2) : ℝ) : ℂ) ≠ 0 := by
  have := Real.exp_pos (Real.exp 1 - 2)
  exact_mod_cast this.ne'

private lemma eval?_TwoTℂ (env : Nat → ℂ) : TwoTℂ.eval? env = some (2 : ℂ) := by
  unfold TwoTℂ
  have h := EMLTermℂ.eval?_eml_of_ne (EMLTermℂ.eval?_one env) (eval?_t₈ℂ env) (t₈ℂ_ne env)
  rw [h]; congr 1
  rw [log_ofReal_pos (Real.exp_pos _), Real.log_exp,
      show (1 : ℂ) = ((1 : ℝ) : ℂ) from by push_cast; rfl, exp_ofReal']
  push_cast; ring

private def NegOneTℂ : EMLTermℂ := .eml Ztℂ (.eml TwoTℂ .one)

private lemma eval?_NegOneTℂ (env : Nat → ℂ) :
    NegOneTℂ.eval? env = some (-1 : ℂ) := by
  unfold NegOneTℂ
  -- inner-RHS: eml(TwoT, one) = exp 2 - log 1 = exp 2
  have hr : (EMLTermℂ.eml TwoTℂ .one).eval? env = some (Complex.exp 2) := by
    have h := EMLTermℂ.eval?_eml_of_ne (eval?_TwoTℂ env) (EMLTermℂ.eval?_one env) one_ne_zero
    rw [h]; congr 1; rw [Complex.log_one, sub_zero]
  -- exp 2 ≠ 0
  have hr_ne : Complex.exp (2 : ℂ) ≠ 0 := Complex.exp_ne_zero _
  have h := EMLTermℂ.eval?_eml_of_ne (eval?_Ztℂ env) hr hr_ne
  rw [h]; congr 1
  rw [Complex.exp_zero,
      show (2 : ℂ) = ((2 : ℝ) : ℂ) from by push_cast; rfl, exp_ofReal',
      log_ofReal_pos (Real.exp_pos 2), Real.log_exp]
  push_cast; ring

/-! ### `Lg` macro: clean log when arg < π. -/

private def Lgℂ (t : EMLTermℂ) : EMLTermℂ := .eml Ztℂ (.eml (.eml Ztℂ t) .one)

private lemma eval?_Lgℂ_of_arg_lt_pi {env : Nat → ℂ} {t : EMLTermℂ} {v : ℂ}
    (ht : t.eval? env = some v) (hv : v ≠ 0)
    (harg : Complex.arg v < Real.pi) :
    (Lgℂ t).eval? env = some (Complex.log v) := by
  unfold Lgℂ
  -- eml(Zt, t) eval = exp 0 - log v = 1 - log v
  have h1 : (EMLTermℂ.eml Ztℂ t).eval? env = some (1 - Complex.log v) := by
    have h := EMLTermℂ.eval?_eml_of_ne (eval?_Ztℂ env) ht hv
    rw [h]; congr 1; rw [Complex.exp_zero]
  -- eml(eml(Zt, t), one) = exp(1 - log v) - log 1 = exp(1 - log v)
  have h2 : (EMLTermℂ.eml (.eml Ztℂ t) .one).eval? env =
      some (Complex.exp (1 - Complex.log v)) := by
    have h := EMLTermℂ.eval?_eml_of_ne h1 (EMLTermℂ.eval?_one env) one_ne_zero
    rw [h]; congr 1; rw [Complex.log_one, sub_zero]
  have h2_ne : Complex.exp (1 - Complex.log v) ≠ 0 := Complex.exp_ne_zero _
  have h3 := EMLTermℂ.eval?_eml_of_ne (eval?_Ztℂ env) h2 h2_ne
  rw [h3]; congr 1
  rw [Complex.exp_zero]
  -- 1 - log(exp(1 - log v)) = log v.
  -- (1 - log v).im = -arg v, in (-π, π) ⊆ (-π, π].
  have hL_im : (Complex.log v).im = Complex.arg v := Complex.log_im v
  have hw_im : (1 - Complex.log v : ℂ).im = -Complex.arg v := by
    simp [Complex.sub_im, Complex.one_im, hL_im]
  rw [Complex.log_exp]
  · ring
  · rw [hw_im]; linarith
  · rw [hw_im]; linarith [Complex.neg_pi_lt_arg v]

private def ExpTℂ (t : EMLTermℂ) : EMLTermℂ := .eml t .one

private lemma eval?_ExpTℂ {env : Nat → ℂ} {t : EMLTermℂ} {v : ℂ}
    (ht : t.eval? env = some v) :
    (ExpTℂ t).eval? env = some (Complex.exp v) := by
  unfold ExpTℂ
  have h := EMLTermℂ.eval?_eml_of_ne ht (EMLTermℂ.eval?_one env) one_ne_zero
  rw [h]; congr 1; rw [Complex.log_one, sub_zero]

private def Subℂ (a b : EMLTermℂ) : EMLTermℂ := .eml (Lgℂ a) (ExpTℂ b)

private lemma eval?_Subℂ_of_safe
    {env : Nat → ℂ} {a b : EMLTermℂ} {va vb : ℂ}
    (ha : a.eval? env = some va) (ha_ne : va ≠ 0)
    (haarg : Complex.arg va < Real.pi)
    (hb : b.eval? env = some vb)
    (hb1 : -Real.pi < vb.im) (hb2 : vb.im ≤ Real.pi) :
    (Subℂ a b).eval? env = some (va - vb) := by
  unfold Subℂ
  have hLg : (Lgℂ a).eval? env = some (Complex.log va) :=
    eval?_Lgℂ_of_arg_lt_pi ha ha_ne haarg
  have hExp : (ExpTℂ b).eval? env = some (Complex.exp vb) :=
    eval?_ExpTℂ hb
  have hExp_ne : Complex.exp vb ≠ 0 := Complex.exp_ne_zero _
  have h := EMLTermℂ.eval?_eml_of_ne hLg hExp hExp_ne
  rw [h]; congr 1
  rw [Complex.exp_log ha_ne, Complex.log_exp hb1 hb2]

/-! ### LogN1, Halve, NegI, iTerm (closed). -/

private def LogN1ℂ : EMLTermℂ := Lgℂ NegOneTℂ

private lemma eval?_LogN1ℂ (env : Nat → ℂ) :
    LogN1ℂ.eval? env = some (-((Real.pi : ℝ) : ℂ) * Complex.I) := by
  -- LogN1ℂ = Lgℂ NegOneTℂ unfolds to:
  -- eml(Zt, eml(eml(Zt, NegOneT), one)).
  -- We manually compute since `arg(-1) = π`, not strictly less.
  unfold LogN1ℂ Lgℂ
  -- inner: eml(Zt, NegOneT) eval = exp 0 - log(-1) = 1 - πI
  have h_negone := eval?_NegOneTℂ env
  have h_negone_ne : (-1 : ℂ) ≠ 0 := by norm_num
  have h1 : (EMLTermℂ.eml Ztℂ NegOneTℂ).eval? env = some (1 - Real.pi * Complex.I) := by
    have h := EMLTermℂ.eval?_eml_of_ne (eval?_Ztℂ env) h_negone h_negone_ne
    rw [h]; congr 1
    rw [Complex.exp_zero, Complex.log_neg_one]
  -- next: eml(eml(Zt, NegOneT), one) eval = exp(1 - πI) - log 1 = exp(1 - πI) = -e
  have h_exp_val : Complex.exp (1 - Real.pi * Complex.I) = -((Real.exp 1 : ℝ) : ℂ) := by
    rw [show (1 - (Real.pi : ℂ) * Complex.I : ℂ) =
        (1 : ℂ) + (-((Real.pi : ℂ) * Complex.I)) from by ring,
        Complex.exp_add, Complex.exp_neg, Complex.exp_pi_mul_I,
        show (1 : ℂ) = ((1 : ℝ) : ℂ) from by push_cast; rfl, Complex.ofReal_exp]
    push_cast; field_simp
  have h2 : (EMLTermℂ.eml (.eml Ztℂ NegOneTℂ) .one).eval? env =
      some (-((Real.exp 1 : ℝ) : ℂ)) := by
    have h := EMLTermℂ.eval?_eml_of_ne h1 (EMLTermℂ.eval?_one env) one_ne_zero
    rw [h]; congr 1
    rw [Complex.log_one, sub_zero, h_exp_val]
  -- outer: eml(Zt, h2) = exp 0 - log(-e) = 1 - (1 + πI) = -πI
  have h_neg_e_ne : -((Real.exp 1 : ℝ) : ℂ) ≠ 0 := by
    have hep : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have : ((Real.exp 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hep.ne'
    intro h
    apply this
    linear_combination -h
  have h := EMLTermℂ.eval?_eml_of_ne (eval?_Ztℂ env) h2 h_neg_e_ne
  rw [h]; congr 1
  rw [Complex.exp_zero]
  -- log(-e) = 1 + πI
  have h_log_neg_e : Complex.log (-((Real.exp 1 : ℝ) : ℂ)) = (1 : ℂ) + (Real.pi : ℂ) * Complex.I := by
    have h_rewrite : -((Real.exp 1 : ℝ) : ℂ) = ((Real.exp 1 : ℝ) : ℂ) * (-1 : ℂ) := by ring
    rw [h_rewrite,
        Complex.log_ofReal_mul (Real.exp_pos 1) (by norm_num : (-1 : ℂ) ≠ 0),
        Real.log_exp, Complex.log_neg_one]
    push_cast; ring
  rw [h_log_neg_e]
  push_cast; ring

private lemma LogN1ℂ_ne (env : Nat → ℂ) : -((Real.pi : ℝ) : ℂ) * Complex.I ≠ 0 := by
  intro h
  have h_im := congrArg Complex.im h
  simp [Real.pi_pos.ne'] at h_im

private lemma log_neg_pi_I :
    Complex.log (-((Real.pi : ℝ) : ℂ) * Complex.I) =
      ((Real.log Real.pi : ℝ) : ℂ) - (Real.pi : ℂ) / 2 * Complex.I := by
  rw [show -((Real.pi : ℝ) : ℂ) * Complex.I = ((Real.pi : ℝ) : ℂ) * (-Complex.I) from by ring,
      Complex.log_ofReal_mul Real.pi_pos (by simpa using Complex.I_ne_zero),
      Complex.log_neg_I]
  push_cast; ring

private lemma arg_LogN1ℂ_lt_pi : Complex.arg (-((Real.pi : ℝ) : ℂ) * Complex.I) < Real.pi := by
  apply Complex.arg_lt_pi_iff.mpr
  left
  simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]

private lemma eval?_Lgℂ_LogN1ℂ (env : Nat → ℂ) :
    (Lgℂ LogN1ℂ).eval? env =
      some (((Real.log Real.pi : ℝ) : ℂ) - (Real.pi : ℂ) / 2 * Complex.I) := by
  have h := eval?_Lgℂ_of_arg_lt_pi (eval?_LogN1ℂ env) (LogN1ℂ_ne env) arg_LogN1ℂ_lt_pi
  rw [h]; congr 1; exact log_neg_pi_I

private lemma arg_TwoTℂ_lt_pi : Complex.arg (2 : ℂ) < Real.pi := by
  apply Complex.arg_lt_pi_iff.mpr; left; simp

private lemma eval?_Lgℂ_TwoTℂ (env : Nat → ℂ) :
    (Lgℂ TwoTℂ).eval? env = some ((Real.log 2 : ℝ) : ℂ) := by
  have h := eval?_Lgℂ_of_arg_lt_pi (eval?_TwoTℂ env) (by norm_num : (2 : ℂ) ≠ 0)
            arg_TwoTℂ_lt_pi
  rw [h]; congr 1
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from by push_cast; rfl,
      log_ofReal_pos (by norm_num : (0:ℝ) < 2)]

private lemma im_log_2 : (((Real.log 2 : ℝ) : ℂ)).im = 0 := Complex.ofReal_im _

private lemma Lg_LogN1ℂ_ne :
    ((Real.log Real.pi : ℝ) : ℂ) - (Real.pi : ℂ) / 2 * Complex.I ≠ 0 := by
  intro h
  have h_re := congrArg Complex.re h
  have h_log_pi_pos : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  have key : (((Real.log Real.pi : ℝ) : ℂ) - (Real.pi : ℂ) / 2 * Complex.I).re = Real.log Real.pi := by
    rw [show (Real.pi : ℂ) / 2 * Complex.I = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I from by push_cast; ring]
    simp
  rw [key, Complex.zero_re] at h_re
  linarith

private lemma arg_Lg_LogN1ℂ_lt_pi :
    Complex.arg (((Real.log Real.pi : ℝ) : ℂ) - (Real.pi : ℂ) / 2 * Complex.I) < Real.pi := by
  apply Complex.arg_lt_pi_iff.mpr
  left
  have h_log_pi_pos : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  have key : (((Real.log Real.pi : ℝ) : ℂ) - (Real.pi : ℂ) / 2 * Complex.I).re = Real.log Real.pi := by
    rw [show (Real.pi : ℂ) / 2 * Complex.I = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I from by push_cast; ring]
    simp
  rw [key]; linarith

private def Halveℂ : EMLTermℂ := ExpTℂ (Subℂ (Lgℂ LogN1ℂ) (Lgℂ TwoTℂ))

private lemma eval?_Halveℂ (env : Nat → ℂ) :
    Halveℂ.eval? env = some (-((Real.pi : ℝ) : ℂ) / 2 * Complex.I) := by
  unfold Halveℂ
  -- Sub: (Lg LogN1) - (Lg TwoT) = (log π - iπ/2) - log 2
  have hSub := eval?_Subℂ_of_safe
    (eval?_Lgℂ_LogN1ℂ env) Lg_LogN1ℂ_ne arg_Lg_LogN1ℂ_lt_pi
    (eval?_Lgℂ_TwoTℂ env)
    (by rw [im_log_2]; linarith [Real.pi_pos])
    (by rw [im_log_2]; linarith [Real.pi_pos])
  have h := eval?_ExpTℂ hSub
  rw [h]; congr 1
  -- exp((log π - iπ/2) - log 2) = exp(log(π/2) + (-iπ/2)) = (π/2) * (-Complex.I)
  have hsub : (((Real.log Real.pi : ℝ) : ℂ) - (Real.pi : ℂ) / 2 * Complex.I) - ((Real.log 2 : ℝ) : ℂ) =
      ((Real.log (Real.pi / 2) : ℝ) : ℂ) + (-(Real.pi : ℂ) / 2 * Complex.I) := by
    have hl := Real.log_div Real.pi_pos.ne' (by norm_num : (2 : ℝ) ≠ 0)
    push_cast [hl]; ring
  rw [hsub, Complex.exp_add, exp_ofReal',
      Real.exp_log (by linarith [Real.pi_pos] : (0:ℝ) < Real.pi / 2)]
  have hexp_neg : Complex.exp (-(Real.pi : ℂ) / 2 * Complex.I) = -Complex.I := by
    rw [show (-(Real.pi : ℂ) / 2 * Complex.I) = (-(Real.pi : ℝ) / 2 : ℂ) * Complex.I from by push_cast; ring]
    exact Complex.exp_neg_pi_div_two_mul_I
  rw [hexp_neg]
  push_cast; ring

private def NegIℂ : EMLTermℂ := ExpTℂ Halveℂ

private lemma eval?_NegIℂ (env : Nat → ℂ) : NegIℂ.eval? env = some (-Complex.I) := by
  unfold NegIℂ
  have h := eval?_ExpTℂ (eval?_Halveℂ env)
  rw [h]; congr 1
  rw [show (-((Real.pi : ℝ) : ℂ) / 2 * Complex.I) = (-(Real.pi : ℝ) / 2 : ℂ) * Complex.I from by push_cast; ring]
  exact Complex.exp_neg_pi_div_two_mul_I

private def Mℂ : EMLTermℂ := .eml NegIℂ (.eml NegIℂ .one)

private lemma eval?_Mℂ (env : Nat → ℂ) : Mℂ.eval? env = some (Complex.exp (-Complex.I) + Complex.I) := by
  unfold Mℂ
  -- inner: eml(NegI, one) = exp(-Complex.I) - log 1 = exp(-Complex.I)
  have h1 : (EMLTermℂ.eml NegIℂ .one).eval? env = some (Complex.exp (-Complex.I)) := by
    have h := EMLTermℂ.eval?_eml_of_ne (eval?_NegIℂ env) (EMLTermℂ.eval?_one env) one_ne_zero
    rw [h]; congr 1; rw [Complex.log_one, sub_zero]
  have h1_ne : Complex.exp (-Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have h := EMLTermℂ.eval?_eml_of_ne (eval?_NegIℂ env) h1 h1_ne
  rw [h]; congr 1
  -- exp(-Complex.I) - log(exp(-Complex.I)) = exp(-Complex.I) - (-Complex.I) = exp(-Complex.I) + Complex.I (since -Complex.I.im = -1 ∈ (-π, π])
  rw [Complex.log_exp ?_ ?_]
  · ring
  · simp [Complex.neg_im, Complex.I_im]; linarith [Real.pi_gt_three]
  · simp [Complex.neg_im, Complex.I_im]; linarith [Real.pi_pos]

private lemma Mℂ_ne : Complex.exp (-Complex.I) + Complex.I ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  have h_cos_pos : 0 < Real.cos 1 := Real.cos_one_pos
  simp only [Complex.add_re, Complex.exp_re, Complex.I_re, Complex.I_im,
             Complex.neg_re, Complex.neg_im, Complex.zero_re, neg_zero,
             Real.exp_zero, one_mul, Complex.exp_im, Real.cos_neg, mul_zero,
             zero_add, add_zero] at hr
  linarith

private lemma arg_Mℂ_lt_pi : Complex.arg (Complex.exp (-Complex.I) + Complex.I) < Real.pi := by
  apply Complex.arg_lt_pi_iff.mpr; left
  simp [Complex.add_re, Complex.exp_re, Complex.I_re, Complex.I_im,
        Complex.neg_re, Complex.neg_im, Real.cos_neg]
  exact Real.cos_one_pos.le

/-- Closed term whose value is `Complex.I` for any `env`. -/
private def iTermℂ : EMLTermℂ := Subℂ Mℂ (ExpTℂ NegIℂ)

private lemma eval?_iTermℂ (env : Nat → ℂ) : iTermℂ.eval? env = some Complex.I := by
  unfold iTermℂ
  have hExpNegI : (ExpTℂ NegIℂ).eval? env = some (Complex.exp (-Complex.I)) :=
    eval?_ExpTℂ (eval?_NegIℂ env)
  -- (exp(-Complex.I)).im = sin(-1) = -sin 1 ∈ (-1, 0) ⊂ (-π, π]
  have h_im_lo : -Real.pi < (Complex.exp (-Complex.I)).im := by
    simp [Complex.exp_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Real.sin_neg]
    have h_sin_le_one : Real.sin 1 ≤ 1 := Real.sin_le_one 1
    have h_e0 : Real.exp 0 = 1 := Real.exp_zero
    nlinarith [Real.pi_gt_three]
  have h_im_hi : (Complex.exp (-Complex.I)).im ≤ Real.pi := by
    simp [Complex.exp_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Real.sin_neg]
    have : Real.sin 1 ≥ -1 := Real.neg_one_le_sin 1
    have h_e0 : Real.exp 0 = 1 := Real.exp_zero
    nlinarith [Real.pi_gt_three]
  have h := eval?_Subℂ_of_safe (eval?_Mℂ env) Mℂ_ne arg_Mℂ_lt_pi
            hExpNegI h_im_lo h_im_hi
  rw [h]; congr 1
  ring

/-! ## Building exp(Complex.I*z) for env 0 = (x : ℝ) with x > 0 -/

/-- The inner LHS sub-term of the `mkAdd`-pattern in the cos witness. -/
private def cosLhsℂ : EMLTermℂ :=
  .eml .one (.eml (.eml .one (.eml (mkLogℂ iTermℂ) .one)) .one)

/-- The inner RHS sub-term of the `mkAdd`-pattern in the cos witness. -/
private def cosRhsℂ : EMLTermℂ :=
  .eml
    (.eml (.eml .one (.eml (.eml .one (.eml (mkLogℂ iTermℂ) (.eml (mkLogℂ iTermℂ) .one))) .one))
          (.eml (mkLogℂ (.var 0)) .one))
    .one

/-- The "cos witness" term: `mkExpℂ (mkExpℂ (mkAddℂ (mkLogℂ iTermℂ) (mkLogℂ (var 0))))`,
which evaluates to `exp(exp(log Complex.I + log x)) = exp(Complex.I * x)` whenever
`env 0 = (x : ℝ)` for `x > 0`. -/
def cosTermℂ : EMLTermℂ :=
  mkExpℂ (mkExpℂ (.eml cosLhsℂ cosRhsℂ))

/-! ### Key value computation: cosTermℂ evaluates to exp(Complex.I*z) when env 0 = (x:ℝ), x > 0. -/

/-- When `env 0 = ((x : ℝ) : ℂ)` with `x > 0`, the inner `mkLogℂ` of
`var 0` evaluates to `(log x : ℂ)`. -/
private lemma eval?_mkLogℂ_var_real {env : Nat → ℂ} {x : ℝ}
    (hx : 0 < x) (hev : env 0 = ((x : ℝ) : ℂ)) :
    (mkLogℂ (.var 0)).eval? env = some (((Real.log x : ℝ) : ℂ)) := by
  have hT : (EMLTermℂ.var 0).eval? env = some ((x : ℝ) : ℂ) := by
    rw [EMLTermℂ.eval?_var, hev]
  have hne : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have harg : Complex.arg ((x : ℝ) : ℂ) < Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_pos
  have h := eval?_mkLogℂ hT hne harg
  rw [h]; congr 1
  exact log_ofReal_pos hx

/-- `mkLogℂ iTermℂ` evaluates to `(π/2) * Complex.I`. -/
private lemma eval?_mkLogℂ_iTerm (env : Nat → ℂ) :
    (mkLogℂ iTermℂ).eval? env = some (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
  have hI : iTermℂ.eval? env = some Complex.I := eval?_iTermℂ env
  have hne : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have harg : Complex.arg Complex.I < Real.pi := by
    rw [Complex.arg_I]; linarith [Real.pi_pos]
  have h := eval?_mkLogℂ hI hne harg
  rw [h]; congr 1
  rw [Complex.log_I]; push_cast; ring

/-- The full inner: cosTermℂ's body `mkAddℂ` part. The expansion of
`mkAddℂ (mkLogℂ iTerm) (mkLogℂ var)` (using chunk-040 ADD pattern) evaluates
to `(π/2) * Complex.I + log x` when env 0 = (x : ℝ), x > 0. -/
private lemma eval?_inner_add {env : Nat → ℂ} {x : ℝ}
    (hx : 0 < x) (hev : env 0 = ((x : ℝ) : ℂ)) :
    (EMLTermℂ.eml cosLhsℂ cosRhsℂ).eval? env =
      some (((Real.pi / 2 : ℝ) : ℂ) * Complex.I + ((Real.log x : ℝ) : ℂ)) := by
  unfold cosLhsℂ cosRhsℂ
  -- Let a := (π/2)*Complex.I and b := (log x : ℂ).
  set a : ℂ := ((Real.pi / 2 : ℝ) : ℂ) * Complex.I with ha_def
  set b : ℂ := ((Real.log x : ℝ) : ℂ) with hb_def
  have hA : (mkLogℂ iTermℂ).eval? env = some a := eval?_mkLogℂ_iTerm env
  have hB : (mkLogℂ (.var 0)).eval? env = some b := eval?_mkLogℂ_var_real hx hev
  -- Step 1: eml(mkLogℂ iTerm, one) eval = exp a - log 1 = exp a = Complex.I
  have e_mlT_one : (EMLTermℂ.eml (mkLogℂ iTermℂ) .one).eval? env = some (Complex.exp a) := by
    have h := EMLTermℂ.eval?_eml_of_ne hA (EMLTermℂ.eval?_one env) one_ne_zero
    rw [h]; congr 1; rw [Complex.log_one, sub_zero]
  -- exp a = Complex.I (since a = (π/2)*Complex.I)
  have h_exp_a : Complex.exp a = Complex.I := by
    rw [ha_def]
    have h_eq : ((Real.pi / 2 : ℝ) : ℂ) * Complex.I = (Real.pi : ℂ) / 2 * Complex.I := by push_cast; ring
    rw [h_eq]; exact Complex.exp_pi_div_two_mul_I
  -- Step 2: eml(one, eml(mkLogℂ iTerm, one)) = exp 1 - log(exp a) = exp 1 - a
  -- non-zero of exp a:
  have hexp_a_ne : Complex.exp a ≠ 0 := Complex.exp_ne_zero _
  -- a.im = π/2 ∈ (-π, π]
  have ha_im : a.im = Real.pi / 2 := by
    rw [ha_def]
    simp [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  have ha_im_lo : -Real.pi < a.im := by rw [ha_im]; linarith [Real.pi_pos]
  have ha_im_hi : a.im ≤ Real.pi := by rw [ha_im]; linarith [Real.pi_pos]
  have e_one_mlT_one :
      (EMLTermℂ.eml .one (.eml (mkLogℂ iTermℂ) .one)).eval? env = some (Complex.exp 1 - a) := by
    have h := EMLTermℂ.eval?_eml_of_ne (EMLTermℂ.eval?_one env) e_mlT_one hexp_a_ne
    rw [h]; congr 1
    rw [Complex.log_exp ha_im_lo ha_im_hi]
  -- Step 3: eml(eml(one, eml(mkLogℂ iTerm, one)), one) = exp(exp 1 - a) - log 1 = exp(exp 1 - a)
  have e_emlone_etc : (EMLTermℂ.eml (.eml .one (.eml (mkLogℂ iTermℂ) .one)) .one).eval? env =
      some (Complex.exp (Complex.exp 1 - a)) := by
    have h := EMLTermℂ.eval?_eml_of_ne e_one_mlT_one (EMLTermℂ.eval?_one env) one_ne_zero
    rw [h]; congr 1; rw [Complex.log_one, sub_zero]
  -- Step 4: lhs = eml(one, eml(eml(one, eml(mkLogℂ iTerm, one)), one)) = exp 1 - log(exp(exp 1 - a))
  -- (exp 1 - a).im = -π/2 ∈ (-π, π]
  have hexp_minus_a_im : (Complex.exp 1 - a).im = -(Real.pi / 2) := by
    rw [Complex.sub_im]
    have hexp1_im : (Complex.exp 1).im = 0 := by simp [Complex.exp_im]
    rw [hexp1_im, ha_im]; ring
  have hema_im_lo : -Real.pi < (Complex.exp 1 - a).im := by rw [hexp_minus_a_im]; linarith [Real.pi_pos]
  have hema_im_hi : (Complex.exp 1 - a).im ≤ Real.pi := by rw [hexp_minus_a_im]; linarith [Real.pi_pos]
  have hexp_ema_ne : Complex.exp (Complex.exp 1 - a) ≠ 0 := Complex.exp_ne_zero _
  have e_lhs : (EMLTermℂ.eml .one (.eml (.eml .one (.eml (mkLogℂ iTermℂ) .one)) .one)).eval? env =
      some a := by
    have h := EMLTermℂ.eval?_eml_of_ne (EMLTermℂ.eval?_one env) e_emlone_etc hexp_ema_ne
    rw [h]; congr 1
    rw [Complex.log_exp hema_im_lo hema_im_hi]; ring
  -- Step 5: eml(mkLogℂ iTerm, eml(mkLogℂ iTerm, one)) = exp a - log(exp a) = exp a - a = Complex.I - (π/2)*Complex.I = (1 - π/2)*Complex.I
  have e_emlA_emlAone : (EMLTermℂ.eml (mkLogℂ iTermℂ) (.eml (mkLogℂ iTermℂ) .one)).eval? env =
      some (Complex.exp a - a) := by
    have h := EMLTermℂ.eval?_eml_of_ne hA e_mlT_one hexp_a_ne
    rw [h]; congr 1
    rw [Complex.log_exp ha_im_lo ha_im_hi]
  -- exp a - a = Complex.I - (π/2)*Complex.I = (1 - π/2)*Complex.I, ≠ 0 since π/2 ≠ 1 (π > 3)
  have h_exp_a_minus_a : Complex.exp a - a = ((1 - Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
    rw [h_exp_a, ha_def]; push_cast; ring
  have h_exp_a_minus_a_ne : Complex.exp a - a ≠ 0 := by
    rw [h_exp_a_minus_a]
    have h_neg : (1 - Real.pi / 2 : ℝ) ≠ 0 := by
      intro h; linarith [Real.pi_gt_three]
    exact mul_ne_zero (by exact_mod_cast h_neg) Complex.I_ne_zero
  -- Step 6: eml(one, eml(mkLogℂ iTerm, eml(mkLogℂ iTerm, one))) = exp 1 - log(exp a - a)
  have e_one_etc1 : (EMLTermℂ.eml .one (.eml (mkLogℂ iTermℂ) (.eml (mkLogℂ iTermℂ) .one))).eval? env =
      some (Complex.exp 1 - Complex.log (Complex.exp a - a)) := by
    have h := EMLTermℂ.eval?_eml_of_ne (EMLTermℂ.eval?_one env) e_emlA_emlAone h_exp_a_minus_a_ne
    rw [h]
  -- Step 7: eml(eml(one, eml(mkLogℂ iTerm, eml(mkLogℂ iTerm, one))), one) = exp(exp 1 - log(exp a - a)) - log 1
  --       = exp(exp 1 - log(exp a - a))
  have e_step7 : (EMLTermℂ.eml (.eml .one (.eml (mkLogℂ iTermℂ) (.eml (mkLogℂ iTermℂ) .one))) .one).eval? env =
      some (Complex.exp (Complex.exp 1 - Complex.log (Complex.exp a - a))) := by
    have h := EMLTermℂ.eval?_eml_of_ne e_one_etc1 (EMLTermℂ.eval?_one env) one_ne_zero
    rw [h]; congr 1; rw [Complex.log_one, sub_zero]
  -- Compute log(exp a - a) = log((1-π/2)*Complex.I) = log(π/2 - 1) - iπ/2
  have h_log_exp_a_minus_a : Complex.log (Complex.exp a - a) =
      ((Real.log (Real.pi / 2 - 1) : ℝ) : ℂ) - (Real.pi / 2 : ℂ) * Complex.I := by
    rw [h_exp_a_minus_a]
    have heq : ((1 - Real.pi / 2 : ℝ) : ℂ) * Complex.I = ((Real.pi / 2 - 1 : ℝ) : ℂ) * (-Complex.I) := by
      push_cast; ring
    rw [heq]
    have h_pos : 0 < Real.pi / 2 - 1 := by linarith [Real.pi_gt_three]
    rw [Complex.log_ofReal_mul h_pos (by simpa using Complex.I_ne_zero),
        Complex.log_neg_I]
    push_cast; ring
  -- Step 8: eml(one, eml(eml(one, ...), one)) = exp 1 - log(exp(exp 1 - log(exp a - a)))
  -- The argument's im = (exp 1 - log(exp a - a)).im = -(log(exp a - a)).im = -(-(π/2)) = π/2 ∈ (-π, π]
  have h_log_im : (Complex.log (Complex.exp a - a)).im = -(Real.pi / 2) := by
    rw [h_log_exp_a_minus_a]
    simp [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.mul_re,
          Complex.I_re, Complex.I_im]
  have helogexpa_im : (Complex.exp 1 - Complex.log (Complex.exp a - a)).im = Real.pi / 2 := by
    rw [Complex.sub_im, h_log_im]
    have hexp1_im : (Complex.exp 1).im = 0 := by simp [Complex.exp_im]
    rw [hexp1_im]; ring
  have helogexpa_im_lo : -Real.pi < (Complex.exp 1 - Complex.log (Complex.exp a - a)).im := by
    rw [helogexpa_im]; linarith [Real.pi_pos]
  have helogexpa_im_hi : (Complex.exp 1 - Complex.log (Complex.exp a - a)).im ≤ Real.pi := by
    rw [helogexpa_im]; linarith [Real.pi_pos]
  have hexp_helogexpa_ne : Complex.exp (Complex.exp 1 - Complex.log (Complex.exp a - a)) ≠ 0 :=
    Complex.exp_ne_zero _
  have e_one_etc2 : (EMLTermℂ.eml .one (.eml (.eml .one (.eml (mkLogℂ iTermℂ) (.eml (mkLogℂ iTermℂ) .one))) .one)).eval? env =
      some (Complex.log (Complex.exp a - a)) := by
    have h := EMLTermℂ.eval?_eml_of_ne (EMLTermℂ.eval?_one env) e_step7 hexp_helogexpa_ne
    rw [h]; congr 1
    rw [Complex.log_exp helogexpa_im_lo helogexpa_im_hi]; ring
  -- Step 9: eml(B, one) where B = mkLogℂ var = (log x : ℂ).
  have e_B_one : (EMLTermℂ.eml (mkLogℂ (.var 0)) .one).eval? env = some (Complex.exp b) := by
    have h := EMLTermℂ.eval?_eml_of_ne hB (EMLTermℂ.eval?_one env) one_ne_zero
    rw [h]; congr 1; rw [Complex.log_one, sub_zero]
  -- Step 10: eml(eml(one, eml(eml(...), .one)), eml(B, one)) = exp(log(exp a - a)) - log(exp b)
  --        = (exp a - a) - b
  have hexp_b_ne : Complex.exp b ≠ 0 := Complex.exp_ne_zero _
  -- b.im = (log x : ℂ).im = 0 ∈ (-π, π]
  have hb_im : b.im = 0 := by rw [hb_def]; simp
  have hb_im_lo : -Real.pi < b.im := by rw [hb_im]; linarith [Real.pi_pos]
  have hb_im_hi : b.im ≤ Real.pi := by rw [hb_im]; linarith [Real.pi_pos]
  have e_step10 : (EMLTermℂ.eml (.eml .one (.eml (.eml .one (.eml (mkLogℂ iTermℂ) (.eml (mkLogℂ iTermℂ) .one))) .one))
                                (.eml (mkLogℂ (.var 0)) .one)).eval? env =
      some (Complex.exp a - a - b) := by
    have h := EMLTermℂ.eval?_eml_of_ne e_one_etc2 e_B_one hexp_b_ne
    rw [h]; congr 1
    rw [Complex.exp_log h_exp_a_minus_a_ne, Complex.log_exp hb_im_lo hb_im_hi]
  -- Step 11: rhs = eml((above), one) = exp(exp a - a - b) - log 1 = exp(exp a - a - b)
  have hexp_aab_ne : Complex.exp (Complex.exp a - a - b) ≠ 0 := Complex.exp_ne_zero _
  have e_rhs : (EMLTermℂ.eml
                  (.eml (.eml .one (.eml (.eml .one (.eml (mkLogℂ iTermℂ) (.eml (mkLogℂ iTermℂ) .one))) .one))
                        (.eml (mkLogℂ (.var 0)) .one))
                  .one).eval? env =
      some (Complex.exp (Complex.exp a - a - b)) := by
    have h := EMLTermℂ.eval?_eml_of_ne e_step10 (EMLTermℂ.eval?_one env) one_ne_zero
    rw [h]; congr 1; rw [Complex.log_one, sub_zero]
  -- Final: eml(lhs, rhs) = exp a - log(exp(exp a - a - b)) = exp a - (exp a - a - b) = a + b
  -- (exp a - a - b).im = (1 - π/2)*1 + 0 = 1 - π/2 ∈ (-π, π]
  have h_exp_a_minus_a_b_im : (Complex.exp a - a - b).im = 1 - Real.pi / 2 := by
    rw [Complex.sub_im, Complex.sub_im]
    rw [hb_im, sub_zero, h_exp_a, ha_im]
    rw [Complex.I_im]
  have h_aab_im_lo : -Real.pi < (Complex.exp a - a - b).im := by
    rw [h_exp_a_minus_a_b_im]; linarith [Real.pi_gt_three]
  have h_aab_im_hi : (Complex.exp a - a - b).im ≤ Real.pi := by
    rw [h_exp_a_minus_a_b_im]; linarith [Real.pi_gt_three]
  have h := EMLTermℂ.eval?_eml_of_ne e_lhs e_rhs hexp_aab_ne
  rw [h]; congr 1
  rw [Complex.log_exp h_aab_im_lo h_aab_im_hi]
  -- Goal: exp a - (exp a - a - b) = a + b
  ring

/-- Main lemma: when `env 0 = (x : ℝ)` for `x > 0`, `cosTermℂ` evaluates
to `Complex.exp (Complex.I * (x : ℂ))`. -/
private lemma eval?_cosTermℂ {env : Nat → ℂ} {x : ℝ}
    (hx : 0 < x) (hev : env 0 = ((x : ℝ) : ℂ)) :
    cosTermℂ.eval? env = some (Complex.exp (Complex.I * ((x : ℝ) : ℂ))) := by
  unfold cosTermℂ
  -- mkExpℂ (mkExpℂ (eml cosLhsℂ cosRhsℂ))
  have hInner := eval?_inner_add hx hev
  -- Apply inner mkExpℂ
  have hMid := eval?_mkExpℂ hInner
  -- exp((π/2)*Complex.I + log x) = x * Complex.I (= Complex.I * x)
  have h_mid_val : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I + ((Real.log x : ℝ) : ℂ)) = ((x : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_add]
    have h1 : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
      have h_eq : ((Real.pi / 2 : ℝ) : ℂ) * Complex.I = (Real.pi : ℂ) / 2 * Complex.I := by push_cast; ring
      rw [h_eq]; exact Complex.exp_pi_div_two_mul_I
    have h2 : Complex.exp ((Real.log x : ℝ) : ℂ) = ((x : ℝ) : ℂ) := by
      rw [exp_ofReal', Real.exp_log hx]
    rw [h1, h2]; ring
  rw [h_mid_val] at hMid
  -- Now apply outer mkExpℂ
  have h := eval?_mkExpℂ hMid
  rw [h]; congr 1
  -- exp(x * Complex.I) = exp(Complex.I * x)
  rw [mul_comm]

/-! ## Public closures -/

/-- Domain predicate for the cos witness: `env 0` is a positive real. -/
private def cosDomain (env : Nat → ℂ) : Prop :=
  ∃ x : ℝ, 0 < x ∧ env 0 = ((x : ℝ) : ℂ)

/--
**Literal complex EML witness** for `Complex.exp (Complex.I * env 0)` on the
domain where `env 0` is a positive real.

This is the witness produced by chunk 062 (`cosTerm`), ported to the
framework's `EMLTermℂ` grammar with partial `eval?` semantics. The
forward-only spec means: when `f env = some v` (i.e. `env 0` is a
positive real), the witness's `eval?` agrees and gives `exp(Complex.I * env 0)`.

The real part of `exp(Complex.I * x)` for real `x > 0` is `Real.cos x`, which
is captured by `cos_re_bridge` below.

We do NOT provide a literal complex witness for `Complex.cos`
itself: that would require the Euler decomposition
`(exp(iz) + exp(-iz)) / 2`, whose `+` and `/2` operators are not part
of the EML grammar at the complex/non-positivity-controlled level
(see file docstring).
-/
noncomputable def realizeℂ_exp_I_var :
    EMLRealizationℂ
      (fun env =>
        if h : ∃ x : ℝ, 0 < x ∧ env 0 = ((x : ℝ) : ℂ)
        then some (Complex.exp (Complex.I * env 0))
        else none) where
  term := cosTermℂ
  spec := fun env v hv => by
    -- Pull out `x` from the if-condition.
    by_cases h : ∃ x : ℝ, 0 < x ∧ env 0 = ((x : ℝ) : ℂ)
    · rw [dif_pos h] at hv
      obtain ⟨x, hx, hev⟩ := h
      have hcos := eval?_cosTermℂ hx hev
      rw [hcos]
      simp only [Option.some.injEq] at hv
      rw [← hv, hev]
    · rw [dif_neg h] at hv
      exact absurd hv (by simp)

/-- Bridge: when `env 0 = ((x : ℝ) : ℂ)` for `x > 0`, the real part of
the witness's evaluation equals `Real.cos x`. -/
theorem cos_re_bridge {env : Nat → ℂ} {x : ℝ} (hx : 0 < x)
    (hev : env 0 = ((x : ℝ) : ℂ)) :
    ∃ v : ℂ, cosTermℂ.eval? env = some v ∧ v.re = Real.cos x := by
  refine ⟨Complex.exp (Complex.I * ((x : ℝ) : ℂ)), eval?_cosTermℂ hx hev, ?_⟩
  -- exp(Complex.I * x).re = cos x
  rw [show (Complex.I * ((x : ℝ) : ℂ)) = ((x : ℝ) : ℂ) * Complex.I from by ring]
  rw [Complex.exp_re]
  simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.cos_ofReal_re,
        Complex.sin_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_im]

/-! ## Sin variant: `exp(Complex.I * (z - π/2))`, real part = sin x

Following chunk 063: `sinTermℂ := mkExpℂ (mkSubℂ (mkLogℂ cosTermℂ) (mkLogℂ iTermℂ))`.
This evaluates to `exp(log(exp(Ix)) - log(Complex.I)) = exp(Ix - Complex.Iπ/2)` whose real
part is `sin x` for `x ∈ (0, π)`.
-/

/-- The "sub" combinator: `eml(mkLogℂ A, mkExpℂ B)` evaluates to `A - B`
under appropriate conditions. -/
private def mkSubℂ_safe (A B : EMLTermℂ) : EMLTermℂ := .eml (mkLogℂ A) (mkExpℂ B)

private lemma eval?_mkSubℂ_safe
    {env : Nat → ℂ} {A B : EMLTermℂ} {va vb : ℂ}
    (hA : A.eval? env = some va) (hA_ne : va ≠ 0)
    (hA_arg : Complex.arg va < Real.pi)
    (hB : B.eval? env = some vb)
    (hB1 : -Real.pi < vb.im) (hB2 : vb.im ≤ Real.pi) :
    (mkSubℂ_safe A B).eval? env = some (va - vb) := by
  unfold mkSubℂ_safe
  have hLog := eval?_mkLogℂ hA hA_ne hA_arg
  have hExp := eval?_mkExpℂ hB
  have hExp_ne : Complex.exp vb ≠ 0 := Complex.exp_ne_zero _
  have h := EMLTermℂ.eval?_eml_of_ne hLog hExp hExp_ne
  rw [h]; congr 1
  rw [Complex.exp_log hA_ne, Complex.log_exp hB1 hB2]

/-- The sin witness term: `mkExpℂ (mkSubℂ_safe (mkLogℂ cosTermℂ) (mkLogℂ iTermℂ))`. -/
def sinTermℂ : EMLTermℂ :=
  mkExpℂ (mkSubℂ_safe (mkLogℂ cosTermℂ) (mkLogℂ iTermℂ))

/-- Main lemma: when `env 0 = (x : ℝ)` for `x ∈ (0, π)`, `sinTermℂ`
evaluates to `Complex.exp (Complex.I * ((x : ℂ) - π/2))`. -/
private lemma eval?_sinTermℂ {env : Nat → ℂ} {x : ℝ}
    (hx0 : 0 < x) (hxpi : x < Real.pi) (hev : env 0 = ((x : ℝ) : ℂ)) :
    sinTermℂ.eval? env =
      some (Complex.exp (((x : ℝ) : ℂ) * Complex.I - ((Real.pi / 2 : ℝ) : ℂ) * Complex.I)) := by
  unfold sinTermℂ
  -- cosTermℂ.eval? env = some (exp(Complex.I * x))
  have hcos : cosTermℂ.eval? env = some (Complex.exp (Complex.I * ((x : ℝ) : ℂ))) :=
    eval?_cosTermℂ hx0 hev
  -- exp(Complex.I*x) = exp(((x:ℝ):ℂ) * Complex.I) — rewrite for clarity
  have h_cos_eq : Complex.exp (Complex.I * ((x : ℝ) : ℂ)) = Complex.exp (((x : ℝ) : ℂ) * Complex.I) := by
    rw [mul_comm]
  rw [h_cos_eq] at hcos
  -- mkLogℂ cosTermℂ eval = log(exp(x*Complex.I)) = x*Complex.I, since (x*Complex.I).im = x ∈ (0,π) ⊂ (-π,π]
  have h_xI_im : (((x : ℝ) : ℂ) * Complex.I).im = x := by
    simp [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
  have h_xI_im_lo : -Real.pi < (((x : ℝ) : ℂ) * Complex.I).im := by rw [h_xI_im]; linarith [Real.pi_pos]
  have h_xI_im_hi : (((x : ℝ) : ℂ) * Complex.I).im ≤ Real.pi := by rw [h_xI_im]; linarith
  have h_log_cos_inner : Complex.log (Complex.exp (((x : ℝ) : ℂ) * Complex.I)) = ((x : ℝ) : ℂ) * Complex.I := by
    rw [Complex.log_exp h_xI_im_lo h_xI_im_hi]
  -- exp(x*Complex.I) ≠ 0
  have h_exp_xI_ne : Complex.exp (((x : ℝ) : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  -- arg(exp(x*Complex.I)) < π: arg(exp(x*Complex.I)) = x for x ∈ (-π, π], here x ∈ (0,π) so arg = x < π.
  have h_arg_cos : Complex.arg (Complex.exp (((x : ℝ) : ℂ) * Complex.I)) < Real.pi := by
    rw [Complex.arg_exp_mul_I]
    have htio : toIocMod Real.two_pi_pos (-Real.pi) x = x := by
      rw [toIocMod_eq_self Real.two_pi_pos]
      refine ⟨by linarith, ?_⟩
      have : -Real.pi + 2 * Real.pi = Real.pi := by ring
      rw [this]; linarith
    rw [htio]; exact hxpi
  have h_log_cos := eval?_mkLogℂ hcos h_exp_xI_ne h_arg_cos
  rw [h_log_cos_inner] at h_log_cos
  -- mkLogℂ iTermℂ evaluates to (π/2)*Complex.I
  have h_log_i := eval?_mkLogℂ_iTerm env
  -- (mkLogℂ cos).eval ≠ 0 and arg < π:
  have h_xI_ne : ((x : ℝ) : ℂ) * Complex.I ≠ 0 := by
    intro h
    have h_im := congrArg Complex.im h
    rw [h_xI_im] at h_im
    simp at h_im
    linarith
  -- arg((x:ℂ)*Complex.I) where x > 0
  have h_arg_xI : Complex.arg (((x : ℝ) : ℂ) * Complex.I) = Real.pi / 2 := by
    have h1 : Complex.arg (((x : ℝ) : ℂ) * Complex.I) = Complex.arg Complex.I :=
      Complex.arg_real_mul Complex.I hx0
    rw [h1, Complex.arg_I]
  have h_arg_xI_lt_pi : Complex.arg (((x : ℝ) : ℂ) * Complex.I) < Real.pi := by
    rw [h_arg_xI]; linarith [Real.pi_pos]
  -- (mkLogℂ iTerm).eval.im = ((π/2:ℝ):ℂ * Complex.I).im = π/2 ∈ (-π,π]
  have h_logi_im : (((Real.pi / 2 : ℝ) : ℂ) * Complex.I).im = Real.pi / 2 := by
    simp [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
  have h_logi_im_lo : -Real.pi < (((Real.pi / 2 : ℝ) : ℂ) * Complex.I).im := by
    rw [h_logi_im]; linarith [Real.pi_pos]
  have h_logi_im_hi : (((Real.pi / 2 : ℝ) : ℂ) * Complex.I).im ≤ Real.pi := by
    rw [h_logi_im]; linarith [Real.pi_pos]
  have h_sub := eval?_mkSubℂ_safe h_log_cos h_xI_ne h_arg_xI_lt_pi
                  h_log_i h_logi_im_lo h_logi_im_hi
  have h := eval?_mkExpℂ h_sub
  exact h

/-- Bridge for sin: when `env 0 = ((x : ℝ) : ℂ)` for `x ∈ (0, π)`, the
real part of `sinTermℂ.eval?` is `Real.sin x`. -/
theorem sin_re_bridge {env : Nat → ℂ} {x : ℝ}
    (hx0 : 0 < x) (hxpi : x < Real.pi) (hev : env 0 = ((x : ℝ) : ℂ)) :
    ∃ v : ℂ, sinTermℂ.eval? env = some v ∧ v.re = Real.sin x := by
  refine ⟨Complex.exp (((x : ℝ) : ℂ) * Complex.I - ((Real.pi / 2 : ℝ) : ℂ) * Complex.I),
          eval?_sinTermℂ hx0 hxpi hev, ?_⟩
  -- exp((x - π/2) * Complex.I).re = cos(x - π/2) = sin x
  have h_eq : (((x : ℝ) : ℂ) * Complex.I - ((Real.pi / 2 : ℝ) : ℂ) * Complex.I) =
      ((x - Real.pi/2 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h_eq, Complex.exp_re]
  have h_cos_sub : Real.cos (x - Real.pi / 2) = Real.sin x := by
    rw [Real.cos_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  -- Compute (((x - π/2 : ℝ) : ℂ) * Complex.I).re and .im, and use cos_ofReal/sin_ofReal
  have h_re : (((x - Real.pi/2 : ℝ) : ℂ) * Complex.I).re = 0 := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  have h_im : (((x - Real.pi/2 : ℝ) : ℂ) * Complex.I).im = (x - Real.pi/2) := by
    simp [Complex.mul_im, Complex.I_re, Complex.I_im]
  rw [h_re, h_im, Real.exp_zero, one_mul]
  exact h_cos_sub

/--
**Literal complex EML witness** for `Complex.exp (Complex.I * (env 0 - π/2))`
on the domain where `env 0` is a real in `(0, π)`.

This is the witness produced by chunk 063 (`sinTerm`), ported to the
framework's `EMLTermℂ` grammar. Its real part is `Real.sin x` (see
`sin_re_bridge`).

As with `realizeℂ_exp_I_var`, this is **not** a literal `Complex.sin`
witness — that would require the Euler decomposition
`(exp(iz) - exp(-iz)) / (2Complex.I)`. We deliver the analogue scope of the
source chunk: the Euler-shifted exponential plus a real-part bridge.
-/
noncomputable def realizeℂ_exp_I_sub_pi2 :
    EMLRealizationℂ
      (fun env =>
        if h : ∃ x : ℝ, 0 < x ∧ x < Real.pi ∧ env 0 = ((x : ℝ) : ℂ)
        then some (Complex.exp (((env 0).re : ℂ) * Complex.I -
                                ((Real.pi / 2 : ℝ) : ℂ) * Complex.I))
        else none) where
  term := sinTermℂ
  spec := fun env v hv => by
    by_cases h : ∃ x : ℝ, 0 < x ∧ x < Real.pi ∧ env 0 = ((x : ℝ) : ℂ)
    · rw [dif_pos h] at hv
      obtain ⟨x, hx0, hxpi, hev⟩ := h
      have hsin := eval?_sinTermℂ hx0 hxpi hev
      rw [hsin]
      simp only [Option.some.injEq] at hv
      rw [← hv]
      -- env 0 = (x : ℂ), so (env 0).re = x, hence ((env 0).re : ℂ) = (x : ℂ)
      have : ((env 0).re : ℂ) = ((x : ℝ) : ℂ) := by
        rw [hev]; simp
      rw [this]
    · rw [dif_neg h] at hv
      exact absurd hv (by simp)

end EML
