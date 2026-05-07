import EML.Framework.Complex.Closures.Trig
import EML.Framework.Complex.Closures.Constants
import EML.Framework.Complex.RealLift
import EML.Framework.Compilers.ELToEML
import Mathlib

/-!
# Trig builders — `mkAddℂ`, `mkMulℂ`, `mkDivℂ`, plus literal `arctan` witness

Phase B++ II §A. Adds the combinators needed to seal `arctan` (chunk 065)
as a literal `EMLTermℂ` witness — currently 065 only provides the
mathematical identity. Once these compile, chunks 064/066/067 are
mechanical replays.

## Bootstrap target

`Real.arctan x = (Complex.log (1 + (x : ℂ) * I)).im` (already proven in
chunk 065). The witness is

```
arctanTermℂ := mkLogℂ (mkAddℂ one (mkMulℂ iTermℂ (var 0)))
```

with the bridge `(arctanTermℂ.eval? env).im = Real.arctan x` when `env 0 = (x:ℝ)`.

## What's new vs. `Complex/Closures/Trig.lean`

That file builds the cos/sin witnesses by **inlining** the add pattern.
We expose `mkAddℂ` (and derived `mkMulℂ`, `mkDivℂ`) as public combinators,
threading the same chunk-062 ADDsafe-style precondition bundle through
`eval?` rather than total `eval`.
-/

namespace EML

open Complex

/-! ## ADDsafe bundle (forward-only on `eval?`) -/

/-- Precondition bundle for `mkAddℂ`. Mirrors chunk 062's `ADDsafe` but
applies to the `eval?`-level values. -/
structure ADDsafeℂ (a b : ℂ) : Prop where
  ha₁ : -Real.pi < a.im
  ha₂ : a.im ≤ Real.pi
  hema₁ : -Real.pi < (Complex.exp 1 - a).im
  hema₂ : (Complex.exp 1 - a).im ≤ Real.pi
  hexpa_a_ne : Complex.exp a - a ≠ 0
  hb₁ : -Real.pi < b.im
  hb₂ : b.im ≤ Real.pi
  helogexpa₁ :
    -Real.pi < (Complex.exp 1 - Complex.log (Complex.exp a - a)).im
  helogexpa₂ :
    (Complex.exp 1 - Complex.log (Complex.exp a - a)).im ≤ Real.pi
  hexp_a_a_b₁ : -Real.pi < (Complex.exp a - a - b).im
  hexp_a_a_b₂ : (Complex.exp a - a - b).im ≤ Real.pi

/-- The `mkAddℂ` term shape (chunk-062 pattern, lifted into `EMLTermℂ`). -/
def mkAddℂ (A B : EMLTermℂ) : EMLTermℂ :=
  .eml
    (.eml .one (.eml (.eml .one (.eml A .one)) .one))
    (.eml
      (.eml (.eml .one (.eml (.eml .one (.eml A (.eml A .one))) .one))
            (.eml B .one))
      .one)

/-- Closure: under `ADDsafeℂ`, `mkAddℂ A B` evaluates to `va + vb`. -/
lemma eval?_mkAddℂ {env : Nat → ℂ} {A B : EMLTermℂ} {va vb : ℂ}
    (hA : A.eval? env = some va) (hB : B.eval? env = some vb)
    (H : ADDsafeℂ va vb) :
    (mkAddℂ A B).eval? env = some (va + vb) := by
  -- Build the inner sub-evaluations one by one. Mirrors chunk 062 line-by-line
  -- but threading `eval?` and `EMLTermℂ.eval?_eml_of_ne` instead of total eval.
  have h_A_one : (EMLTermℂ.eml A .one).eval? env = some (Complex.exp va) := by
    have h := EMLTermℂ.eval?_eml_of_ne hA (EMLTermℂ.eval?_one env) one_ne_zero
    rw [Complex.log_one, sub_zero] at h
    exact h
  have h_one_eA1 :
      (EMLTermℂ.eml .one (.eml A .one)).eval? env =
        some (Complex.exp 1 - va) := by
    have h := EMLTermℂ.eval?_eml_of_ne (EMLTermℂ.eval?_one env) h_A_one
      (Complex.exp_ne_zero _)
    rw [Complex.log_exp H.ha₁ H.ha₂] at h
    exact h
  have h_eA_one_top :
      (EMLTermℂ.eml (.eml .one (.eml A .one)) .one).eval? env =
        some (Complex.exp (Complex.exp 1 - va)) := by
    have h := EMLTermℂ.eval?_eml_of_ne h_one_eA1 (EMLTermℂ.eval?_one env) one_ne_zero
    rw [Complex.log_one, sub_zero] at h
    exact h
  have h_LHS :
      (EMLTermℂ.eml .one (.eml (.eml .one (.eml A .one)) .one)).eval? env =
        some va := by
    have h := EMLTermℂ.eval?_eml_of_ne (EMLTermℂ.eval?_one env) h_eA_one_top
      (Complex.exp_ne_zero _)
    rw [Complex.log_exp H.hema₁ H.hema₂] at h
    convert h using 2
    ring
  -- inner: A (A 1) = exp a - log(exp a) = exp a - a
  have h_A_AA1 :
      (EMLTermℂ.eml A (.eml A .one)).eval? env =
        some (Complex.exp va - va) := by
    have h := EMLTermℂ.eval?_eml_of_ne hA h_A_one (Complex.exp_ne_zero _)
    rw [Complex.log_exp H.ha₁ H.ha₂] at h
    exact h
  -- 1 (A (A 1)) = exp 1 - log(exp a - a)
  have h_1_AA1 :
      (EMLTermℂ.eml .one (.eml A (.eml A .one))).eval? env =
        some (Complex.exp 1 - Complex.log (Complex.exp va - va)) := by
    exact EMLTermℂ.eval?_eml_of_ne (EMLTermℂ.eval?_one env) h_A_AA1
      H.hexpa_a_ne
  -- (1 (A (A 1))) 1 = exp(exp 1 - log(exp a - a)) - log 1
  have h_1AA1_1 :
      (EMLTermℂ.eml (.eml .one (.eml A (.eml A .one))) .one).eval? env =
        some (Complex.exp (Complex.exp 1 - Complex.log (Complex.exp va - va))) := by
    have h := EMLTermℂ.eval?_eml_of_ne h_1_AA1 (EMLTermℂ.eval?_one env) one_ne_zero
    rw [Complex.log_one, sub_zero] at h
    exact h
  -- 1 ((1 (A (A 1))) 1) = exp 1 - log(exp(...)) = log(exp a - a)
  have h_1_1AA1_1 :
      (EMLTermℂ.eml .one (.eml (.eml .one (.eml A (.eml A .one))) .one)).eval? env =
        some (Complex.log (Complex.exp va - va)) := by
    have h := EMLTermℂ.eval?_eml_of_ne (EMLTermℂ.eval?_one env) h_1AA1_1
      (Complex.exp_ne_zero _)
    rw [Complex.log_exp H.helogexpa₁ H.helogexpa₂] at h
    convert h using 2
    ring
  -- B 1 = exp b - log 1 = exp b
  have h_B_one : (EMLTermℂ.eml B .one).eval? env = some (Complex.exp vb) := by
    have h := EMLTermℂ.eval?_eml_of_ne hB (EMLTermℂ.eval?_one env) one_ne_zero
    rw [Complex.log_one, sub_zero] at h
    exact h
  -- (1 ((1 (A (A 1))) 1)) (B 1) = log(exp a - a) - log(exp b) = log(exp a - a) - b
  have h_inner_RHS :
      (EMLTermℂ.eml
        (.eml .one (.eml (.eml .one (.eml A (.eml A .one))) .one))
        (.eml B .one)).eval? env =
        some (Complex.exp va - va - vb) := by
    have h := EMLTermℂ.eval?_eml_of_ne h_1_1AA1_1 h_B_one (Complex.exp_ne_zero _)
    rw [Complex.exp_log H.hexpa_a_ne, Complex.log_exp H.hb₁ H.hb₂] at h
    exact h
  -- ((... ) 1) = exp(exp a - a - b) - log 1 = exp(exp a - a - b)
  have h_inner_RHS_1 :
      (EMLTermℂ.eml
        (.eml
          (.eml .one (.eml (.eml .one (.eml A (.eml A .one))) .one))
          (.eml B .one)) .one).eval? env =
        some (Complex.exp (Complex.exp va - va - vb)) := by
    have h := EMLTermℂ.eval?_eml_of_ne h_inner_RHS (EMLTermℂ.eval?_one env) one_ne_zero
    rw [Complex.log_one, sub_zero] at h
    exact h
  -- final: LHS - log(... ) = a - log(exp(exp a - a - b)) = a - (exp a - a - b) = b + (2a - exp a)
  -- Wait, let's compute exactly: exp 1 - log(exp X) where LHS = a, X = exp a - a - b.
  -- That gives a - X = a - (exp a - a - b) = 2a - exp a + b.
  -- That's not a + b. Let me re-trace chunk 062's final step.
  unfold mkAddℂ
  have h := EMLTermℂ.eval?_eml_of_ne h_LHS h_inner_RHS_1 (Complex.exp_ne_zero _)
  rw [Complex.log_exp H.hexp_a_a_b₁ H.hexp_a_a_b₂] at h
  -- h : ... = some (exp(va) - (exp va - va - vb))
  -- Want: some (va + vb)
  convert h using 2
  ring

/-! ## Multiplication via log-sum -/

/-- `mkMulℂ A B := mkExpℂ (mkAddℂ (mkLogℂ A) (mkLogℂ B))`. -/
def mkMulℂ (A B : EMLTermℂ) : EMLTermℂ :=
  mkExpℂ (mkAddℂ (mkLogℂ A) (mkLogℂ B))

/-- Closure: `mkMulℂ A B` evaluates to `va * vb` under the bundle of
log-sum branch-cut hypotheses. -/
lemma eval?_mkMulℂ {env : Nat → ℂ} {A B : EMLTermℂ} {va vb : ℂ}
    (hA : A.eval? env = some va) (hB : B.eval? env = some vb)
    (hva_ne : va ≠ 0) (hvb_ne : vb ≠ 0)
    (h_arg_a : Complex.arg va < Real.pi)
    (h_arg_b : Complex.arg vb < Real.pi)
    (Hadd : ADDsafeℂ (Complex.log va) (Complex.log vb)) :
    (mkMulℂ A B).eval? env = some (va * vb) := by
  unfold mkMulℂ
  have hLa : (mkLogℂ A).eval? env = some (Complex.log va) :=
    eval?_mkLogℂ hA hva_ne h_arg_a
  have hLb : (mkLogℂ B).eval? env = some (Complex.log vb) :=
    eval?_mkLogℂ hB hvb_ne h_arg_b
  have hAdd : (mkAddℂ (mkLogℂ A) (mkLogℂ B)).eval? env =
      some (Complex.log va + Complex.log vb) := eval?_mkAddℂ hLa hLb Hadd
  have hExp : (mkExpℂ (mkAddℂ (mkLogℂ A) (mkLogℂ B))).eval? env =
      some (Complex.exp (Complex.log va + Complex.log vb)) := eval?_mkExpℂ hAdd
  -- exp(log va + log vb) = exp(log va) * exp(log vb) = va * vb
  rw [Complex.exp_add, Complex.exp_log hva_ne, Complex.exp_log hvb_ne] at hExp
  exact hExp

/-! ## Public `iTermℂ` re-export via the framework realization -/

/-- A public `EMLTermℂ` that always evaluates to `Complex.I`. Built from
`EML.EMLRealizationℂ.realizeℂ_i`. -/
noncomputable def iTermPubℂ : EMLTermℂ := EMLRealizationℂ.realizeℂ_i.term

lemma eval?_iTermPubℂ (env : Nat → ℂ) : iTermPubℂ.eval? env = some Complex.I :=
  EMLRealizationℂ.realizeℂ_i.spec env _ rfl

/-- Public `EMLTermℂ` for `0 : ℂ`. -/
noncomputable def zeroPubℂ : EMLTermℂ := EMLRealizationℂ.realizeℂ_zero.term

lemma eval?_zeroPubℂ (env : Nat → ℂ) : zeroPubℂ.eval? env = some (0 : ℂ) :=
  EMLRealizationℂ.realizeℂ_zero.spec env _ rfl

/-- Public `EMLTermℂ` for `2 : ℂ`. -/
noncomputable def twoPubℂ : EMLTermℂ := EMLRealizationℂ.realizeℂ_two.term

lemma eval?_twoPubℂ (env : Nat → ℂ) : twoPubℂ.eval? env = some (2 : ℂ) :=
  EMLRealizationℂ.realizeℂ_two.spec env _ rfl

/-- Public `EMLTermℂ` for `-Complex.I`. -/
noncomputable def negIPubℂ : EMLTermℂ := EMLRealizationℂ.realizeℂ_negI.term

lemma eval?_negIPubℂ (env : Nat → ℂ) : negIPubℂ.eval? env = some (-Complex.I) :=
  EMLRealizationℂ.realizeℂ_negI.spec env _ rfl

/-- Public `EMLTermℂ` for `(Real.pi : ℂ)`. -/
noncomputable def piPubℂ : EMLTermℂ := EMLRealizationℂ.realizeℂ_pi.term

lemma eval?_piPubℂ (env : Nat → ℂ) : piPubℂ.eval? env = some (Real.pi : ℂ) :=
  EMLRealizationℂ.realizeℂ_pi.spec env _ rfl

/-! ## Subtraction combinator -/

/-- Subtraction term: `mkSubℂ A B := eml(Lg A, ExpT B) = exp(log A) - log(exp B) = A - B`
under the conditions:
* `A.eval ≠ 0` and `arg(A.eval) < π` so `Lg A` returns `log A`,
* `(log A).im ∈ (-π, π]`,
* `B.eval` has `im ∈ (-π, π]` so `log(exp B) = B`.

In its bare form `eml(Lg A, ExpT B)` this evaluates to `exp(log A) − log(exp B)`,
which simplifies under the above to `A − B`. -/
def mkSubℂ (A B : EMLTermℂ) : EMLTermℂ := .eml (mkLogℂ A) (mkExpℂ B)

lemma eval?_mkSubℂ {env : Nat → ℂ} {A B : EMLTermℂ} {va vb : ℂ}
    (hA : A.eval? env = some va) (hB : B.eval? env = some vb)
    (hva_ne : va ≠ 0) (hva_arg : Complex.arg va < Real.pi)
    (hvb_im_lo : -Real.pi < vb.im) (hvb_im_hi : vb.im ≤ Real.pi) :
    (mkSubℂ A B).eval? env = some (va - vb) := by
  unfold mkSubℂ
  have hLogA : (mkLogℂ A).eval? env = some (Complex.log va) :=
    eval?_mkLogℂ hA hva_ne hva_arg
  have hExpB : (mkExpℂ B).eval? env = some (Complex.exp vb) := eval?_mkExpℂ hB
  have h := EMLTermℂ.eval?_eml_of_ne hLogA hExpB (Complex.exp_ne_zero _)
  rw [Complex.exp_log hva_ne, Complex.log_exp hvb_im_lo hvb_im_hi] at h
  exact h

/-! ## Division via log-difference -/

/-- `mkDivℂ A B := mkExpℂ (mkSubℂ (mkLogℂ A) (mkLogℂ B))`.

Evaluates to `va / vb` under the conditions:
* `va, vb ≠ 0`,
* `arg(va), arg(vb) < π` (logs valid),
* `arg((log va) - (log vb)) < π` (the inner `mkSubℂ`'s `Lg`),
* `(log vb).im ∈ (-π, π]` (the inner `mkSubℂ`'s `B` precondition). -/
def mkDivℂ (A B : EMLTermℂ) : EMLTermℂ :=
  mkExpℂ (mkSubℂ (mkLogℂ A) (mkLogℂ B))

lemma eval?_mkDivℂ {env : Nat → ℂ} {A B : EMLTermℂ} {va vb : ℂ}
    (hA : A.eval? env = some va) (hB : B.eval? env = some vb)
    (hva_ne : va ≠ 0) (hvb_ne : vb ≠ 0)
    (hva_arg : Complex.arg va < Real.pi) (hvb_arg : Complex.arg vb < Real.pi)
    (h_logA_ne : Complex.log va ≠ 0)
    (h_logA_arg : Complex.arg (Complex.log va) < Real.pi)
    (h_logB_im_lo : -Real.pi < (Complex.log vb).im)
    (h_logB_im_hi : (Complex.log vb).im ≤ Real.pi) :
    (mkDivℂ A B).eval? env = some (va / vb) := by
  unfold mkDivℂ
  have hLogA : (mkLogℂ A).eval? env = some (Complex.log va) :=
    eval?_mkLogℂ hA hva_ne hva_arg
  have hLogB : (mkLogℂ B).eval? env = some (Complex.log vb) :=
    eval?_mkLogℂ hB hvb_ne hvb_arg
  have hSub : (mkSubℂ (mkLogℂ A) (mkLogℂ B)).eval? env =
      some (Complex.log va - Complex.log vb) :=
    eval?_mkSubℂ hLogA hLogB h_logA_ne h_logA_arg h_logB_im_lo h_logB_im_hi
  have hExp : (mkExpℂ (mkSubℂ (mkLogℂ A) (mkLogℂ B))).eval? env =
      some (Complex.exp (Complex.log va - Complex.log vb)) := eval?_mkExpℂ hSub
  -- exp(log va - log vb) = exp(log va) / exp(log vb) = va / vb
  rw [show Complex.log va - Complex.log vb = Complex.log va + (-Complex.log vb) from by ring,
      Complex.exp_add, Complex.exp_neg, Complex.exp_log hva_ne, Complex.exp_log hvb_ne,
      ← div_eq_mul_inv] at hExp
  exact hExp

/-! ## §A.4 — literal `EMLTermℂ` witness for `Real.arctan` (narrowed)

The witness term itself is well-defined: `1 + ix` lifted into the
EML grammar via `mkAddℂ` and `mkMulℂ`, with `mkLogℂ` taking the
final logarithm. The closed-form identity
`Real.arctan x = (Complex.log (1 + ix)).im` (chunk 065) gives the
bridge from witness to paper claim.

The eval lemma proving `arctanTermℂ.eval? env = some (Complex.log (1 + ix))`
requires discharging the `ADDsafeℂ` bundle for two distinct argument
pairs (one for `mkMulℂ`, one for `mkAddℂ`). Each bundle expands into
~11 imaginary-part bound and arg-side conditions. The full proof is
estimated at ~400 lines of side-condition discharge plus arg-helper
lemmas (`Complex.arg_neg_imag`, `Complex.arg_ofReal_of_pos`, etc.).

**Status:** scaffolding sealed; eval-level seal of `arctanTermℂ` is
deferred to a follow-up commit. -/

/-- The narrowed-arctan witness term. -/
noncomputable def arctanTermℂ : EMLTermℂ :=
  mkLogℂ (mkAddℂ .one (mkMulℂ iTermPubℂ (.var 0)))

/-! ### Arg helpers for ADDsafeℂ on negative imaginary axis -/

/-- For `z` purely on the negative imaginary axis (re = 0, im < 0),
`Complex.arg z = -π/2`. -/
private lemma arg_eq_neg_pi_div_two_of_neg_imag {z : ℂ}
    (hre : z.re = 0) (him : z.im < 0) :
    Complex.arg z = -(Real.pi / 2) :=
  Complex.arg_eq_neg_pi_div_two_iff.mpr ⟨hre, him⟩

/-- And the imaginary part of `Complex.log` on the negative imag axis
is exactly `-π/2`. -/
private lemma im_log_eq_neg_pi_div_two {z : ℂ}
    (hre : z.re = 0) (him : z.im < 0) :
    (Complex.log z).im = -(Real.pi / 2) := by
  rw [Complex.log_im]
  exact arg_eq_neg_pi_div_two_of_neg_imag hre him

/-! ### ADDsafeℂ helpers -/

/-- For any real `r`, `Real.exp r - r > 0`. -/
private lemma exp_sub_self_pos_real (r : ℝ) :
    0 < Real.exp r - r := by
  have h := Real.add_one_le_exp r
  linarith

/-- For real `r`, `(Complex.exp ((r : ℝ) : ℂ) - ((r : ℝ) : ℂ))` is the
real-cast of `Real.exp r - r`. -/
private lemma exp_sub_self_ofReal (r : ℝ) :
    Complex.exp ((r : ℝ) : ℂ) - ((r : ℝ) : ℂ) = ((Real.exp r - r : ℝ) : ℂ) := by
  rw [← Complex.ofReal_exp]
  push_cast
  ring

/-- For real `r`, `Complex.log (Complex.exp r - r)` has imaginary part 0
(it's a positive real). -/
private lemma im_log_exp_sub_self_ofReal (r : ℝ) :
    (Complex.log (Complex.exp ((r : ℝ) : ℂ) - ((r : ℝ) : ℂ))).im = 0 := by
  rw [exp_sub_self_ofReal r,
      ← Complex.ofReal_log (exp_sub_self_pos_real r).le]
  simp

/-- Generic ADDsafeℂ when the left argument is the real-cast of `r`. -/
private lemma addsafe_ofReal_left {r : ℝ} {b : ℂ}
    (hb₁ : -Real.pi < b.im) (hb₂ : b.im ≤ Real.pi)
    (hnb₁ : -Real.pi < -b.im) (hnb₂ : -b.im ≤ Real.pi) :
    ADDsafeℂ ((r : ℝ) : ℂ) b := by
  have h_r_im : (((r : ℝ) : ℂ)).im = 0 := Complex.ofReal_im r
  have h_r_re : (((r : ℝ) : ℂ)).re = r := Complex.ofReal_re r
  have h_exp_r : Complex.exp ((r : ℝ) : ℂ) = ((Real.exp r : ℝ) : ℂ) :=
    (Complex.ofReal_exp r).symm
  have h_exp_r_im : (Complex.exp ((r : ℝ) : ℂ)).im = 0 := by
    rw [h_exp_r]; exact Complex.ofReal_im _
  have h_exp_r_re : (Complex.exp ((r : ℝ) : ℂ)).re = Real.exp r := by
    rw [h_exp_r]; exact Complex.ofReal_re _
  have h_exp_one_im : (Complex.exp 1 : ℂ).im = 0 := by
    show (Complex.exp ((1 : ℝ) : ℂ)).im = 0
    rw [← Complex.ofReal_exp]; exact Complex.ofReal_im _
  have h_exp_sub_ne :
      Complex.exp ((r : ℝ) : ℂ) - ((r : ℝ) : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    rw [Complex.sub_re, h_exp_r_re, h_r_re] at hr
    simp at hr
    have hpos := exp_sub_self_pos_real r
    linarith
  refine {
    ha₁ := ?_, ha₂ := ?_,
    hema₁ := ?_, hema₂ := ?_,
    hexpa_a_ne := h_exp_sub_ne,
    hb₁ := hb₁, hb₂ := hb₂,
    helogexpa₁ := ?_, helogexpa₂ := ?_,
    hexp_a_a_b₁ := ?_, hexp_a_a_b₂ := ?_ }
  · rw [h_r_im]; linarith [Real.pi_pos]
  · rw [h_r_im]; linarith [Real.pi_pos]
  · rw [Complex.sub_im, h_exp_one_im, h_r_im]; linarith [Real.pi_pos]
  · rw [Complex.sub_im, h_exp_one_im, h_r_im]; linarith [Real.pi_pos]
  · rw [Complex.sub_im, h_exp_one_im, im_log_exp_sub_self_ofReal r]
    simp; linarith [Real.pi_pos]
  · rw [Complex.sub_im, h_exp_one_im, im_log_exp_sub_self_ofReal r]
    simp; linarith [Real.pi_pos]
  · rw [Complex.sub_im, Complex.sub_im, h_exp_r_im, h_r_im]
    simpa using hnb₁
  · rw [Complex.sub_im, Complex.sub_im, h_exp_r_im, h_r_im]
    simpa using hnb₂

/-- ADDsafeℂ holds for `(log I, log (x : ℂ))` whenever `x > 0`. -/
private lemma addsafe_logI_logX {x : ℝ} (hx : 0 < x) :
    ADDsafeℂ (Complex.log Complex.I) (Complex.log ((x : ℝ) : ℂ)) := by
  -- log I = (π/2) · I (via Complex.log_I)
  have hlogI : Complex.log Complex.I = Real.pi / 2 * Complex.I :=
    Complex.log_I
  have h_logI_im : (Complex.log Complex.I).im = Real.pi / 2 := by
    rw [hlogI]; simp
  have h_logI_re : (Complex.log Complex.I).re = 0 := by
    rw [hlogI]; simp
  -- log (x : ℂ) is real
  have hlogX : Complex.log ((x : ℝ) : ℂ) = ((Real.log x : ℝ) : ℂ) :=
    (Complex.ofReal_log hx.le).symm
  have h_logX_im : (Complex.log ((x : ℝ) : ℂ)).im = 0 := by
    rw [hlogX]; simp
  -- exp(log I) = I
  have h_exp_logI : Complex.exp (Complex.log Complex.I) = Complex.I :=
    Complex.exp_log Complex.I_ne_zero
  -- The "exp(a) - a" value: I - log I = I - iπ/2 = i(1 - π/2)
  set w : ℂ := Complex.exp (Complex.log Complex.I) - Complex.log Complex.I with hw_def
  have hw_re : w.re = 0 := by
    show (Complex.exp (Complex.log Complex.I) - Complex.log Complex.I).re = 0
    rw [Complex.sub_re, h_exp_logI]
    simp [h_logI_re]
  have hw_im : w.im = 1 - Real.pi / 2 := by
    show (Complex.exp (Complex.log Complex.I) - Complex.log Complex.I).im = 1 - Real.pi / 2
    rw [Complex.sub_im, h_exp_logI, h_logI_im]
    simp
  have hw_im_neg : w.im < 0 := by
    rw [hw_im]; linarith [Real.pi_gt_three]
  have hw_ne : w ≠ 0 := by
    intro h; have := congrArg Complex.im h
    rw [hw_im] at this; simp at this
    linarith [Real.pi_gt_three]
  -- log w on negative imaginary axis has .im = -π/2
  have h_log_w_im : (Complex.log w).im = -(Real.pi / 2) :=
    im_log_eq_neg_pi_div_two hw_re hw_im_neg
  -- Now build the bundle
  refine {
    ha₁ := ?_, ha₂ := ?_,
    hema₁ := ?_, hema₂ := ?_,
    hexpa_a_ne := hw_ne,
    hb₁ := ?_, hb₂ := ?_,
    helogexpa₁ := ?_, helogexpa₂ := ?_,
    hexp_a_a_b₁ := ?_, hexp_a_a_b₂ := ?_ }
  · rw [h_logI_im]; linarith [Real.pi_pos]
  · rw [h_logI_im]; linarith [Real.pi_pos]
  · -- (e - log I).im = 0 - π/2 = -π/2
    show -Real.pi < (Complex.exp 1 - Complex.log Complex.I).im
    rw [Complex.sub_im]
    simp only [Complex.exp_im, Complex.one_im, Complex.one_re,
      Real.sin_zero, mul_zero, zero_sub, h_logI_im]
    linarith [Real.pi_pos]
  · show (Complex.exp 1 - Complex.log Complex.I).im ≤ Real.pi
    rw [Complex.sub_im]
    simp only [Complex.exp_im, Complex.one_im, Complex.one_re,
      Real.sin_zero, mul_zero, zero_sub, h_logI_im]
    linarith [Real.pi_pos]
  · rw [h_logX_im]; linarith [Real.pi_pos]
  · rw [h_logX_im]; linarith [Real.pi_pos]
  · -- (e - log w).im = 0 - (-π/2) = π/2
    show -Real.pi < (Complex.exp 1 - Complex.log w).im
    rw [Complex.sub_im]
    simp only [Complex.exp_im, Complex.one_im, Complex.one_re,
      Real.sin_zero, mul_zero, zero_sub, h_log_w_im]
    linarith [Real.pi_pos]
  · show (Complex.exp 1 - Complex.log w).im ≤ Real.pi
    rw [Complex.sub_im]
    simp only [Complex.exp_im, Complex.one_im, Complex.one_re,
      Real.sin_zero, mul_zero, zero_sub, h_log_w_im]
    linarith [Real.pi_pos]
  · -- (w - log x).im = 1 - π/2 - 0 = 1 - π/2
    show -Real.pi < (w - Complex.log ((x : ℝ) : ℂ)).im
    rw [Complex.sub_im, hw_im, h_logX_im]
    linarith [Real.pi_gt_three]
  · show (w - Complex.log ((x : ℝ) : ℂ)).im ≤ Real.pi
    rw [Complex.sub_im, hw_im, h_logX_im]
    linarith [Real.pi_gt_three]

/-- ADDsafeℂ holds for `(1, I * x)` whenever `0 < x < π`. -/
private lemma addsafe_one_iX {x : ℝ} (hx_pos : 0 < x) (hx_lt : x < Real.pi) :
    ADDsafeℂ (1 : ℂ) (Complex.I * ((x : ℝ) : ℂ)) := by
  -- (Complex.I * (x : ℂ)).im = x
  have h_iX_im : (Complex.I * ((x : ℝ) : ℂ)).im = x := by
    simp [Complex.mul_im, Complex.I_re, Complex.I_im]
  have h_iX_re : (Complex.I * ((x : ℝ) : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  -- exp(1) - 1: real
  have h_exp_one_im : (Complex.exp 1 : ℂ).im = 0 := by
    simp [Complex.exp_im, Complex.one_im, Complex.one_re]
  have h_exp_one_re : (Complex.exp 1 : ℂ).re = Real.exp 1 := by
    simp [Complex.exp_re, Complex.one_im, Complex.one_re]
  have h_e_minus_1_pos : 0 < Real.exp 1 - 1 := by
    have := Real.exp_pos 1
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  -- exp(1) - 1 = ((Real.exp 1 - 1) : ℂ) (purely real)
  have h_exp_one_sub_one_re : (Complex.exp 1 - 1 : ℂ).re = Real.exp 1 - 1 := by
    rw [Complex.sub_re]; simp [h_exp_one_re]
  have h_exp_one_sub_one_im : (Complex.exp 1 - 1 : ℂ).im = 0 := by
    rw [Complex.sub_im]; simp [h_exp_one_im]
  have h_exp_one_sub_one_ne : (Complex.exp 1 - 1 : ℂ) ≠ 0 := by
    intro h
    have h_re := congrArg Complex.re h
    rw [h_exp_one_sub_one_re] at h_re
    simp at h_re
    linarith
  -- log(e - 1): purely real (since e - 1 > 0 is real)
  have h_log_em1_im : (Complex.log (Complex.exp 1 - 1)).im = 0 := by
    rw [Complex.log_im]
    -- arg of positive real = 0
    apply Complex.arg_eq_zero_iff.mpr
    refine ⟨?_, ?_⟩
    · rw [h_exp_one_sub_one_re]; linarith
    · rw [h_exp_one_sub_one_im]
  -- Build the bundle
  refine {
    ha₁ := ?_, ha₂ := ?_,
    hema₁ := ?_, hema₂ := ?_,
    hexpa_a_ne := h_exp_one_sub_one_ne,
    hb₁ := ?_, hb₂ := ?_,
    helogexpa₁ := ?_, helogexpa₂ := ?_,
    hexp_a_a_b₁ := ?_, hexp_a_a_b₂ := ?_ }
  · simp; linarith [Real.pi_pos]
  · simp; linarith [Real.pi_pos]
  · -- (e - 1).im = 0
    show -Real.pi < (Complex.exp 1 - (1 : ℂ)).im
    rw [h_exp_one_sub_one_im]; linarith [Real.pi_pos]
  · show (Complex.exp 1 - (1 : ℂ)).im ≤ Real.pi
    rw [h_exp_one_sub_one_im]; linarith [Real.pi_pos]
  · rw [h_iX_im]; linarith
  · rw [h_iX_im]; linarith
  · -- (e - log(e-1)).im = 0
    show -Real.pi < (Complex.exp 1 - Complex.log (Complex.exp 1 - 1)).im
    rw [Complex.sub_im, h_exp_one_im, h_log_em1_im]
    linarith [Real.pi_pos]
  · show (Complex.exp 1 - Complex.log (Complex.exp 1 - 1)).im ≤ Real.pi
    rw [Complex.sub_im, h_exp_one_im, h_log_em1_im]
    linarith [Real.pi_pos]
  · -- (e - 1 - i·x).im = 0 - x = -x
    show -Real.pi < (Complex.exp 1 - 1 - Complex.I * ((x : ℝ) : ℂ)).im
    rw [Complex.sub_im, h_exp_one_sub_one_im, h_iX_im]
    linarith
  · show (Complex.exp 1 - 1 - Complex.I * ((x : ℝ) : ℂ)).im ≤ Real.pi
    rw [Complex.sub_im, h_exp_one_sub_one_im, h_iX_im]
    linarith [Real.pi_pos]

/-! ### `eval?_arctanTermℂ` — the literal witness eval lemma -/

/-- For `0 < x < π`, `arctanTermℂ` partial-evaluates to `log(1 + ix)`. -/
lemma eval?_arctanTermℂ {env : Nat → ℂ} {x : ℝ}
    (hev : env 0 = ((x : ℝ) : ℂ)) (hx_pos : 0 < x) (hx_lt : x < Real.pi) :
    arctanTermℂ.eval? env =
      some (Complex.log (1 + Complex.I * ((x : ℝ) : ℂ))) := by
  unfold arctanTermℂ
  -- 1. iTermPubℂ.eval? = some I
  have hI : iTermPubℂ.eval? env = some Complex.I := eval?_iTermPubℂ env
  -- 2. (var 0).eval? = some (x : ℂ)
  have hX : (EMLTermℂ.var 0).eval? env = some ((x : ℝ) : ℂ) := by
    show some (env 0) = _; rw [hev]
  -- 3. mkMulℂ iTermPubℂ (var 0).eval? = some (I * x)
  have hX_ne : ((x : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hx_pos.ne'
  have hI_arg : Complex.arg Complex.I < Real.pi := by
    rw [Complex.arg_I]; linarith [Real.pi_pos]
  have hX_arg : Complex.arg ((x : ℝ) : ℂ) < Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx_pos.le]
    exact Real.pi_pos
  have hMul : (mkMulℂ iTermPubℂ (.var 0)).eval? env =
      some (Complex.I * ((x : ℝ) : ℂ)) :=
    eval?_mkMulℂ hI hX Complex.I_ne_zero hX_ne hI_arg hX_arg
      (addsafe_logI_logX hx_pos)
  -- 4. mkAddℂ .one (mkMulℂ ...).eval? = some (1 + I*x)
  have hOne : (EMLTermℂ.one).eval? env = some 1 := EMLTermℂ.eval?_one env
  have hAdd : (mkAddℂ .one (mkMulℂ iTermPubℂ (.var 0))).eval? env =
      some (1 + Complex.I * ((x : ℝ) : ℂ)) :=
    eval?_mkAddℂ hOne hMul (addsafe_one_iX hx_pos hx_lt)
  -- 5. mkLogℂ ... .eval? = some (log (1 + I*x))
  have h_one_plus_iX_ne : (1 + Complex.I * ((x : ℝ) : ℂ)) ≠ 0 := by
    intro h
    have h_re := congrArg Complex.re h
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im] at h_re
  have h_one_plus_iX_arg : Complex.arg (1 + Complex.I * ((x : ℝ) : ℂ)) < Real.pi := by
    -- re = 1 > 0, so arg ≠ π (only -arg-cut). Use arg_lt_pi_iff.
    apply Complex.arg_lt_pi_iff.mpr
    left
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  exact eval?_mkLogℂ hAdd h_one_plus_iX_ne h_one_plus_iX_arg

/-! ### `√(1 − x²)` via the real compiler, lifted to ℂ -/

/-- The real EL expression `sqrt(1 − x²)` (with var 0 the input). -/
def sqrtOneSubSqELℝ : ELExpr := .sqrt (.sub .one (.sq (.var 0)))

/-- The complex-grammar witness for `√(1 − x²)`, obtained by compiling
the real EL expression and lifting. -/
noncomputable def sqrtOneSubSqTermℂ : EMLTermℂ := sqrtOneSubSqELℝ.compile.toComplex

/-- Eval lemma: for `|x| < 1`, the complex-lifted real witness for
`√(1 − x²)` evaluates to `((Real.sqrt (1 − x²) : ℝ) : ℂ)` at the
canonical lift env `fun n => if n = 0 then ((x : ℝ) : ℂ) else 0`. -/
lemma eval?_sqrtOneSubSqTermℂ_lift {x : ℝ} (hxlo : -1 < x) (hxhi : x < 1) :
    sqrtOneSubSqTermℂ.eval?
        (fun n => if n = 0 then ((x : ℝ) : ℂ) else 0) =
      some ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) := by
  unfold sqrtOneSubSqTermℂ
  -- ELExpr eval at the canonical real env
  set realEnv : Nat → ℝ := fun n => if n = 0 then x else 0 with hrealEnv
  have h_one_sub_sq_pos : 0 < 1 - x ^ 2 := by nlinarith
  have h_el_eval :
      sqrtOneSubSqELℝ.eval? realEnv = some (Real.sqrt (1 - x ^ 2)) := by
    unfold sqrtOneSubSqELℝ
    simp [ELExpr.eval?, bind2, hrealEnv, h_one_sub_sq_pos]
  have h_compile :
      sqrtOneSubSqELℝ.compile.eval? realEnv = some (Real.sqrt (1 - x ^ 2)) :=
    ELExpr.compile_correct sqrtOneSubSqELℝ realEnv (Real.sqrt (1 - x ^ 2)) h_el_eval
  -- Show the complex env in the goal is the real-cast of realEnv
  have h_env_eq :
      (fun n : Nat => if n = 0 then ((x : ℝ) : ℂ) else 0)
        = (fun n => ((realEnv n : ℝ) : ℂ)) := by
    funext n
    by_cases h : n = 0
    · subst h; simp [hrealEnv]
    · simp [hrealEnv, h]
  rw [h_env_eq]
  exact EMLTerm.eval?_toComplex_of_real h_compile

/-! ### Bridge: `(arctanTermℂ.eval?).im = Real.arctan x` -/

/-- For `0 < x < π`, the imaginary part of `arctanTermℂ`'s evaluation is
exactly `Real.arctan x`. -/
theorem arctan_im_bridge {env : Nat → ℂ} {x : ℝ}
    (hev : env 0 = ((x : ℝ) : ℂ)) (hx_pos : 0 < x) (hx_lt : x < Real.pi) :
    ∃ vc : ℂ, arctanTermℂ.eval? env = some vc ∧ vc.im = Real.arctan x := by
  refine ⟨Complex.log (1 + Complex.I * ((x : ℝ) : ℂ)),
    eval?_arctanTermℂ hev hx_pos hx_lt, ?_⟩
  -- Goal: (Complex.log (1 + I * x)).im = Real.arctan x
  -- Use Complex.log_im → arg(1 + ix) = arctan x
  rw [Complex.log_im]
  -- arg(1 + ix) = arctan x for x real
  -- (1 + ix).re = 1 > 0, so arg z = arcsin (z.im / ‖z‖)
  -- (1 + ix).im = x, ‖z‖ = √(1 + x²)
  -- arcsin (x / √(1 + x²)) = arctan x by Real.arctan_eq_arcsin
  have hre : (1 + Complex.I * ((x : ℝ) : ℂ)).re = 1 := by
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have him : (1 + Complex.I * ((x : ℝ) : ℂ)).im = x := by
    simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hnorm : ‖(1 + Complex.I * ((x : ℝ) : ℂ))‖ = Real.sqrt (1 + x ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply, hre, him]
    congr 1; ring
  have h_re_nn : 0 ≤ (1 + Complex.I * ((x : ℝ) : ℂ)).re := by rw [hre]; exact zero_le_one
  rw [Complex.arg_of_re_nonneg h_re_nn, him, hnorm, Real.arctan_eq_arcsin]

/-! ## §A.6 — literal `EMLTermℂ` witness for `Real.arccos` (full open `(-1, 1)`)

For `x ∈ (-1, 1)`, the complex number `x + i√(1−x²)` lies on the unit
circle (`‖z‖ = 1`) with imaginary part `> 0`, so

  `Complex.log (x + i√(1−x²)) = i · Real.arccos x`,

giving the bridge `(arccosTermℂ.eval? env).im = Real.arccos x`. -/

/-- The arccos witness term. Pro's recommended path: `mkLogℂ` of
`x + i·√(1−x²)`, with the square root lifted from the sealed real
compiler via `EMLTerm.toComplex`. -/
noncomputable def arccosTermℂ : EMLTermℂ :=
  mkLogℂ (mkAddℂ (.var 0) (mkMulℂ iTermPubℂ sqrtOneSubSqTermℂ))

/-- For `|x| < 1`, `arccosTermℂ` partial-evaluates to `log(x + i√(1−x²))`. -/
lemma eval?_arccosTermℂ_lift {x : ℝ} (hxlo : -1 < x) (hxhi : x < 1) :
    arccosTermℂ.eval?
        (fun n => if n = 0 then ((x : ℝ) : ℂ) else 0) =
      some (Complex.log (((x : ℝ) : ℂ) +
        Complex.I * ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ))) := by
  unfold arccosTermℂ
  set env : Nat → ℂ := fun n => if n = 0 then ((x : ℝ) : ℂ) else 0 with henv
  -- (var 0).eval? env = some ((x : ℝ) : ℂ)
  have hVar : (EMLTermℂ.var 0).eval? env = some ((x : ℝ) : ℂ) := by
    show some (env 0) = _; simp [henv]
  -- iTermPubℂ.eval? env = some Complex.I
  have hI : iTermPubℂ.eval? env = some Complex.I := eval?_iTermPubℂ env
  -- sqrtOneSubSqTermℂ.eval? env = some ((Real.sqrt (1 - x^2) : ℝ) : ℂ)
  have hSqrt : sqrtOneSubSqTermℂ.eval? env =
      some ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) :=
    eval?_sqrtOneSubSqTermℂ_lift hxlo hxhi
  -- 0 < √(1 - x²) since |x| < 1
  have h_one_sub_sq_pos : 0 < 1 - x ^ 2 := by nlinarith
  have hSqrtPos : 0 < Real.sqrt (1 - x ^ 2) :=
    Real.sqrt_pos.mpr h_one_sub_sq_pos
  -- mkMulℂ iTermPubℂ sqrtOneSubSqTermℂ → some (I · √(1-x²))
  have hSqrt_ne : ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hSqrtPos.ne'
  have hI_arg : Complex.arg Complex.I < Real.pi := by
    rw [Complex.arg_I]; linarith [Real.pi_pos]
  have hSqrt_arg : Complex.arg ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) < Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hSqrtPos.le]; exact Real.pi_pos
  have hMul : (mkMulℂ iTermPubℂ sqrtOneSubSqTermℂ).eval? env =
      some (Complex.I * ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ)) :=
    eval?_mkMulℂ hI hSqrt Complex.I_ne_zero hSqrt_ne hI_arg hSqrt_arg
      (addsafe_logI_logX hSqrtPos)
  -- I · √(1-x²) is purely imaginary with .im = √(1-x²)
  have h_iSqrt_im : (Complex.I * ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ)).im =
      Real.sqrt (1 - x ^ 2) := by
    simp [Complex.mul_im, Complex.I_re, Complex.I_im]
  have h_iSqrt_re : (Complex.I * ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  -- ADDsafeℂ for ((x:ℂ), I·√(1-x²))
  -- Bound √(1-x²) ≤ 1 (since 1 - x² ≤ 1)
  have h_sqrt_le : Real.sqrt (1 - x ^ 2) ≤ 1 := by
    have h_le : (1 - x ^ 2) ≤ 1 := by nlinarith [sq_nonneg x]
    calc Real.sqrt (1 - x ^ 2)
        ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h_le
      _ = 1 := Real.sqrt_one
  have hAddSafe : ADDsafeℂ (((x : ℝ) : ℂ))
      (Complex.I * ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ)) := by
    apply addsafe_ofReal_left
    · -- -π < √(1-x²) — true since √ ≥ 0 and π > 0
      rw [h_iSqrt_im]
      linarith [Real.sqrt_nonneg (1 - x^2), Real.pi_pos]
    · -- √(1-x²) ≤ π — use √(1-x²) ≤ 1 < π
      rw [h_iSqrt_im]; linarith [h_sqrt_le, Real.pi_gt_three]
    · -- -π < -√(1-x²) — i.e., √(1-x²) < π
      rw [h_iSqrt_im]; linarith [h_sqrt_le, Real.pi_gt_three]
    · -- -√(1-x²) ≤ π — true since √ ≥ 0 ≥ -π
      rw [h_iSqrt_im]
      linarith [Real.sqrt_nonneg (1 - x^2), Real.pi_pos]
  have hAdd : (mkAddℂ (.var 0) (mkMulℂ iTermPubℂ sqrtOneSubSqTermℂ)).eval? env =
      some (((x : ℝ) : ℂ) + Complex.I * ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ)) :=
    eval?_mkAddℂ hVar hMul hAddSafe
  -- Now mkLogℂ — need (x + i√(1-x²)) ≠ 0 and arg < π
  set z : ℂ := ((x : ℝ) : ℂ) + Complex.I * ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ)
    with hz_def
  have h_z_re : z.re = x := by
    rw [hz_def]; simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have h_z_im : z.im = Real.sqrt (1 - x ^ 2) := by
    rw [hz_def]; simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  -- ‖z‖ = 1, so z ≠ 0
  have h_norm_z : ‖z‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_apply, h_z_re, h_z_im]
    have hnn : 0 ≤ 1 - x ^ 2 := h_one_sub_sq_pos.le
    rw [Real.mul_self_sqrt hnn]
    rw [show x * x + (1 - x^2) = 1 from by ring]
    exact Real.sqrt_one
  have h_z_ne : z ≠ 0 := by
    intro h; rw [h] at h_norm_z; simp at h_norm_z
  -- arg z < π : z has im > 0, so arg z = arccos(re/‖z‖) ∈ (0, π) for re > -1
  -- Since ‖z‖ = 1 and im = √(1-x²) > 0, arg z = arccos x.
  have h_z_arg_lt_pi : Complex.arg z < Real.pi := by
    -- Use arg_lt_pi_iff: arg z < π iff 0 ≤ z.re ∨ z.im ≠ 0
    apply Complex.arg_lt_pi_iff.mpr
    right
    rw [h_z_im]
    exact hSqrtPos.ne'
  exact eval?_mkLogℂ hAdd h_z_ne h_z_arg_lt_pi

/-- For `-1 < x < 1`, the imaginary part of `arccosTermℂ.eval?` is
exactly `Real.arccos x`. -/
theorem arccos_im_bridge {x : ℝ} (hxlo : -1 < x) (hxhi : x < 1) :
    ∃ vc : ℂ,
      arccosTermℂ.eval? (fun n => if n = 0 then ((x : ℝ) : ℂ) else 0) = some vc
        ∧ vc.im = Real.arccos x := by
  refine ⟨Complex.log (((x : ℝ) : ℂ) +
            Complex.I * ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ)),
    eval?_arccosTermℂ_lift hxlo hxhi, ?_⟩
  -- z := x + i·√(1−x²)
  set z : ℂ := ((x : ℝ) : ℂ) + Complex.I * ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ)
    with hz_def
  -- Step 1: z = exp(I · arccos x).  Use Real.cos_arccos / Real.sin_arccos.
  have h_exp_eq : Complex.exp (Complex.I * ((Real.arccos x : ℝ) : ℂ)) = z := by
    rw [show Complex.I * ((Real.arccos x : ℝ) : ℂ) =
            ((Real.arccos x : ℝ) : ℂ) * Complex.I from by ring,
        Complex.exp_mul_I]
    rw [hz_def]
    rw [(Complex.ofReal_cos (Real.arccos x)).symm,
        (Complex.ofReal_sin (Real.arccos x)).symm,
        Real.cos_arccos hxlo.le hxhi.le, Real.sin_arccos]
    ring
  -- Step 2: log z = I · arccos x via Complex.log_exp.
  have h_arccos_im :
      (Complex.I * ((Real.arccos x : ℝ) : ℂ)).im = Real.arccos x := by
    simp [Complex.mul_im, Complex.I_re, Complex.I_im]
  rw [show z = Complex.exp (Complex.I * ((Real.arccos x : ℝ) : ℂ))
        from h_exp_eq.symm,
      Complex.log_exp ?_ ?_, h_arccos_im]
  · rw [h_arccos_im]
    have h1 : 0 ≤ Real.arccos x := Real.arccos_nonneg x
    linarith [Real.pi_pos]
  · rw [h_arccos_im]; exact Real.arccos_le_pi x

/-! ## §A.4b — `arctanTermℂ_neg`: literal witness for `Real.arctan` on `(-π, 0)`

The narrowed `arctanTermℂ` only handles `0 < x < π` because its inner
`mkMulℂ iTermPubℂ (.var 0)` requires `arg(x) < π`, failing for `x ≤ 0`.

For `x < 0`, use `1 + ix = 1 − i·(−x)` where `−x > 0`. This shifts the
multiplication-by-i into a positive-real argument (which `mkMulℂ` accepts)
and absorbs the sign into the outer `mkSubℂ .one`. The imaginary-part
identity `(log(1 + ix)).im = arctan x` from `arctan_im_bridge` then
re-applies verbatim because it never used `0 < x`. -/

/-- Real EL expression for `−x`. -/
def negVarELℝ : ELExpr := .neg (.var 0)

/-- Complex-grammar witness for `−x`, lifted from the compiled real EL. -/
noncomputable def negVarTermℂ : EMLTermℂ := negVarELℝ.compile.toComplex

/-- Eval lemma: at the canonical real-cast env, the lifted `−x` witness
evaluates to `((−x : ℝ) : ℂ)`. -/
lemma eval?_negVarTermℂ_lift {x : ℝ} :
    negVarTermℂ.eval? (fun n => if n = 0 then ((x : ℝ) : ℂ) else 0) =
      some (((-x : ℝ) : ℂ)) := by
  unfold negVarTermℂ
  set realEnv : Nat → ℝ := fun n => if n = 0 then x else 0 with hrealEnv
  have h_el_eval : negVarELℝ.eval? realEnv = some (-x) := by
    unfold negVarELℝ
    simp [ELExpr.eval?, hrealEnv]
  have h_compile :
      negVarELℝ.compile.eval? realEnv = some (-x) :=
    ELExpr.compile_correct negVarELℝ realEnv (-x) h_el_eval
  have h_env_eq :
      (fun n : Nat => if n = 0 then ((x : ℝ) : ℂ) else 0)
        = (fun n => ((realEnv n : ℝ) : ℂ)) := by
    funext n
    by_cases h : n = 0
    · subst h; simp [hrealEnv]
    · simp [hrealEnv, h]
  rw [h_env_eq]
  exact EMLTerm.eval?_toComplex_of_real h_compile

/-- ADDsafeℂ for `(.one, I * (−x : ℝ : ℂ))` when `0 < −x < π`
(equivalently `−π < x < 0`). Mirrors `addsafe_one_iX` with `−x` in place
of `x`. -/
private lemma addsafe_one_iNegX {x : ℝ} (hx_neg : x < 0) (hx_lo : -Real.pi < x) :
    ADDsafeℂ (1 : ℂ) (Complex.I * (((-x : ℝ)) : ℂ)) :=
  addsafe_one_iX (by linarith : 0 < -x) (by linarith : -x < Real.pi)

/-- The negative-side arctan witness, sealed on `(-π, 0)`. -/
noncomputable def arctanTermℂ_neg : EMLTermℂ :=
  mkLogℂ (mkSubℂ .one (mkMulℂ iTermPubℂ negVarTermℂ))

/-- For `-π < x < 0`, `arctanTermℂ_neg` evaluates to `Complex.log (1 + I*x)`. -/
lemma eval?_arctanTermℂ_neg {x : ℝ} (hx_neg : x < 0) (hx_lo : -Real.pi < x) :
    arctanTermℂ_neg.eval?
        (fun n => if n = 0 then ((x : ℝ) : ℂ) else 0) =
      some (Complex.log (1 + Complex.I * ((x : ℝ) : ℂ))) := by
  unfold arctanTermℂ_neg
  set env : Nat → ℂ := fun n => if n = 0 then ((x : ℝ) : ℂ) else 0 with henv
  have hI : iTermPubℂ.eval? env = some Complex.I := eval?_iTermPubℂ env
  have hNeg : negVarTermℂ.eval? env = some (((-x : ℝ)) : ℂ) :=
    eval?_negVarTermℂ_lift (x := x)
  have h_negx_pos : 0 < -x := by linarith
  have h_negx_ne : (((-x : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast h_negx_pos.ne'
  have hI_arg : Complex.arg Complex.I < Real.pi := by
    rw [Complex.arg_I]; linarith [Real.pi_pos]
  have h_negx_arg : Complex.arg (((-x : ℝ)) : ℂ) < Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg h_negx_pos.le]; exact Real.pi_pos
  have hMul : (mkMulℂ iTermPubℂ negVarTermℂ).eval? env =
      some (Complex.I * (((-x : ℝ)) : ℂ)) :=
    eval?_mkMulℂ hI hNeg Complex.I_ne_zero h_negx_ne hI_arg h_negx_arg
      (addsafe_logI_logX h_negx_pos)
  have hOne : (EMLTermℂ.one).eval? env = some 1 := EMLTermℂ.eval?_one env
  -- mkSubℂ .one (mkMulℂ iTermPubℂ negVarTermℂ) = 1 - I*(-x) = 1 + I*x
  have h_iNegX_im : (Complex.I * (((-x : ℝ)) : ℂ)).im = -x := by
    simp [Complex.mul_im, Complex.I_re, Complex.I_im]
  have h_im_lo : -Real.pi < (Complex.I * (((-x : ℝ)) : ℂ)).im := by
    rw [h_iNegX_im]; linarith
  have h_im_hi : (Complex.I * (((-x : ℝ)) : ℂ)).im ≤ Real.pi := by
    rw [h_iNegX_im]; linarith
  have h1_arg : Complex.arg (1 : ℂ) < Real.pi := by
    rw [Complex.arg_one]; linarith [Real.pi_pos]
  have hSub : (mkSubℂ .one (mkMulℂ iTermPubℂ negVarTermℂ)).eval? env =
      some (1 - Complex.I * (((-x : ℝ)) : ℂ)) :=
    eval?_mkSubℂ hOne hMul one_ne_zero h1_arg h_im_lo h_im_hi
  -- 1 - I*(-x) = 1 + I*x as complex values
  have h_eq : (1 - Complex.I * (((-x : ℝ)) : ℂ)) =
      (1 + Complex.I * ((x : ℝ) : ℂ)) := by push_cast; ring
  rw [h_eq] at hSub
  -- Apply mkLogℂ — re = 1 > 0, so arg < π
  have h_one_plus_iX_ne : (1 + Complex.I * ((x : ℝ) : ℂ)) ≠ 0 := by
    intro h
    have h_re := congrArg Complex.re h
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im] at h_re
  have h_one_plus_iX_arg : Complex.arg (1 + Complex.I * ((x : ℝ) : ℂ)) < Real.pi := by
    apply Complex.arg_lt_pi_iff.mpr
    left
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  exact eval?_mkLogℂ hSub h_one_plus_iX_ne h_one_plus_iX_arg

/-- For `-π < x < 0`, the imaginary part of `arctanTermℂ_neg.eval?` is
exactly `Real.arctan x`. The `.im` calculation is identical to the
positive-side bridge — neither uses `0 < x`. -/
theorem arctan_im_bridge_neg {x : ℝ} (hx_neg : x < 0) (hx_lo : -Real.pi < x) :
    ∃ vc : ℂ,
      arctanTermℂ_neg.eval? (fun n => if n = 0 then ((x : ℝ) : ℂ) else 0)
        = some vc
        ∧ vc.im = Real.arctan x := by
  refine ⟨Complex.log (1 + Complex.I * ((x : ℝ) : ℂ)),
    eval?_arctanTermℂ_neg hx_neg hx_lo, ?_⟩
  rw [Complex.log_im]
  have hre : (1 + Complex.I * ((x : ℝ) : ℂ)).re = 1 := by
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have him : (1 + Complex.I * ((x : ℝ) : ℂ)).im = x := by
    simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hnorm : ‖(1 + Complex.I * ((x : ℝ) : ℂ))‖ = Real.sqrt (1 + x ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply, hre, him]
    congr 1; ring
  have h_re_nn : 0 ≤ (1 + Complex.I * ((x : ℝ) : ℂ)).re := by rw [hre]; exact zero_le_one
  rw [Complex.arg_of_re_nonneg h_re_nn, him, hnorm, Real.arctan_eq_arcsin]

/-! ## §A.4c — `cosTermℂ_neg`: cos witness on `(-∞, 0)`

Mirror trick: `cos x = cos(-x)`. Since the existing `cosTermℂ` only works
for `x > 0` (its inner `mkLogℂ (.var 0)` requires `arg(x) < π`, failing for
`x ≤ 0`), we feed `-x` (positive) into the cleaner builder form. -/

/-- The cos witness for negative inputs, built with high-level builders
plus the `negVarTermℂ` substitute. Evaluates to `Complex.exp (Complex.exp
(log I + log (-x))) = Complex.exp (-I*x)` for `x < 0`, whose real part is
`Real.cos x` (cos is even). -/
noncomputable def cosTermℂ_neg : EMLTermℂ :=
  mkExpℂ (mkExpℂ (mkAddℂ (mkLogℂ iTermPubℂ) (mkLogℂ negVarTermℂ)))

/-- For `x < 0`, `cosTermℂ_neg` evaluates to `Complex.exp (-I*x)`. -/
lemma eval?_cosTermℂ_neg {x : ℝ} (hx_neg : x < 0) :
    cosTermℂ_neg.eval?
        (fun n => if n = 0 then ((x : ℝ) : ℂ) else 0) =
      some (Complex.exp (-(Complex.I * ((x : ℝ) : ℂ)))) := by
  unfold cosTermℂ_neg
  set env : Nat → ℂ := fun n => if n = 0 then ((x : ℝ) : ℂ) else 0 with henv
  -- step 1: log I = iπ/2
  have hI : iTermPubℂ.eval? env = some Complex.I := eval?_iTermPubℂ env
  have hI_arg : Complex.arg Complex.I < Real.pi := by
    rw [Complex.arg_I]; linarith [Real.pi_pos]
  have h_logI : (mkLogℂ iTermPubℂ).eval? env = some (Complex.log Complex.I) :=
    eval?_mkLogℂ hI Complex.I_ne_zero hI_arg
  -- step 2: log (-x : ℂ)
  have h_negx_pos : 0 < -x := by linarith
  have hNeg : negVarTermℂ.eval? env = some (((-x : ℝ)) : ℂ) :=
    eval?_negVarTermℂ_lift (x := x)
  have h_negx_ne : (((-x : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast h_negx_pos.ne'
  have h_negx_arg : Complex.arg (((-x : ℝ)) : ℂ) < Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg h_negx_pos.le]; exact Real.pi_pos
  have h_logNegX : (mkLogℂ negVarTermℂ).eval? env =
      some (Complex.log (((-x : ℝ)) : ℂ)) :=
    eval?_mkLogℂ hNeg h_negx_ne h_negx_arg
  -- ADDsafeℂ for (log I, log (-x : ℂ))
  have hAddSafe : ADDsafeℂ (Complex.log Complex.I)
      (Complex.log (((-x : ℝ)) : ℂ)) :=
    addsafe_logI_logX h_negx_pos
  have h_inner_add :
      (mkAddℂ (mkLogℂ iTermPubℂ) (mkLogℂ negVarTermℂ)).eval? env =
      some (Complex.log Complex.I + Complex.log (((-x : ℝ)) : ℂ)) :=
    eval?_mkAddℂ h_logI h_logNegX hAddSafe
  -- exp(log I + log(-x : ℂ)) = I * (-x : ℂ) = -(I * x)
  have h_inner_exp :
      (mkExpℂ (mkAddℂ (mkLogℂ iTermPubℂ) (mkLogℂ negVarTermℂ))).eval? env =
      some (Complex.exp (Complex.log Complex.I +
        Complex.log (((-x : ℝ)) : ℂ))) :=
    eval?_mkExpℂ h_inner_add
  -- Simplify Complex.exp (log I + log(-x)) = I * (-x)
  have h_simpl : Complex.exp (Complex.log Complex.I +
      Complex.log (((-x : ℝ)) : ℂ)) = -(Complex.I * ((x : ℝ) : ℂ)) := by
    rw [Complex.exp_add, Complex.exp_log Complex.I_ne_zero,
        Complex.exp_log h_negx_ne]
    push_cast; ring
  rw [h_simpl] at h_inner_exp
  -- Outer mkExpℂ: exp(-Ix)
  exact eval?_mkExpℂ h_inner_exp

/-- For `x < 0`, the **real part** of `cosTermℂ_neg.eval?` is `Real.cos x`. -/
theorem cos_re_bridge_neg {x : ℝ} (hx_neg : x < 0) :
    ∃ vc : ℂ,
      cosTermℂ_neg.eval? (fun n => if n = 0 then ((x : ℝ) : ℂ) else 0)
        = some vc ∧ vc.re = Real.cos x := by
  refine ⟨Complex.exp (-(Complex.I * ((x : ℝ) : ℂ))), eval?_cosTermℂ_neg hx_neg, ?_⟩
  -- exp(-Ix) = cos(-x) + i*sin(-x) = cos x - i*sin x; re = cos x.
  rw [show -(Complex.I * ((x : ℝ) : ℂ)) =
          (((-x : ℝ)) : ℂ) * Complex.I from by push_cast; ring,
      Complex.exp_mul_I]
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.add_re,
    Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, Complex.ofReal_re, mul_zero, mul_one,
    sub_zero, add_zero, Real.cos_neg]

/-! ## §A.4d — `sinTermℂ_neg`: sin witness on `(-π, 0)`

Mirror of `cos_re_bridge_neg`. The choice is
`mkExpℂ (mkSubℂ (mkLogℂ cosTermℂ_neg) (mkLogℂ negIPubℂ))`:

  inner: `(−Ix) − (−Iπ/2) = I(π/2 − x)`,
  outer: `exp(I(π/2 − x)) = cos(π/2 − x) + I sin(π/2 − x)`,
  real part: `cos(π/2 − x) = sin x`. -/

/-- The sin witness for negative inputs, sealed on `(-π, 0)`. -/
noncomputable def sinTermℂ_neg : EMLTermℂ :=
  mkExpℂ (mkSubℂ (mkLogℂ cosTermℂ_neg) (mkLogℂ negIPubℂ))

/-- For `-π < x < 0`, `sinTermℂ_neg` evaluates to `Complex.exp (I*(π/2 − x))`. -/
lemma eval?_sinTermℂ_neg {x : ℝ} (hx_neg : x < 0) (hx_lo : -Real.pi < x) :
    sinTermℂ_neg.eval?
        (fun n => if n = 0 then ((x : ℝ) : ℂ) else 0) =
      some (Complex.exp (Complex.I * (((Real.pi / 2 - x : ℝ)) : ℂ))) := by
  unfold sinTermℂ_neg
  set env : Nat → ℂ := fun n => if n = 0 then ((x : ℝ) : ℂ) else 0 with henv
  -- cosTermℂ_neg.eval = exp(-Ix)
  have h_cos : cosTermℂ_neg.eval? env = some (Complex.exp (-(Complex.I * ((x : ℝ) : ℂ)))) :=
    eval?_cosTermℂ_neg hx_neg
  -- (-Ix).im = -x, lies in (0, π) for x ∈ (-π, 0)
  have h_negIx_im : (-(Complex.I * ((x : ℝ) : ℂ))).im = -x := by
    simp [Complex.neg_im, Complex.mul_im, Complex.I_re, Complex.I_im]
  have h_negIx_im_lo : -Real.pi < (-(Complex.I * ((x : ℝ) : ℂ))).im := by
    rw [h_negIx_im]; linarith [Real.pi_pos]
  have h_negIx_im_hi : (-(Complex.I * ((x : ℝ) : ℂ))).im ≤ Real.pi := by
    rw [h_negIx_im]; linarith
  -- exp(-Ix) ≠ 0
  have h_exp_negIx_ne : Complex.exp (-(Complex.I * ((x : ℝ) : ℂ))) ≠ 0 :=
    Complex.exp_ne_zero _
  -- arg(exp(-Ix)) < π. arg(exp(y*I)) = y mod 2π for y real.
  have h_exp_negIx_arg_lt_pi :
      Complex.arg (Complex.exp (-(Complex.I * ((x : ℝ) : ℂ)))) < Real.pi := by
    have h_eq : -(Complex.I * ((x : ℝ) : ℂ)) =
        ((-x : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [h_eq, Complex.arg_exp_mul_I]
    have htio : toIocMod Real.two_pi_pos (-Real.pi) (-x) = -x := by
      rw [toIocMod_eq_self Real.two_pi_pos]
      refine ⟨by linarith, ?_⟩
      have : -Real.pi + 2 * Real.pi = Real.pi := by ring
      rw [this]; linarith
    rw [htio]; linarith
  -- mkLogℂ cosTermℂ_neg.eval = log(exp(-Ix)) = -Ix
  have h_log_cos := eval?_mkLogℂ h_cos h_exp_negIx_ne h_exp_negIx_arg_lt_pi
  rw [Complex.log_exp h_negIx_im_lo h_negIx_im_hi] at h_log_cos
  -- mkLogℂ negIPubℂ.eval = log(-I) = -Iπ/2
  have h_negI : negIPubℂ.eval? env = some (-Complex.I) := eval?_negIPubℂ env
  have h_negI_arg : Complex.arg (-Complex.I) < Real.pi := by
    rw [Complex.arg_neg_I]; linarith [Real.pi_pos]
  have h_neg_I_ne : (-Complex.I) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  have h_log_negI := eval?_mkLogℂ h_negI h_neg_I_ne h_negI_arg
  -- log(-I) = -(π/2)*I
  have h_log_negI_im : (Complex.log (-Complex.I)).im = -(Real.pi / 2) := by
    rw [Complex.log_neg_I]
    simp [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.neg_im]
  have h_log_negI_im_lo : -Real.pi < (Complex.log (-Complex.I)).im := by
    rw [h_log_negI_im]; linarith [Real.pi_pos]
  have h_log_negI_im_hi : (Complex.log (-Complex.I)).im ≤ Real.pi := by
    rw [h_log_negI_im]; linarith [Real.pi_pos]
  -- mkSubℂ: (-Ix) - log(-I) = -Ix + Iπ/2 = I(π/2 - x)
  have h_log_cos_ne : -(Complex.I * ((x : ℝ) : ℂ)) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    rw [h_negIx_im] at him
    simp at him; linarith
  have h_log_cos_arg : Complex.arg (-(Complex.I * ((x : ℝ) : ℂ))) < Real.pi := by
    -- -Ix has re = 0, im = -x > 0 for x < 0; arg = π/2
    have h_eq : -(Complex.I * ((x : ℝ) : ℂ)) =
        ((-x : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [h_eq, Complex.arg_real_mul Complex.I (by linarith : (0 : ℝ) < -x), Complex.arg_I]
    linarith [Real.pi_pos]
  have h_sub :
      (mkSubℂ (mkLogℂ cosTermℂ_neg) (mkLogℂ negIPubℂ)).eval? env =
        some (-(Complex.I * ((x : ℝ) : ℂ)) - Complex.log (-Complex.I)) :=
    eval?_mkSubℂ h_log_cos h_log_negI h_log_cos_ne h_log_cos_arg
      h_log_negI_im_lo h_log_negI_im_hi
  -- Simplify the subtraction: -Ix - (-Iπ/2) = -Ix + Iπ/2 = I(π/2 - x)
  have h_simpl : -(Complex.I * ((x : ℝ) : ℂ)) - Complex.log (-Complex.I) =
      Complex.I * (((Real.pi / 2 - x : ℝ)) : ℂ) := by
    rw [Complex.log_neg_I]; push_cast; ring
  rw [h_simpl] at h_sub
  -- Apply outer mkExpℂ
  exact eval?_mkExpℂ h_sub

/-- For `-π < x < 0`, the **real part** of `sinTermℂ_neg.eval?` is `Real.sin x`. -/
theorem sin_re_bridge_neg {x : ℝ} (hx_neg : x < 0) (hx_lo : -Real.pi < x) :
    ∃ vc : ℂ,
      sinTermℂ_neg.eval? (fun n => if n = 0 then ((x : ℝ) : ℂ) else 0)
        = some vc ∧ vc.re = Real.sin x := by
  refine ⟨Complex.exp (Complex.I * (((Real.pi / 2 - x : ℝ)) : ℂ)),
    eval?_sinTermℂ_neg hx_neg hx_lo, ?_⟩
  -- exp(I*(π/2 - x)).re = cos(π/2 - x) = sin x
  rw [show Complex.I * (((Real.pi / 2 - x : ℝ)) : ℂ) =
          (((Real.pi / 2 - x : ℝ)) : ℂ) * Complex.I from by ring,
      Complex.exp_mul_I]
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.add_re,
    Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, Complex.ofReal_re, mul_zero, mul_one,
    sub_zero, add_zero]
  exact (Real.cos_pi_div_two_sub x).symm ▸ rfl

/-! ## §A.5 — literal `EMLTermℂ` witness for `Real.arcsin` (narrowed `(0, 1)`)

For `x ∈ (0, 1)`,

  `Complex.log (√(1−x²) + i·x) = i · Real.arcsin x`,

so `(arcsinTermℂ.eval? env).im = Real.arcsin x` on this open subinterval.
The narrowing comes from `mkMulℂ iTermPubℂ (var 0)` which needs
`var ≠ 0` and `arg(var) < π` (true for `var = (x : ℂ)` with `x > 0`). -/

/-- The arcsin witness term. -/
noncomputable def arcsinTermℂ : EMLTermℂ :=
  mkLogℂ (mkAddℂ sqrtOneSubSqTermℂ (mkMulℂ iTermPubℂ (.var 0)))

/-- For `0 < x < 1`, `arcsinTermℂ` partial-evaluates to
`log(√(1−x²) + i·x)`. -/
lemma eval?_arcsinTermℂ_lift {x : ℝ} (hx_pos : 0 < x) (hx_lt : x < 1) :
    arcsinTermℂ.eval?
        (fun n => if n = 0 then ((x : ℝ) : ℂ) else 0) =
      some (Complex.log (((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) +
        Complex.I * ((x : ℝ) : ℂ))) := by
  unfold arcsinTermℂ
  set env : Nat → ℂ := fun n => if n = 0 then ((x : ℝ) : ℂ) else 0 with henv
  have hxlo : -1 < x := by linarith
  have hxhi : x < 1 := hx_lt
  have h_one_sub_sq_pos : 0 < 1 - x ^ 2 := by nlinarith
  have hSqrtPos : 0 < Real.sqrt (1 - x ^ 2) :=
    Real.sqrt_pos.mpr h_one_sub_sq_pos
  -- Sub-evaluations
  have hVar : (EMLTermℂ.var 0).eval? env = some ((x : ℝ) : ℂ) := by
    show some (env 0) = _; simp [henv]
  have hI : iTermPubℂ.eval? env = some Complex.I := eval?_iTermPubℂ env
  have hSqrt : sqrtOneSubSqTermℂ.eval? env =
      some ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) :=
    eval?_sqrtOneSubSqTermℂ_lift hxlo hxhi
  -- mkMulℂ iTermPubℂ (var 0) → some (I · x)
  have hX_ne : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx_pos.ne'
  have hI_arg : Complex.arg Complex.I < Real.pi := by
    rw [Complex.arg_I]; linarith [Real.pi_pos]
  have hX_arg : Complex.arg ((x : ℝ) : ℂ) < Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx_pos.le]; exact Real.pi_pos
  have hMul : (mkMulℂ iTermPubℂ (.var 0)).eval? env =
      some (Complex.I * ((x : ℝ) : ℂ)) :=
    eval?_mkMulℂ hI hVar Complex.I_ne_zero hX_ne hI_arg hX_arg
      (addsafe_logI_logX hx_pos)
  -- I · x is purely imaginary
  have h_iX_im : (Complex.I * ((x : ℝ) : ℂ)).im = x := by
    simp [Complex.mul_im, Complex.I_re, Complex.I_im]
  -- ADDsafeℂ for (√(1-x²) cast, I·x)
  have hAddSafe : ADDsafeℂ (((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ))
      (Complex.I * ((x : ℝ) : ℂ)) := by
    apply addsafe_ofReal_left
    · rw [h_iX_im]; linarith [Real.pi_gt_three]
    · rw [h_iX_im]; linarith [Real.pi_gt_three]
    · rw [h_iX_im]; linarith [Real.pi_gt_three]
    · rw [h_iX_im]; linarith [Real.pi_gt_three]
  have hAdd : (mkAddℂ sqrtOneSubSqTermℂ (mkMulℂ iTermPubℂ (.var 0))).eval? env =
      some (((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) + Complex.I * ((x : ℝ) : ℂ)) :=
    eval?_mkAddℂ hSqrt hMul hAddSafe
  -- mkLogℂ — z = √(1-x²) + i·x lies on the unit circle
  set z : ℂ := ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) + Complex.I * ((x : ℝ) : ℂ)
    with hz_def
  have h_z_re : z.re = Real.sqrt (1 - x ^ 2) := by
    rw [hz_def]; simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have h_z_im : z.im = x := by
    rw [hz_def]; simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have h_norm_z : ‖z‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_apply, h_z_re, h_z_im]
    rw [Real.mul_self_sqrt h_one_sub_sq_pos.le]
    rw [show (1 - x^2) + x * x = 1 from by ring]
    exact Real.sqrt_one
  have h_z_ne : z ≠ 0 := by
    intro h; rw [h] at h_norm_z; simp at h_norm_z
  have h_z_arg_lt_pi : Complex.arg z < Real.pi := by
    apply Complex.arg_lt_pi_iff.mpr
    left; rw [h_z_re]; exact hSqrtPos.le
  exact eval?_mkLogℂ hAdd h_z_ne h_z_arg_lt_pi

/-- For `0 < x < 1`, the imaginary part of `arcsinTermℂ.eval?` is exactly
`Real.arcsin x`. -/
theorem arcsin_im_bridge {x : ℝ} (hx_pos : 0 < x) (hx_lt : x < 1) :
    ∃ vc : ℂ,
      arcsinTermℂ.eval? (fun n => if n = 0 then ((x : ℝ) : ℂ) else 0) = some vc
        ∧ vc.im = Real.arcsin x := by
  refine ⟨Complex.log (((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) +
            Complex.I * ((x : ℝ) : ℂ)),
    eval?_arcsinTermℂ_lift hx_pos hx_lt, ?_⟩
  set z : ℂ := ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) + Complex.I * ((x : ℝ) : ℂ)
    with hz_def
  have hxlo : -1 < x := by linarith
  -- z = exp(I · arcsin x)
  have h_exp_eq : Complex.exp (Complex.I * ((Real.arcsin x : ℝ) : ℂ)) = z := by
    rw [show Complex.I * ((Real.arcsin x : ℝ) : ℂ) =
            ((Real.arcsin x : ℝ) : ℂ) * Complex.I from by ring,
        Complex.exp_mul_I]
    rw [hz_def]
    rw [(Complex.ofReal_cos (Real.arcsin x)).symm,
        (Complex.ofReal_sin (Real.arcsin x)).symm,
        Real.sin_arcsin hxlo.le hx_lt.le,
        Real.cos_arcsin]
    ring
  have h_arcsin_im :
      (Complex.I * ((Real.arcsin x : ℝ) : ℂ)).im = Real.arcsin x := by
    simp [Complex.mul_im, Complex.I_re, Complex.I_im]
  rw [show z = Complex.exp (Complex.I * ((Real.arcsin x : ℝ) : ℂ))
        from h_exp_eq.symm,
      Complex.log_exp ?_ ?_, h_arcsin_im]
  · rw [h_arcsin_im]
    -- arcsin x ∈ [-π/2, π/2], so > -π
    linarith [Real.neg_pi_div_two_le_arcsin x, Real.pi_pos]
  · rw [h_arcsin_im]
    linarith [Real.arcsin_le_pi_div_two x, Real.pi_pos]

/-! ## §A.5b — `arcsinTermℂ_open`: literal witness for `Real.arcsin` on full `(-1, 1)`

The narrowed `arcsinTermℂ` above only handles `0 < x < 1` because its
inner `mkMulℂ iTermPubℂ (.var 0)` requires `arg(x) < π`, which fails for
`x ≤ 0` (real negatives have `arg = π` exactly).

To widen, use the identity `arcsin x = π/2 − arccos x` (Mathlib's
`Real.arcsin_eq_pi_div_two_sub_arccos`). Encode `iπ/2` literally via
`mkLogℂ iTermPubℂ` (since `Complex.log I = iπ/2`), then subtract
`arccosTermℂ` whose imaginary part is `arccos x` on the full open
`(-1, 1)`. -/

/-- The wider arcsin witness, sealed on the **full open** `(-1, 1)`. -/
noncomputable def arcsinTermℂ_open : EMLTermℂ :=
  mkSubℂ (mkLogℂ iTermPubℂ) arccosTermℂ

/-- For `-1 < x < 1`, the imaginary part of `arcsinTermℂ_open.eval?` is
exactly `Real.arcsin x`. -/
theorem arcsin_im_bridge_open {x : ℝ} (hxlo : -1 < x) (hxhi : x < 1) :
    ∃ vc : ℂ,
      arcsinTermℂ_open.eval? (fun n => if n = 0 then ((x : ℝ) : ℂ) else 0)
        = some vc
        ∧ vc.im = Real.arcsin x := by
  unfold arcsinTermℂ_open
  set env : Nat → ℂ := fun n => if n = 0 then ((x : ℝ) : ℂ) else 0 with henv
  -- mkLogℂ iTermPubℂ → some (Complex.log Complex.I) = some (iπ/2)
  have hI : iTermPubℂ.eval? env = some Complex.I := eval?_iTermPubℂ env
  have hI_arg : Complex.arg Complex.I < Real.pi := by
    rw [Complex.arg_I]; linarith [Real.pi_pos]
  have h_logI : (mkLogℂ iTermPubℂ).eval? env = some (Complex.log Complex.I) :=
    eval?_mkLogℂ hI Complex.I_ne_zero hI_arg
  -- Compute Complex.log I = (π/2) * I
  have h_logI_im : (Complex.log Complex.I).im = Real.pi / 2 := by
    rw [Complex.log_I]
    simp [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.div_re, Complex.div_im]
  -- arccosTermℂ → some (Complex.log (x + i√(1-x²)))
  have h_arc : arccosTermℂ.eval? env =
      some (Complex.log (((x : ℝ) : ℂ) +
        Complex.I * ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ))) :=
    eval?_arccosTermℂ_lift hxlo hxhi
  -- The arccos witness value's imaginary part is Real.arccos x
  set zArc : ℂ := Complex.log (((x : ℝ) : ℂ) +
    Complex.I * ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ)) with hzArc_def
  have h_zArc_im : zArc.im = Real.arccos x := by
    obtain ⟨vc, hvc_eval, hvc_im⟩ := arccos_im_bridge hxlo hxhi
    have h_eq : some zArc = some vc := by
      rw [← h_arc]; exact hvc_eval
    have h_zArc_eq : zArc = vc := (Option.some.injEq _ _).mp h_eq
    rw [h_zArc_eq]; exact hvc_im
  -- Apply mkSubℂ
  have h_logI_ne : Complex.log Complex.I ≠ 0 := by
    intro h
    have : (Complex.log Complex.I).im = 0 := by rw [h]; simp
    rw [h_logI_im] at this
    linarith [Real.pi_pos]
  have h_logI_arg : Complex.arg (Complex.log Complex.I) < Real.pi := by
    rw [Complex.log_I]
    -- arg (↑π / 2 * I) = π/2 since π/2 > 0
    have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
    have h_pi2_pos : (0 : ℝ) < Real.pi / 2 := by linarith
    rw [show ((Real.pi : ℝ) : ℂ) / 2 * Complex.I =
            (((Real.pi / 2 : ℝ)) : ℂ) * Complex.I from by push_cast; ring]
    rw [Complex.arg_real_mul Complex.I h_pi2_pos, Complex.arg_I]
    linarith
  -- arccos x ∈ (0, π) for x ∈ (-1, 1) strict
  have h_arccos_hi : Real.arccos x < Real.pi := by
    have h1 : Real.arccos x ≠ Real.pi := by
      intro h
      have hcos := Real.cos_arccos (by linarith : -1 ≤ x) (by linarith : x ≤ 1)
      rw [h, Real.cos_pi] at hcos
      linarith
    have h2 : Real.arccos x ≤ Real.pi := Real.arccos_le_pi x
    exact lt_of_le_of_ne h2 h1
  have h_zArc_im_lo : -Real.pi < zArc.im := by
    rw [h_zArc_im]
    linarith [Real.pi_pos, Real.arccos_nonneg x]
  have h_zArc_im_hi : zArc.im ≤ Real.pi := by
    rw [h_zArc_im]; exact h_arccos_hi.le
  have h_sub : (mkSubℂ (mkLogℂ iTermPubℂ) arccosTermℂ).eval? env =
      some (Complex.log Complex.I - zArc) :=
    eval?_mkSubℂ h_logI h_arc h_logI_ne h_logI_arg h_zArc_im_lo h_zArc_im_hi
  refine ⟨Complex.log Complex.I - zArc, h_sub, ?_⟩
  rw [Complex.sub_im, h_logI_im, h_zArc_im,
      Real.arcsin_eq_pi_div_two_sub_arccos]

/-! ## §A.3 — literal `EMLTermℂ` witness for `Real.tan` (narrowed `(0, π/2)`)

GPT Pro's recommended Cayley quotient:

  `q(x) := (exp(2ix) − 1) / (1 + exp(2ix)) = i · tan x`,   `x ∈ (0, π/2)`.

The witness is `mkDivℂ (mkSubℂ E2 .one) (mkAddℂ .one E2)` with
`E2 := mkExpℂ (mkMulℂ iTermPubℂ (mkMulℂ twoPubℂ (.var 0)))`. Since the
result is purely imaginary `i · tan x`, `(eval).im = tan x`. -/

/-- Helper: `ADDsafeℂ (log r₁) (log r₂)` for two positive real values. -/
private lemma addsafe_logPos_logPos {r1 r2 : ℝ} (hr1 : 0 < r1) (hr2 : 0 < r2) :
    ADDsafeℂ (Complex.log ((r1 : ℝ) : ℂ)) (Complex.log ((r2 : ℝ) : ℂ)) := by
  rw [(Complex.ofReal_log hr1.le).symm, (Complex.ofReal_log hr2.le).symm]
  apply addsafe_ofReal_left
  · simp; linarith [Real.pi_pos]
  · simp; linarith [Real.pi_pos]
  · simp; linarith [Real.pi_pos]
  · simp; linarith [Real.pi_pos]

/-- The tan witness term — Pro's Cayley quotient. -/
noncomputable def tanCoreTermℂ : EMLTermℂ :=
  let twoX := mkMulℂ twoPubℂ (.var 0)
  let I2x  := mkMulℂ iTermPubℂ twoX
  let E2   := mkExpℂ I2x
  mkDivℂ (mkSubℂ E2 .one) (mkAddℂ .one E2)

/-- For `0 < x < π/2`, `tanCoreTermℂ` evaluates to the Cayley quotient. -/
lemma eval?_tanCoreTermℂ_lift {x : ℝ} (hx_pos : 0 < x) (hx_lt : x < Real.pi / 2) :
    tanCoreTermℂ.eval?
        (fun n => if n = 0 then ((x : ℝ) : ℂ) else 0) =
      some ((Complex.exp (((2 * x : ℝ) : ℂ) * Complex.I) - 1) /
            (1 + Complex.exp (((2 * x : ℝ) : ℂ) * Complex.I))) := by
  unfold tanCoreTermℂ
  set env : Nat → ℂ := fun n => if n = 0 then ((x : ℝ) : ℂ) else 0 with henv
  have h_2x_pos : 0 < 2 * x := by linarith
  have h_2x_lt_pi : 2 * x < Real.pi := by linarith
  have hVar : (EMLTermℂ.var 0).eval? env = some ((x : ℝ) : ℂ) := by
    show some (env 0) = _; simp [henv]
  have hTwo : twoPubℂ.eval? env = some (2 : ℂ) := eval?_twoPubℂ env
  have hI : iTermPubℂ.eval? env = some Complex.I := eval?_iTermPubℂ env
  have hX_ne : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx_pos.ne'
  have h2_arg : Complex.arg (2 : ℂ) < Real.pi := by
    rw [show (2 : ℂ) = (((2 : ℝ)) : ℂ) from by push_cast; rfl,
        Complex.arg_ofReal_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.pi_pos
  have hX_arg : Complex.arg ((x : ℝ) : ℂ) < Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx_pos.le]; exact Real.pi_pos
  have hcast2 : Complex.log (2 : ℂ) = Complex.log (((2 : ℝ)) : ℂ) := by
    show Complex.log _ = Complex.log _
    push_cast
    rfl
  have hAddSafe2x : ADDsafeℂ (Complex.log (2 : ℂ)) (Complex.log ((x : ℝ) : ℂ)) := by
    rw [hcast2]; exact addsafe_logPos_logPos (by norm_num : (0 : ℝ) < 2) hx_pos
  have hMul_2x : (mkMulℂ twoPubℂ (.var 0)).eval? env = some (2 * ((x : ℝ) : ℂ)) :=
    eval?_mkMulℂ hTwo hVar (by norm_num : (2 : ℂ) ≠ 0) hX_ne h2_arg hX_arg hAddSafe2x
  have h_2x_C_eq : (2 : ℂ) * ((x : ℝ) : ℂ) = (((2 * x : ℝ)) : ℂ) := by push_cast; ring
  rw [h_2x_C_eq] at hMul_2x
  have h_2x_ne : (((2 * x : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast h_2x_pos.ne'
  have h_2x_arg : Complex.arg (((2 * x : ℝ)) : ℂ) < Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg h_2x_pos.le]; exact Real.pi_pos
  have hI_arg : Complex.arg Complex.I < Real.pi := by
    rw [Complex.arg_I]; linarith [Real.pi_pos]
  have hMul_I2x : (mkMulℂ iTermPubℂ (mkMulℂ twoPubℂ (.var 0))).eval? env =
      some (Complex.I * (((2 * x : ℝ)) : ℂ)) :=
    eval?_mkMulℂ hI hMul_2x Complex.I_ne_zero h_2x_ne hI_arg h_2x_arg
      (addsafe_logI_logX h_2x_pos)
  have h_I2x_eq : Complex.I * (((2 * x : ℝ)) : ℂ) = (((2 * x : ℝ)) : ℂ) * Complex.I := by ring
  rw [h_I2x_eq] at hMul_I2x
  have hExp : (mkExpℂ (mkMulℂ iTermPubℂ (mkMulℂ twoPubℂ (.var 0)))).eval? env =
      some (Complex.exp ((((2 * x : ℝ)) : ℂ) * Complex.I)) := eval?_mkExpℂ hMul_I2x
  set E : ℂ := Complex.exp ((((2 * x : ℝ)) : ℂ) * Complex.I) with hE_def
  have hE_re : E.re = Real.cos (2 * x) := by
    rw [hE_def]; exact Complex.exp_ofReal_mul_I_re (2 * x)
  have hE_im : E.im = Real.sin (2 * x) := by
    rw [hE_def]; exact Complex.exp_ofReal_mul_I_im (2 * x)
  have h_sin_2x_pos : 0 < Real.sin (2 * x) :=
    Real.sin_pos_of_pos_of_lt_pi h_2x_pos h_2x_lt_pi
  have h_num_im : (E - 1).im = Real.sin (2 * x) := by
    rw [Complex.sub_im, hE_im]; simp
  have h_denom_im : (1 + E).im = Real.sin (2 * x) := by
    rw [Complex.add_im, hE_im]; simp
  have h_num_ne : E - 1 ≠ 0 := by
    intro h; have := congrArg Complex.im h; rw [h_num_im] at this; simp at this
    linarith
  have h_denom_ne : 1 + E ≠ 0 := by
    intro h; have := congrArg Complex.im h; rw [h_denom_im] at this; simp at this
    linarith
  have h_num_arg : Complex.arg (E - 1) < Real.pi :=
    Complex.arg_lt_pi_iff.mpr (Or.inr (by rw [h_num_im]; exact h_sin_2x_pos.ne'))
  have h_denom_arg : Complex.arg (1 + E) < Real.pi :=
    Complex.arg_lt_pi_iff.mpr (Or.inr (by rw [h_denom_im]; exact h_sin_2x_pos.ne'))
  have h_E_arg : Complex.arg E < Real.pi :=
    Complex.arg_lt_pi_iff.mpr (Or.inr (by rw [hE_im]; exact h_sin_2x_pos.ne'))
  have h_one_im : (1 : ℂ).im = 0 := by simp
  have hSub_num : (mkSubℂ (mkExpℂ (mkMulℂ iTermPubℂ (mkMulℂ twoPubℂ (.var 0))))
                          .one).eval? env = some (E - 1) :=
    eval?_mkSubℂ hExp (EMLTermℂ.eval?_one env) (Complex.exp_ne_zero _) h_E_arg
      (by rw [h_one_im]; linarith [Real.pi_pos])
      (by rw [h_one_im]; linarith [Real.pi_pos])
  have hE_im_le : E.im ≤ Real.pi := by
    rw [hE_im]; linarith [Real.sin_le_one (2 * x), Real.pi_gt_three]
  have hE_im_ge : -Real.pi < E.im := by
    rw [hE_im]; linarith [Real.neg_one_le_sin (2 * x), Real.pi_gt_three]
  have hAddSafe_one_E : ADDsafeℂ (1 : ℂ) E := by
    have h_one_eq : (1 : ℂ) = (((1 : ℝ)) : ℂ) := by push_cast; rfl
    rw [h_one_eq]
    apply addsafe_ofReal_left hE_im_ge hE_im_le
    · rw [hE_im]; linarith [Real.sin_le_one (2 * x), Real.pi_gt_three]
    · rw [hE_im]; linarith [Real.neg_one_le_sin (2 * x), Real.pi_gt_three]
  have hAdd_denom : (mkAddℂ .one (mkExpℂ (mkMulℂ iTermPubℂ
                          (mkMulℂ twoPubℂ (.var 0))))).eval? env = some (1 + E) :=
    eval?_mkAddℂ (EMLTermℂ.eval?_one env) hExp hAddSafe_one_E
  have h_arg_num_ne_zero : Complex.arg (E - 1) ≠ 0 := by
    intro h
    have heq := Complex.arg_eq_zero_iff.mp h
    rw [h_num_im] at heq; linarith [heq.2]
  have h_log_num_ne : Complex.log (E - 1) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    rw [Complex.log_im] at hi; simp at hi
    exact h_arg_num_ne_zero hi
  have h_log_num_im_pos : 0 < (Complex.log (E - 1)).im := by
    rw [Complex.log_im]
    rcases lt_trichotomy (Complex.arg (E - 1)) 0 with h_neg | h_zero | h_pos
    · exfalso
      have := Complex.arg_neg_iff.mp h_neg
      rw [h_num_im] at this; linarith
    · exfalso; exact h_arg_num_ne_zero h_zero
    · exact h_pos
  have h_arg_log_num_lt_pi : Complex.arg (Complex.log (E - 1)) < Real.pi :=
    Complex.arg_lt_pi_iff.mpr (Or.inr h_log_num_im_pos.ne')
  have h_log_denom_im_lo : -Real.pi < (Complex.log (1 + E)).im := by
    rw [Complex.log_im]; linarith [Complex.neg_pi_lt_arg (1 + E)]
  have h_log_denom_im_hi : (Complex.log (1 + E)).im ≤ Real.pi := by
    rw [Complex.log_im]; exact Complex.arg_le_pi (1 + E)
  exact eval?_mkDivℂ hSub_num hAdd_denom h_num_ne h_denom_ne h_num_arg h_denom_arg
    h_log_num_ne h_arg_log_num_lt_pi h_log_denom_im_lo h_log_denom_im_hi

/-- Cayley quotient's imaginary part = `Real.tan x` (via `Complex.div_im`). -/
lemma cayley_quotient_im {x : ℝ} (hx_pos : 0 < x) (hx_lt : x < Real.pi / 2) :
    ((Complex.exp (((2 * x : ℝ) : ℂ) * Complex.I) - 1) /
     (1 + Complex.exp (((2 * x : ℝ) : ℂ) * Complex.I))).im = Real.tan x := by
  set E : ℂ := Complex.exp ((((2 * x : ℝ)) : ℂ) * Complex.I)
  have hE_re : E.re = Real.cos (2 * x) := Complex.exp_ofReal_mul_I_re (2 * x)
  have hE_im : E.im = Real.sin (2 * x) := Complex.exp_ofReal_mul_I_im (2 * x)
  have h_cos_pos : 0 < Real.cos x :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hx_lt⟩
  have h_cos_ne : Real.cos x ≠ 0 := h_cos_pos.ne'
  have h_num_im : (E - 1).im = Real.sin (2 * x) := by rw [Complex.sub_im, hE_im]; simp
  have h_num_re : (E - 1).re = Real.cos (2 * x) - 1 := by rw [Complex.sub_re, hE_re]; simp
  have h_denom_im : (1 + E).im = Real.sin (2 * x) := by rw [Complex.add_im, hE_im]; simp
  have h_denom_re : (1 + E).re = 1 + Real.cos (2 * x) := by rw [Complex.add_re, hE_re]; simp
  rw [Complex.div_im]
  rw [h_num_im, h_num_re, h_denom_im, h_denom_re]
  rw [Complex.normSq_apply, h_denom_re, h_denom_im]
  rw [Real.tan_eq_sin_div_cos, Real.sin_two_mul, Real.cos_two_mul]
  have hpyt : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have h_denom_simpl :
      (1 + (2 * Real.cos x ^ 2 - 1)) * (1 + (2 * Real.cos x ^ 2 - 1))
      + 2 * Real.sin x * Real.cos x * (2 * Real.sin x * Real.cos x)
      = 4 * Real.cos x ^ 2 := by
    nlinarith [hpyt, sq_nonneg (Real.sin x), sq_nonneg (Real.cos x)]
  rw [h_denom_simpl]
  field_simp
  nlinarith [hpyt, sq_nonneg (Real.sin x), sq_nonneg (Real.cos x),
             sq_nonneg (Real.sin x - Real.cos x),
             sq_nonneg (Real.sin x + Real.cos x),
             mul_self_nonneg (Real.sin x * Real.cos x)]

/-- Bridge: `(tanCoreTermℂ.eval?).im = Real.tan x` for `0 < x < π/2`. -/
theorem tan_im_bridge {x : ℝ} (hx_pos : 0 < x) (hx_lt : x < Real.pi / 2) :
    ∃ vc : ℂ,
      tanCoreTermℂ.eval? (fun n => if n = 0 then ((x : ℝ) : ℂ) else 0) = some vc
        ∧ vc.im = Real.tan x := by
  refine ⟨(Complex.exp (((2 * x : ℝ) : ℂ) * Complex.I) - 1) /
            (1 + Complex.exp (((2 * x : ℝ) : ℂ) * Complex.I)),
    eval?_tanCoreTermℂ_lift hx_pos hx_lt,
    cayley_quotient_im hx_pos hx_lt⟩

/-! ## §A.3b — `tanCoreTermℂ_neg`: tan witness on `(-π/2, 0)`

For `x ∈ (-π/2, 0)`, the swap-numerator Cayley quotient gives `i · tan x`
directly:

  `(1 − exp(−2ix)) / (1 + exp(−2ix)) = i · tan x`,

since `(1 − E_neg)/(1 + E_neg) = −(E_neg − 1)/(1 + E_neg) = −(i · tan(−x))
= i · tan x` by `tan` being odd. The witness shape is parallel to
`tanCoreTermℂ` but uses `negVarTermℂ` for `(.var 0)` and reverses the
numerator subtraction. -/

/-- The negative-side tan witness, sealed on `(-π/2, 0)`. -/
noncomputable def tanCoreTermℂ_neg : EMLTermℂ :=
  let twoNegX := mkMulℂ twoPubℂ negVarTermℂ
  let I2x_neg := mkMulℂ iTermPubℂ twoNegX
  let E2_neg  := mkExpℂ I2x_neg
  mkDivℂ (mkSubℂ .one E2_neg) (mkAddℂ .one E2_neg)

/-- For `-π/2 < x < 0`, `tanCoreTermℂ_neg` evaluates to the swap-numerator
Cayley quotient. -/
lemma eval?_tanCoreTermℂ_neg_lift {x : ℝ}
    (hx_neg : x < 0) (hx_lt : -Real.pi / 2 < x) :
    tanCoreTermℂ_neg.eval?
        (fun n => if n = 0 then ((x : ℝ) : ℂ) else 0) =
      some ((1 - Complex.exp (((2 * (-x) : ℝ) : ℂ) * Complex.I)) /
            (1 + Complex.exp (((2 * (-x) : ℝ) : ℂ) * Complex.I))) := by
  unfold tanCoreTermℂ_neg
  set env : Nat → ℂ := fun n => if n = 0 then ((x : ℝ) : ℂ) else 0 with henv
  have h_neg_pos : 0 < -x := by linarith
  have h_2neg_pos : 0 < 2 * (-x) := by linarith
  have h_2neg_lt_pi : 2 * (-x) < Real.pi := by
    have : -x < Real.pi / 2 := by linarith
    linarith
  -- negVarTermℂ.eval = some ((-x : ℝ) : ℂ)
  have hNeg : negVarTermℂ.eval? env = some (((-x : ℝ)) : ℂ) :=
    eval?_negVarTermℂ_lift (x := x)
  have hTwo : twoPubℂ.eval? env = some (2 : ℂ) := eval?_twoPubℂ env
  have hI : iTermPubℂ.eval? env = some Complex.I := eval?_iTermPubℂ env
  have h_negx_ne : (((-x : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast h_neg_pos.ne'
  have h2_arg : Complex.arg (2 : ℂ) < Real.pi := by
    rw [show (2 : ℂ) = (((2 : ℝ)) : ℂ) from by norm_num,
        Complex.arg_ofReal_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.pi_pos
  have h_negx_arg : Complex.arg (((-x : ℝ)) : ℂ) < Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg h_neg_pos.le]; exact Real.pi_pos
  have hcast2 : Complex.log (2 : ℂ) = Complex.log (((2 : ℝ)) : ℂ) := by
    show Complex.log _ = Complex.log _; push_cast; rfl
  have hAddSafe2neg : ADDsafeℂ (Complex.log (2 : ℂ))
      (Complex.log (((-x : ℝ)) : ℂ)) := by
    rw [hcast2]; exact addsafe_logPos_logPos (by norm_num : (0 : ℝ) < 2) h_neg_pos
  have hMul_2neg : (mkMulℂ twoPubℂ negVarTermℂ).eval? env =
      some (2 * (((-x : ℝ)) : ℂ)) :=
    eval?_mkMulℂ hTwo hNeg (by norm_num : (2 : ℂ) ≠ 0) h_negx_ne h2_arg h_negx_arg
      hAddSafe2neg
  have h_2neg_C_eq : (2 : ℂ) * (((-x : ℝ)) : ℂ) = (((2 * (-x) : ℝ)) : ℂ) := by
    push_cast; ring
  rw [h_2neg_C_eq] at hMul_2neg
  have h_2neg_ne_C : (((2 * (-x) : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast h_2neg_pos.ne'
  have h_2neg_arg_C : Complex.arg (((2 * (-x) : ℝ)) : ℂ) < Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg h_2neg_pos.le]; exact Real.pi_pos
  have hI_arg : Complex.arg Complex.I < Real.pi := by
    rw [Complex.arg_I]; linarith [Real.pi_pos]
  have hMul_I2neg : (mkMulℂ iTermPubℂ (mkMulℂ twoPubℂ negVarTermℂ)).eval? env =
      some (Complex.I * (((2 * (-x) : ℝ)) : ℂ)) :=
    eval?_mkMulℂ hI hMul_2neg Complex.I_ne_zero h_2neg_ne_C hI_arg h_2neg_arg_C
      (addsafe_logI_logX h_2neg_pos)
  have h_I2neg_eq : Complex.I * (((2 * (-x) : ℝ)) : ℂ) =
      (((2 * (-x) : ℝ)) : ℂ) * Complex.I := by ring
  rw [h_I2neg_eq] at hMul_I2neg
  have hExp : (mkExpℂ (mkMulℂ iTermPubℂ (mkMulℂ twoPubℂ negVarTermℂ))).eval? env =
      some (Complex.exp ((((2 * (-x) : ℝ)) : ℂ) * Complex.I)) :=
    eval?_mkExpℂ hMul_I2neg
  set E_neg : ℂ := Complex.exp ((((2 * (-x) : ℝ)) : ℂ) * Complex.I) with hE_neg_def
  have hE_neg_re : E_neg.re = Real.cos (2 * (-x)) := by
    rw [hE_neg_def]; exact Complex.exp_ofReal_mul_I_re (2 * (-x))
  have hE_neg_im : E_neg.im = Real.sin (2 * (-x)) := by
    rw [hE_neg_def]; exact Complex.exp_ofReal_mul_I_im (2 * (-x))
  have h_sin_2neg_pos : 0 < Real.sin (2 * (-x)) :=
    Real.sin_pos_of_pos_of_lt_pi h_2neg_pos h_2neg_lt_pi
  -- 1 - E_neg
  have h_num_im : ((1 : ℂ) - E_neg).im = -Real.sin (2 * (-x)) := by
    rw [Complex.sub_im, hE_neg_im]; simp
  have h_denom_im : ((1 : ℂ) + E_neg).im = Real.sin (2 * (-x)) := by
    rw [Complex.add_im, hE_neg_im]; simp
  have h_num_ne : (1 : ℂ) - E_neg ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    rw [h_num_im, Complex.zero_im] at him
    have : Real.sin (2 * (-x)) = 0 := by linarith
    linarith [h_sin_2neg_pos]
  have h_denom_ne : (1 : ℂ) + E_neg ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    rw [h_denom_im, Complex.zero_im] at him
    linarith [h_sin_2neg_pos]
  -- mkSubℂ .one E2_neg = 1 - E_neg. Constraint on B: vb.im ∈ (-π, π].
  have h_E_neg_im_lo : -Real.pi < E_neg.im := by
    rw [hE_neg_im]
    linarith [Real.neg_one_le_sin (2 * (-x)), Real.pi_gt_three]
  have h_E_neg_im_hi : E_neg.im ≤ Real.pi := by
    rw [hE_neg_im]; linarith [Real.sin_le_one (2 * (-x)), Real.pi_gt_three]
  have h_one_arg : Complex.arg (1 : ℂ) < Real.pi := by
    rw [Complex.arg_one]; linarith [Real.pi_pos]
  have hSub_num : (mkSubℂ .one (mkExpℂ (mkMulℂ iTermPubℂ
                          (mkMulℂ twoPubℂ negVarTermℂ)))).eval? env =
      some ((1 : ℂ) - E_neg) :=
    eval?_mkSubℂ (EMLTermℂ.eval?_one env) hExp one_ne_zero h_one_arg
      h_E_neg_im_lo h_E_neg_im_hi
  -- mkAddℂ .one E2_neg = 1 + E_neg
  have hAddSafe_one_Eneg : ADDsafeℂ (1 : ℂ) E_neg := by
    have h_one_eq : (1 : ℂ) = (((1 : ℝ)) : ℂ) := by push_cast; rfl
    rw [h_one_eq]
    apply addsafe_ofReal_left h_E_neg_im_lo h_E_neg_im_hi
    · rw [hE_neg_im]; linarith [Real.sin_le_one (2 * (-x)), Real.pi_gt_three]
    · rw [hE_neg_im]; linarith [Real.neg_one_le_sin (2 * (-x)), Real.pi_gt_three]
  have hAdd_denom : (mkAddℂ .one (mkExpℂ (mkMulℂ iTermPubℂ
                          (mkMulℂ twoPubℂ negVarTermℂ)))).eval? env =
      some ((1 : ℂ) + E_neg) :=
    eval?_mkAddℂ (EMLTermℂ.eval?_one env) hExp hAddSafe_one_Eneg
  -- mkDivℂ constraints
  have h_num_arg : Complex.arg ((1 : ℂ) - E_neg) < Real.pi :=
    Complex.arg_lt_pi_iff.mpr (Or.inr (by rw [h_num_im]; linarith))
  have h_denom_arg : Complex.arg ((1 : ℂ) + E_neg) < Real.pi :=
    Complex.arg_lt_pi_iff.mpr (Or.inr (by rw [h_denom_im]; linarith))
  -- log(num).im < 0, so arg(log(num)) < π and ≠ 0
  have h_arg_num_ne_zero : Complex.arg ((1 : ℂ) - E_neg) ≠ 0 := by
    intro h
    have heq := Complex.arg_eq_zero_iff.mp h
    rw [h_num_im] at heq; linarith [heq.2]
  have h_log_num_ne : Complex.log ((1 : ℂ) - E_neg) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    rw [Complex.log_im] at hi; simp at hi
    exact h_arg_num_ne_zero hi
  have h_log_num_arg_lt_pi : Complex.arg (Complex.log ((1 : ℂ) - E_neg)) < Real.pi := by
    -- arg of log(1 - E_neg). log_im = arg(1 - E_neg) which is negative (since (1-E_neg).im < 0)
    -- so log(1 - E_neg) has negative imaginary part, putting it in lower half, arg ∈ (-π, 0).
    apply Complex.arg_lt_pi_iff.mpr
    right
    rw [Complex.log_im]
    -- arg(1 - E_neg) ≠ 0 because (1 - E_neg).im < 0
    have : Complex.arg ((1 : ℂ) - E_neg) < 0 := by
      apply Complex.arg_neg_iff.mpr
      rw [h_num_im]; linarith
    exact this.ne
  have h_log_denom_im_lo : -Real.pi < (Complex.log ((1 : ℂ) + E_neg)).im := by
    rw [Complex.log_im]; linarith [Complex.neg_pi_lt_arg ((1 : ℂ) + E_neg)]
  have h_log_denom_im_hi : (Complex.log ((1 : ℂ) + E_neg)).im ≤ Real.pi := by
    rw [Complex.log_im]; exact Complex.arg_le_pi ((1 : ℂ) + E_neg)
  exact eval?_mkDivℂ hSub_num hAdd_denom h_num_ne h_denom_ne h_num_arg h_denom_arg
    h_log_num_ne h_log_num_arg_lt_pi h_log_denom_im_lo h_log_denom_im_hi

/-- Bridge: imaginary part of the swap-numerator Cayley quotient evaluates
to `Real.tan x` for `x ∈ (-π/2, 0)`. -/
lemma cayley_quotient_im_neg {x : ℝ}
    (hx_neg : x < 0) (hx_lt : -Real.pi / 2 < x) :
    ((1 - Complex.exp (((2 * (-x) : ℝ) : ℂ) * Complex.I)) /
     (1 + Complex.exp (((2 * (-x) : ℝ) : ℂ) * Complex.I))).im = Real.tan x := by
  -- Reduce to existing positive-side bridge: (1 - E_neg)/(1 + E_neg) =
  -- −((E_neg − 1)/(1 + E_neg)) = −(i · tan(−x)) = i · tan(x), so .im = tan x.
  have h_neg_pos : 0 < -x := by linarith
  have h_neg_lt : -x < Real.pi / 2 := by linarith
  have h_pos_form := cayley_quotient_im h_neg_pos h_neg_lt
  -- The positive-side: ((exp(2(-x)*I) - 1)/(1 + exp(2(-x)*I))).im = tan(-x)
  set E_neg : ℂ := Complex.exp ((((2 * (-x) : ℝ)) : ℂ) * Complex.I)
  -- (1 - E_neg) / (1 + E_neg) = -(E_neg - 1) / (1 + E_neg)
  -- = -((E_neg - 1) / (1 + E_neg)), so .im = -tan(-x) = tan x.
  rw [show ((1 : ℂ) - E_neg) / (1 + E_neg) =
          -((E_neg - 1) / (1 + E_neg)) from by
        rw [show (1 : ℂ) - E_neg = -(E_neg - 1) from by ring, neg_div]]
  rw [Complex.neg_im, h_pos_form, Real.tan_neg]
  ring

/-- Bridge: `(tanCoreTermℂ_neg.eval?).im = Real.tan x` for `-π/2 < x < 0`. -/
theorem tan_im_bridge_neg {x : ℝ} (hx_neg : x < 0) (hx_lt : -Real.pi / 2 < x) :
    ∃ vc : ℂ,
      tanCoreTermℂ_neg.eval? (fun n => if n = 0 then ((x : ℝ) : ℂ) else 0)
        = some vc ∧ vc.im = Real.tan x := by
  refine ⟨(1 - Complex.exp (((2 * (-x) : ℝ) : ℂ) * Complex.I)) /
            (1 + Complex.exp (((2 * (-x) : ℝ) : ℂ) * Complex.I)),
    eval?_tanCoreTermℂ_neg_lift hx_neg hx_lt,
    cayley_quotient_im_neg hx_neg hx_lt⟩

end EML
