import Mathlib

namespace EML

/-! # Chunk 039 — `EMLTerm₁` realising `Real.sqrt x` for the full positive domain.

    Strategy: lift chunk 042's `pow_term : EMLTerm₂` (which evaluates to `x^y` for
    `0 < x ∧ 0 < y`) and substitute `varX ↦ var` (the EMLTerm₁ variable) and
    `varY ↦ <closed EMLTerm₁ evaluating to 1/2>`.  Since `√x = x^(1/2)` for
    `x > 0`, this gives a one-variable EML term realising `Real.sqrt` on `(0,∞)`.

    This sidesteps the "x > 1" restriction that the iterated-log construction
    suffered from (because `log(log x)` is junk for `0 < x ≤ 1`). -/

/-! ### One-variable grammar (the public surface). -/

inductive EMLTerm₁ : Type
  | one : EMLTerm₁
  | var : EMLTerm₁
  | eml : EMLTerm₁ → EMLTerm₁ → EMLTerm₁
  deriving Repr

noncomputable def EMLTerm₁.eval (x : ℝ) : EMLTerm₁ → ℝ
  | .one => 1
  | .var => x
  | .eml t u => Real.exp (EMLTerm₁.eval x t) - Real.log (EMLTerm₁.eval x u)

/-! ### Two-variable grammar (used internally to host `pow_term`). -/

inductive EMLTerm₂ : Type
  | one  : EMLTerm₂
  | varX : EMLTerm₂
  | varY : EMLTerm₂
  | eml  : EMLTerm₂ → EMLTerm₂ → EMLTerm₂
  deriving Repr

noncomputable def EMLTerm₂.eval (x y : ℝ) : EMLTerm₂ → ℝ
  | .one      => 1
  | .varX     => x
  | .varY     => y
  | .eml t u  => Real.exp (EMLTerm₂.eval x y t) - Real.log (EMLTerm₂.eval x y u)

/-- `proj t A B` translates an `EMLTerm₂` into an `EMLTerm₁` by replacing
    `varX` with `A` and `varY` with `B`. -/
def proj (t : EMLTerm₂) (A B : EMLTerm₁) : EMLTerm₁ :=
  match t with
  | .one      => .one
  | .varX     => A
  | .varY     => B
  | .eml u v  => .eml (proj u A B) (proj v A B)

lemma eval_proj (x : ℝ) (t : EMLTerm₂) (A B : EMLTerm₁) :
    EMLTerm₁.eval x (proj t A B) =
    EMLTerm₂.eval (EMLTerm₁.eval x A) (EMLTerm₁.eval x B) t := by
  induction t with
  | one => rfl
  | varX => rfl
  | varY => rfl
  | eml u v ihu ihv =>
    show Real.exp (EMLTerm₁.eval x (proj u A B)) -
         Real.log (EMLTerm₁.eval x (proj v A B)) =
         Real.exp (EMLTerm₂.eval (EMLTerm₁.eval x A) (EMLTerm₁.eval x B) u) -
         Real.log (EMLTerm₂.eval (EMLTerm₁.eval x A) (EMLTerm₁.eval x B) v)
    rw [ihu, ihv]

/-! ### chunk 042's `pow_term` lifted in (verbatim). -/

private def Z : EMLTerm₂ := .eml .one (.eml (.eml .one .one) .one)
private def LOG (a : EMLTerm₂) : EMLTerm₂ := .eml Z (.eml (.eml Z a) .one)
private def NEG_LOG (v : EMLTerm₂) (raw : EMLTerm₂) : EMLTerm₂ :=
  .eml (LOG (.eml v raw)) (.eml raw .one)

noncomputable def pow_term : EMLTerm₂ :=
  let logx := LOG .varX
  let logy := LOG .varY
  let neg_logx := NEG_LOG logx .varX
  let neg_logy := NEG_LOG logy .varY
  let inv_y_plus_logy := EMLTerm₂.eml neg_logy (.eml neg_logy .one)
  let log_inv_y_plus_logy := LOG inv_y_plus_logy
  let inv_x_plus_logx := EMLTerm₂.eml neg_logx (.eml neg_logx .one)
  let log_inv_x_plus_logx := LOG inv_x_plus_logx
  let A_arg := EMLTerm₂.eml log_inv_y_plus_logy
    (.eml (.eml neg_logy (.eml log_inv_x_plus_logx .one)) .one)
  let B_arg := EMLTerm₂.eml log_inv_y_plus_logy
    (.eml (.eml neg_logy (.eml neg_logx .one)) .one)
  let A := EMLTerm₂.eml A_arg .one
  let B := EMLTerm₂.eml B_arg .one
  let y_logx := EMLTerm₂.eml (LOG A) (.eml B .one)
  EMLTerm₂.eml y_logx .one

private lemma inv_add_log_pos {a : ℝ} (ha : 0 < a) : 0 < a⁻¹ + Real.log a := by
  nlinarith [ inv_pos.2 ha, mul_inv_cancel₀ ha.ne',
    Real.log_inv a ▸ Real.log_le_sub_one_of_pos ( inv_pos.2 ha ) ]

private lemma eval_Z (x y : ℝ) : EMLTerm₂.eval x y Z = 0 := by
  unfold Z; simp [EMLTerm₂.eval]

private lemma eval_LOG (x y : ℝ) (a : EMLTerm₂) (ha : 0 < EMLTerm₂.eval x y a) :
    EMLTerm₂.eval x y (LOG a) = Real.log (EMLTerm₂.eval x y a) := by
  unfold LOG; simp [EMLTerm₂.eval]

private lemma eval_NEG_LOG (x y : ℝ) (v raw : EMLTerm₂)
    (hraw : 0 < EMLTerm₂.eval x y raw)
    (hv : EMLTerm₂.eval x y v = Real.log (EMLTerm₂.eval x y raw))
    (_hd : 0 < EMLTerm₂.eval x y raw - EMLTerm₂.eval x y v) :
    EMLTerm₂.eval x y (NEG_LOG v raw) = -(EMLTerm₂.eval x y v) := by
  unfold NEG_LOG; unfold LOG; norm_num [EMLTerm₂.eval]
  rw [Real.exp_log] <;> norm_num [hv]
  · linarith [Real.exp_log hraw]
  · linarith [Real.add_one_le_exp (Real.log (EMLTerm₂.eval x y raw))]

private lemma eval_pow_term_eq (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    EMLTerm₂.eval x y pow_term = Real.exp (y * Real.log x) := by
  have h1 : EMLTerm₂.eval x y (LOG .varX) = Real.log x := by
    exact eval_LOG x y _ hx
  have h2 : EMLTerm₂.eval x y (LOG .varY) = Real.log y := by
    exact eval_LOG x y _ hy
  have h3 : EMLTerm₂.eval x y (NEG_LOG (LOG .varX) .varX) = -Real.log x := by
    rw [ ← h1 ];
    apply_rules [ eval_NEG_LOG ];
    exact sub_pos_of_lt ( by linarith [ Real.log_le_sub_one_of_pos hx, show EMLTerm₂.eval x y EMLTerm₂.varX = x from rfl ] )
  have h4 : EMLTerm₂.eval x y (NEG_LOG (LOG .varY) .varY) = -Real.log y := by
    rw [ ← h2 ];
    apply_rules [ eval_NEG_LOG ];
    exact sub_pos_of_lt ( by linarith [ Real.log_le_sub_one_of_pos hy, show EMLTerm₂.eval x y EMLTerm₂.varY = y from rfl ] );
  unfold pow_term; simp +decide [ *, EMLTerm₂.eval ] ; ring;
  simp +decide [ *, EMLTerm₂.eval, LOG ] at *;
  norm_num [ Real.exp_add, Real.exp_sub, Real.exp_neg, Real.exp_log hx, Real.exp_log hy ] ; ring;
  rw [ Real.exp_log ( by linarith [ inv_pos.2 hy, Real.log_inv y ▸ Real.log_le_sub_one_of_pos ( inv_pos.2 hy ) ] ), Real.exp_log ( by linarith [ inv_pos.2 hx, Real.log_inv x ▸ Real.log_le_sub_one_of_pos ( inv_pos.2 hx ) ] ) ] ; norm_num [ Real.exp_ne_zero, hx.ne', hy.ne' ] ; ring;
  norm_num [ Real.exp_add, Real.exp_log hy, mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( Real.exp_pos _ ) ]

/-! ### A closed `EMLTerm₁` evaluating to `1/2` (chunk 033 trick). -/

private def Z₁ : EMLTerm₁ := .eml .one (.eml (.eml .one .one) .one)
private def Lg₁ (T : EMLTerm₁) : EMLTerm₁ := .eml Z₁ (.eml (.eml Z₁ T) .one)
private def e1₁ : EMLTerm₁ := .eml .one (.eml .one .one)
private def log_e1₁ : EMLTerm₁ := Lg₁ e1₁
private def e2₁ : EMLTerm₁ := .eml log_e1₁ (.eml .one .one)
private def exp_e2₁ : EMLTerm₁ := .eml e2₁ .one
private def two₁ : EMLTerm₁ := .eml .one exp_e2₁
private def eml2₁ : EMLTerm₁ := .eml .one two₁
private def log_eml2₁ : EMLTerm₁ := Lg₁ eml2₁
private def neg_log2₁ : EMLTerm₁ := .eml log_eml2₁ (.eml (.eml .one .one) .one)
private def half₁ : EMLTerm₁ := .eml neg_log2₁ .one

private lemma eval_Z₁ (x : ℝ) : EMLTerm₁.eval x Z₁ = 0 := by
  simp [Z₁, EMLTerm₁.eval, Real.log_one, Real.log_exp]

private lemma eval_Lg₁ (x : ℝ) {t : EMLTerm₁} (_ : 0 < EMLTerm₁.eval x t) :
    EMLTerm₁.eval x (Lg₁ t) = Real.log (EMLTerm₁.eval x t) := by
  simp only [Lg₁, EMLTerm₁.eval, eval_Z₁, Real.exp_zero, Real.log_exp,
    Real.log_one, sub_zero]
  ring

private lemma eval_e1₁ (x : ℝ) : EMLTerm₁.eval x e1₁ = Real.exp 1 - 1 := by
  simp [e1₁, EMLTerm₁.eval, Real.log_one, Real.log_exp]

private lemma exp_one_sub_one_pos : (0 : ℝ) < Real.exp 1 - 1 := by
  linarith [Real.add_one_le_exp (1:ℝ)]

private lemma eval_log_e1₁ (x : ℝ) :
    EMLTerm₁.eval x log_e1₁ = Real.log (Real.exp 1 - 1) := by
  simp only [log_e1₁]
  rw [eval_Lg₁ x (by rw [eval_e1₁]; exact exp_one_sub_one_pos), eval_e1₁]

private lemma eval_e2₁ (x : ℝ) : EMLTerm₁.eval x e2₁ = Real.exp 1 - 2 := by
  simp only [e2₁, EMLTerm₁.eval, eval_log_e1₁,
    Real.exp_log exp_one_sub_one_pos, Real.log_one, sub_zero, Real.log_exp]
  ring

private lemma eval_exp_e2₁ (x : ℝ) :
    EMLTerm₁.eval x exp_e2₁ = Real.exp (Real.exp 1 - 2) := by
  simp only [exp_e2₁, EMLTerm₁.eval, eval_e2₁, Real.log_one, sub_zero]

private lemma eval_two₁ (x : ℝ) : EMLTerm₁.eval x two₁ = 2 := by
  simp only [two₁, EMLTerm₁.eval, eval_exp_e2₁, Real.log_exp]; ring

private lemma eval_eml2₁ (x : ℝ) :
    EMLTerm₁.eval x eml2₁ = Real.exp 1 - Real.log 2 := by
  simp only [eml2₁, EMLTerm₁.eval, eval_two₁]

private lemma log_two_le_one : Real.log 2 ≤ 1 := by
  rw [show (1:ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
  exact Real.log_le_log (by norm_num) (by linarith [Real.add_one_le_exp (1:ℝ)])

private lemma exp_one_sub_log_two_pos : (0 : ℝ) < Real.exp 1 - Real.log 2 := by
  linarith [exp_one_sub_one_pos, log_two_le_one]

private lemma eval_log_eml2₁ (x : ℝ) :
    EMLTerm₁.eval x log_eml2₁ = Real.log (Real.exp 1 - Real.log 2) := by
  simp only [log_eml2₁]
  rw [eval_Lg₁ x (by rw [eval_eml2₁]; exact exp_one_sub_log_two_pos),
    eval_eml2₁]

private lemma eval_neg_log2₁ (x : ℝ) :
    EMLTerm₁.eval x neg_log2₁ = -Real.log 2 := by
  simp only [neg_log2₁, EMLTerm₁.eval, eval_log_eml2₁, Real.log_exp,
    Real.exp_log exp_one_sub_log_two_pos, Real.log_one, sub_zero]
  ring

lemma eval_half₁ (x : ℝ) : EMLTerm₁.eval x half₁ = 1 / 2 := by
  simp only [half₁, EMLTerm₁.eval, eval_neg_log2₁, Real.log_one, sub_zero,
    Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
  norm_num

/-! ### The sqrt witness: project `pow_term` with `varX ↦ var`, `varY ↦ half₁`. -/

noncomputable def sqrt_term : EMLTerm₁ := proj pow_term .var half₁

lemma eval_sqrt_term (x : ℝ) (hx : 0 < x) :
    EMLTerm₁.eval x sqrt_term = Real.sqrt x := by
  unfold sqrt_term
  rw [eval_proj]
  -- After projection, eval is at (eval x .var, eval x half₁) = (x, 1/2).
  have hvar : EMLTerm₁.eval x (.var : EMLTerm₁) = x := rfl
  have hhalf : EMLTerm₁.eval x half₁ = 1 / 2 := eval_half₁ x
  rw [hvar, hhalf]
  -- Now reduce pow_term at (x, 1/2) using the chunk-042 evaluator.
  rw [eval_pow_term_eq _ _ hx (by norm_num : (0:ℝ) < 1/2)]
  -- Goal: Real.exp ((1/2) * Real.log x) = Real.sqrt x.
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
  ring_nf

-- ═══════════════════════════════════════════════════════════
-- Main theorem (full positive domain).
-- ═══════════════════════════════════════════════════════════

theorem emlterm1_for_sqrt_x_pos :
    ∃ t : EMLTerm₁, ∀ x : ℝ, 0 < x → EMLTerm₁.eval x t = Real.sqrt x :=
  ⟨sqrt_term, fun x hx => eval_sqrt_term x hx⟩

end EML
