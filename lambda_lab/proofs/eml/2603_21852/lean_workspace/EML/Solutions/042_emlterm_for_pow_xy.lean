import Mathlib

namespace EML

inductive EMLTerm₂ : Type
  | one : EMLTerm₂
  | varX : EMLTerm₂
  | varY : EMLTerm₂
  | eml : EMLTerm₂ → EMLTerm₂ → EMLTerm₂
  deriving Repr

noncomputable def EMLTerm₂.eval (x y : ℝ) : EMLTerm₂ → ℝ
  | .one => 1
  | .varX => x
  | .varY => y
  | .eml t u => Real.exp (EMLTerm₂.eval x y t) - Real.log (EMLTerm₂.eval x y u)

-- Helper definitions for building the term
private def Z : EMLTerm₂ := .eml .one (.eml (.eml .one .one) .one)
private def LOG (a : EMLTerm₂) : EMLTerm₂ := .eml Z (.eml (.eml Z a) .one)
private def NEG_LOG (v : EMLTerm₂) (raw : EMLTerm₂) : EMLTerm₂ :=
  .eml (LOG (.eml v raw)) (.eml raw .one)

/-- EML term that computes x^y for x > 0, y > 0.
Key identity: y * log(x) = y * (1/x + log(x)) - y/x,
where both 1/x + log(x) > 0 and 1/x > 0 for x > 0. -/
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

/-
Auxiliary lemmas
-/
private lemma inv_add_log_pos {a : ℝ} (ha : 0 < a) : 0 < a⁻¹ + Real.log a := by
  nlinarith [ inv_pos.2 ha, mul_inv_cancel₀ ha.ne', Real.log_inv a ▸ Real.log_le_sub_one_of_pos ( inv_pos.2 ha ) ]

private lemma eval_Z (x y : ℝ) : EMLTerm₂.eval x y Z = 0 := by
  unfold Z;
  -- By definition of $Z$, we know that $Z = \exp(1) - \log(\exp(\exp(1) - \log(1)))$.
  simp [EMLTerm₂.eval]

private lemma eval_LOG (x y : ℝ) (a : EMLTerm₂) (ha : 0 < EMLTerm₂.eval x y a) :
    EMLTerm₂.eval x y (LOG a) = Real.log (EMLTerm₂.eval x y a) := by
  unfold LOG;
  -- By definition of `LOG`, we know that `EMLTerm₂.eval x y (Z.eml ((Z.eml a).eml EMLTerm₂.one)) = Real.log (EMLTerm₂.eval x y a)`.
  simp [EMLTerm₂.eval]

private lemma eval_NEG_LOG (x y : ℝ) (v raw : EMLTerm₂)
    (hraw : 0 < EMLTerm₂.eval x y raw)
    (hv : EMLTerm₂.eval x y v = Real.log (EMLTerm₂.eval x y raw))
    (_hd : 0 < EMLTerm₂.eval x y raw - EMLTerm₂.eval x y v) :
    EMLTerm₂.eval x y (NEG_LOG v raw) = -(EMLTerm₂.eval x y v) := by
  unfold NEG_LOG;
  unfold LOG; norm_num [ EMLTerm₂.eval ] ;
  rw [ Real.exp_log ] <;> norm_num [ hv ] ; linarith [ Real.exp_log hraw ];
  linarith [ Real.add_one_le_exp ( Real.log ( EMLTerm₂.eval x y raw ) ) ]

private lemma eval_pow_term_eq (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    EMLTerm₂.eval x y pow_term = Real.exp (y * Real.log x) := by
  -- Let's simplify the expression step by step.
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

theorem emlterm2_for_pow_pos :
    ∃ t : EMLTerm₂, ∀ x y : ℝ, 0 < x → 0 < y → EMLTerm₂.eval x y t = x ^ y := by
  exact ⟨pow_term, fun x y hx hy => by
    rw [eval_pow_term_eq x y hx hy]
    rw [Real.rpow_def_of_pos hx]
    ring_nf⟩

end EML
