import Mathlib

/-!
# Main completeness umbrella for the EML formalization (chunk 045).

This file is **self-contained**: it redefines the three EMLTerm shapes
(`EMLTerm`, `EMLTerm₁`, `EMLTerm₂`) and their `eval` functions, then
inlines the constructive witnesses harvested from chunks 030, 031, 032,
033, 022, 036, 037, 038, 040, 041, 042, and finally bundles them into a
single 11-conjunct existential.

Note: π (chunk 034), i (chunk 035), and √x (chunk 039) are **not** part of
this umbrella — their witnesses require the paper's Supplementary trees,
which are kept as permanent sorries elsewhere.
-/

namespace EML

/-! ## Term shapes -/

/-- Closed EML term (no variables). -/
inductive EMLTerm : Type
  | one : EMLTerm
  | eml : EMLTerm → EMLTerm → EMLTerm
  deriving Repr

/-- Single-variable EML term. -/
inductive EMLTerm₁ : Type
  | one : EMLTerm₁
  | var : EMLTerm₁
  | eml : EMLTerm₁ → EMLTerm₁ → EMLTerm₁
  deriving Repr

/-- Two-variable EML term. -/
inductive EMLTerm₂ : Type
  | one : EMLTerm₂
  | varX : EMLTerm₂
  | varY : EMLTerm₂
  | eml : EMLTerm₂ → EMLTerm₂ → EMLTerm₂
  deriving Repr

noncomputable def EMLTerm.eval : EMLTerm → ℝ
  | .one => 1
  | .eml t u => Real.exp (EMLTerm.eval t) - Real.log (EMLTerm.eval u)

noncomputable def EMLTerm₁.eval (x : ℝ) : EMLTerm₁ → ℝ
  | .one => 1
  | .var => x
  | .eml t u => Real.exp (EMLTerm₁.eval x t) - Real.log (EMLTerm₁.eval x u)

noncomputable def EMLTerm₂.eval (x y : ℝ) : EMLTerm₂ → ℝ
  | .one => 1
  | .varX => x
  | .varY => y
  | .eml t u => Real.exp (EMLTerm₂.eval x y t) - Real.log (EMLTerm₂.eval x y u)

/-! ## Shared positivity helpers -/

private lemma exp_one_sub_one_pos : (0 : ℝ) < Real.exp 1 - 1 := by
  linarith [Real.add_one_le_exp (1 : ℝ)]

private lemma exp_sub_self_pos (x : ℝ) : 0 < Real.exp x - x := by
  linarith [Real.add_one_le_exp x]

private lemma sub_log_pos {x : ℝ} (hx : 0 < x) : 0 < x - Real.log x := by
  linarith [Real.log_le_sub_one_of_pos hx]

private lemma inv_add_log_pos {a : ℝ} (ha : 0 < a) : 0 < a⁻¹ + Real.log a := by
  nlinarith [inv_pos.2 ha, mul_inv_cancel₀ ha.ne',
    Real.log_inv a ▸ Real.log_le_sub_one_of_pos (inv_pos.2 ha)]

/-! ## Conjunct 1 (chunk 030): zero is EML-representable -/

private theorem c030_zero : ∃ t : EMLTerm, EMLTerm.eval t = 0 := by
  refine ⟨.eml .one (.eml (.eml .one .one) .one), ?_⟩
  simp [EMLTerm.eval, Real.log_one, sub_zero, Real.log_exp, sub_self]

/-! ## Conjunct 2 (chunk 031): −1 is EML-representable -/

private theorem c031_neg_one : ∃ t : EMLTerm, EMLTerm.eval t = -1 := by
  refine ⟨.eml (.eml .one (.eml (.eml .one (.eml .one (.eml .one .one))) .one))
            (.eml (.eml .one .one) .one), ?_⟩
  simp [EMLTerm.eval]
  rw [Real.exp_log] <;> linarith [Real.add_one_le_exp 1]

/-! ## Conjunct 3 (chunk 032): 2 is EML-representable -/

private theorem c032_two : ∃ t : EMLTerm, EMLTerm.eval t = 2 := by
  set t2 : EMLTerm := .eml .one .one with ht2
  set t3 : EMLTerm := .eml .one t2 with ht3
  set t4 : EMLTerm := .eml .one t3 with ht4
  set t5 : EMLTerm := .eml t4 .one with ht5
  set t6 : EMLTerm := .eml .one t5 with ht6
  set t7 : EMLTerm := .eml t6 t2 with ht7
  set t8 : EMLTerm := .eml t7 .one with ht8
  refine ⟨.eml .one t8, ?_⟩
  have e2 : EMLTerm.eval t2 = Real.exp 1 := by
    simp [ht2, EMLTerm.eval, Real.log_one]
  have e3 : EMLTerm.eval t3 = Real.exp 1 - 1 := by
    simp [ht3, EMLTerm.eval, e2, Real.log_exp]
  have e4 : EMLTerm.eval t4 = Real.exp 1 - Real.log (Real.exp 1 - 1) := by
    simp [ht4, EMLTerm.eval, e3]
  have e5 : EMLTerm.eval t5 = Real.exp (Real.exp 1 - Real.log (Real.exp 1 - 1)) := by
    simp [ht5, EMLTerm.eval, e4, Real.log_one]
  have e6 : EMLTerm.eval t6 = Real.log (Real.exp 1 - 1) := by
    simp [ht6, EMLTerm.eval, e5, Real.log_exp]
  have e7 : EMLTerm.eval t7 = Real.exp 1 - 2 := by
    simp only [ht7, EMLTerm.eval, e6, e2]
    rw [Real.exp_log exp_one_sub_one_pos]
    linarith [Real.log_exp 1]
  have e8 : EMLTerm.eval t8 = Real.exp (Real.exp 1 - 2) := by
    simp [ht8, EMLTerm.eval, e7, Real.log_one]
  simp only [EMLTerm.eval, e8, Real.log_exp]
  ring

/-! ## Conjunct 4 (chunk 033): 1/2 is EML-representable -/

private theorem c033_half : ∃ t : EMLTerm, EMLTerm.eval t = 1 / 2 := by
  set Z : EMLTerm := .eml .one (.eml (.eml .one .one) .one) with hZ
  let Lg : EMLTerm → EMLTerm := fun t => .eml Z (.eml (.eml Z t) .one)
  set e1 : EMLTerm := .eml .one (.eml .one .one) with he1
  set log_e1 : EMLTerm := Lg e1 with hle1
  set e2 : EMLTerm := .eml log_e1 (.eml .one .one) with he2
  set exp_e2 : EMLTerm := .eml e2 .one with hexpe2
  set two_t : EMLTerm := .eml .one exp_e2 with htwo_t
  set eml2 : EMLTerm := .eml .one two_t with heml2
  set log_eml2 : EMLTerm := Lg eml2 with hle2
  set neg_log2 : EMLTerm := .eml log_eml2 (.eml (.eml .one .one) .one) with hnl2
  set half_term : EMLTerm := .eml neg_log2 .one with hht
  refine ⟨half_term, ?_⟩
  have eval_Z : EMLTerm.eval Z = 0 := by
    simp [hZ, EMLTerm.eval, Real.log_one, Real.log_exp]
  have eval_Lg : ∀ s : EMLTerm, 0 < EMLTerm.eval s →
      EMLTerm.eval (Lg s) = Real.log (EMLTerm.eval s) := by
    intro s _
    show EMLTerm.eval (.eml Z (.eml (.eml Z s) .one)) = _
    simp only [EMLTerm.eval, eval_Z, Real.exp_zero, Real.log_exp, Real.log_one, sub_zero]
    ring
  have eval_e1 : EMLTerm.eval e1 = Real.exp 1 - 1 := by
    simp [he1, EMLTerm.eval, Real.log_one, Real.log_exp]
  have eval_log_e1 : EMLTerm.eval log_e1 = Real.log (Real.exp 1 - 1) := by
    rw [hle1, eval_Lg e1 (by rw [eval_e1]; exact exp_one_sub_one_pos), eval_e1]
  have eval_e2 : EMLTerm.eval e2 = Real.exp 1 - 2 := by
    simp only [he2, EMLTerm.eval, eval_log_e1, Real.exp_log exp_one_sub_one_pos,
      Real.log_one, sub_zero, Real.log_exp]
    ring
  have eval_exp_e2 : EMLTerm.eval exp_e2 = Real.exp (Real.exp 1 - 2) := by
    simp only [hexpe2, EMLTerm.eval, eval_e2, Real.log_one, sub_zero]
  have eval_two : EMLTerm.eval two_t = 2 := by
    simp only [htwo_t, EMLTerm.eval, eval_exp_e2, Real.log_exp]; ring
  have eval_eml2 : EMLTerm.eval eml2 = Real.exp 1 - Real.log 2 := by
    simp only [heml2, EMLTerm.eval, eval_two]
  have log_two_le_one : Real.log 2 ≤ 1 := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
    exact Real.log_le_log (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)])
  have exp_one_sub_log_two_pos : (0 : ℝ) < Real.exp 1 - Real.log 2 := by
    linarith [exp_one_sub_one_pos, log_two_le_one]
  have eval_log_eml2 : EMLTerm.eval log_eml2 = Real.log (Real.exp 1 - Real.log 2) := by
    rw [hle2, eval_Lg eml2 (by rw [eval_eml2]; exact exp_one_sub_log_two_pos), eval_eml2]
  have eval_neg_log2 : EMLTerm.eval neg_log2 = -Real.log 2 := by
    simp only [hnl2, EMLTerm.eval, eval_log_eml2, Real.log_exp,
      Real.exp_log exp_one_sub_log_two_pos, Real.log_one, sub_zero]
    ring
  simp only [hht, EMLTerm.eval, eval_neg_log2, Real.log_one, sub_zero,
    Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-! ## Conjunct 5 (chunk 022): e is EML-representable -/

private theorem c022_e : ∃ t : EMLTerm, EMLTerm.eval t = Real.exp 1 := by
  refine ⟨.eml .one .one, ?_⟩
  simp [EMLTerm.eval, Real.log_one]

/-! ## Conjunct 6 (chunk 036): negation is EML-representable -/

private theorem c036_neg_x :
    ∃ t : EMLTerm₁, ∀ x : ℝ, EMLTerm₁.eval x t = -x := by
  -- Witness: eml (eml one (eml (eml one w) one)) (eml expx one)
  --   where w = eml var (eml var one), expx = eml var one.
  refine ⟨.eml
    (.eml .one (.eml (.eml .one (.eml .var (.eml .var .one))) .one))
    (.eml (.eml .var .one) .one), ?_⟩
  intro x
  -- Step-by-step unfold via simp on EMLTerm₁.eval.
  show Real.exp (EMLTerm₁.eval x
        (.eml .one (.eml (.eml .one (.eml .var (.eml .var .one))) .one))) -
      Real.log (EMLTerm₁.eval x (.eml (.eml .var .one) .one)) = -x
  simp only [EMLTerm₁.eval, Real.log_one, sub_zero, Real.log_exp]
  -- Goal: exp(1 - log(exp(1 - log(exp x - x)))) - exp x = -x  (using log_exp/log_one rewrites)
  -- Actually after simp: exp 1 - (exp 1 - log(exp x - x)) appears and gets log_exp'd.
  rw [show Real.exp 1 - (Real.exp 1 - Real.log (Real.exp x - x)) =
        Real.log (Real.exp x - x) from by ring]
  rw [Real.exp_log (exp_sub_self_pos x)]
  ring

/-! ## Conjunct 7 (chunk 037): reciprocal (positive case) is EML-representable -/

private theorem c037_inv_x :
    ∃ t : EMLTerm₁, ∀ x : ℝ, 0 < x → EMLTerm₁.eval x t = 1 / x := by
  set logTerm : EMLTerm₁ := .eml .one (.eml (.eml .one .var) .one) with hlogTerm
  set xMinusLogTerm : EMLTerm₁ := .eml logTerm .var with hxmlt
  set logXMinusLogTerm : EMLTerm₁ :=
    .eml .one (.eml (.eml .one xMinusLogTerm) .one) with hlxmlt
  set negLogTerm : EMLTerm₁ := .eml logXMinusLogTerm (.eml .var .one) with hnlt
  set invTerm : EMLTerm₁ := .eml negLogTerm .one with hinvT
  refine ⟨invTerm, fun x hx => ?_⟩
  have eval_logTerm : EMLTerm₁.eval x logTerm = Real.log x := by
    simp only [hlogTerm, EMLTerm₁.eval, Real.log_one, sub_zero, Real.log_exp]
    ring
  have eval_xMinusLogTerm : EMLTerm₁.eval x xMinusLogTerm = x - Real.log x := by
    simp only [hxmlt, EMLTerm₁.eval, eval_logTerm, Real.exp_log hx]
  have eval_logXMinusLogTerm :
      EMLTerm₁.eval x logXMinusLogTerm = Real.log (x - Real.log x) := by
    simp only [hlxmlt, EMLTerm₁.eval, eval_xMinusLogTerm,
      Real.log_one, sub_zero, Real.log_exp]
    ring
  have eval_negLogTerm : EMLTerm₁.eval x negLogTerm = -Real.log x := by
    simp only [hnlt, EMLTerm₁.eval, eval_logXMinusLogTerm,
      Real.exp_log (sub_log_pos hx), Real.log_one, sub_zero, Real.log_exp]
    ring
  simp only [hinvT, EMLTerm₁.eval, eval_negLogTerm, Real.log_one, sub_zero]
  rw [Real.exp_neg, Real.exp_log hx, one_div]

/-! ## Conjunct 8 (chunk 038): square (positive case) is EML-representable -/

private theorem c038_sq_x :
    ∃ t : EMLTerm₁, ∀ x : ℝ, 0 < x → EMLTerm₁.eval x t = x ^ 2 := by
  set zeroT : EMLTerm₁ := .eml .one (.eml (.eml .one .one) .one) with hzeroT
  set logT : EMLTerm₁ := .eml zeroT (.eml (.eml zeroT .var) .one) with hlogT
  set xMinusLogT : EMLTerm₁ := .eml logT .var with hxml
  set logXMinusLogT : EMLTerm₁ :=
    .eml zeroT (.eml (.eml zeroT xMinusLogT) .one) with hlxml
  set xMinus2LogT : EMLTerm₁ := .eml logXMinusLogT (.eml logT .one) with hx2l
  set twoLogT : EMLTerm₁ := .eml logT (.eml xMinus2LogT .one) with htl
  set sqT : EMLTerm₁ := .eml twoLogT .one with hsqT
  refine ⟨sqT, fun x hx => ?_⟩
  have eval_zeroT : EMLTerm₁.eval x zeroT = 0 := by
    simp [hzeroT, EMLTerm₁.eval, Real.log_one, Real.log_exp]
  have eval_logT : EMLTerm₁.eval x logT = Real.log x := by
    simp only [hlogT, EMLTerm₁.eval, eval_zeroT, Real.exp_zero, Real.log_one,
      sub_zero, Real.log_exp]
    ring
  have eval_xMinusLogT : EMLTerm₁.eval x xMinusLogT = x - Real.log x := by
    simp only [hxml, EMLTerm₁.eval, eval_logT, Real.exp_log hx]
  have eval_logXMinusLogT :
      EMLTerm₁.eval x logXMinusLogT = Real.log (x - Real.log x) := by
    simp only [hlxml, EMLTerm₁.eval, eval_zeroT, eval_xMinusLogT,
      Real.exp_zero, Real.log_one, sub_zero, Real.log_exp]
    ring
  have eval_xMinus2LogT : EMLTerm₁.eval x xMinus2LogT = x - 2 * Real.log x := by
    simp only [hx2l, EMLTerm₁.eval, eval_logXMinusLogT, eval_logT,
      Real.exp_log (sub_log_pos hx), Real.log_one, sub_zero, Real.log_exp]
    ring
  have eval_twoLogT : EMLTerm₁.eval x twoLogT = 2 * Real.log x := by
    simp only [htl, EMLTerm₁.eval, eval_logT, eval_xMinus2LogT,
      Real.log_one, sub_zero]
    rw [Real.exp_log hx, Real.log_exp]
    ring
  show Real.exp (EMLTerm₁.eval x twoLogT) - Real.log (EMLTerm₁.eval x .one) = x ^ 2
  simp only [EMLTerm₁.eval, eval_twoLogT, Real.log_one, sub_zero]
  -- Goal: Real.exp (2 * Real.log x) = x ^ 2
  rw [show (2 : ℝ) * Real.log x = Real.log x + Real.log x from by ring,
      Real.exp_add, Real.exp_log hx, sq]

/-! ## Conjunct 9 (chunk 040): addition is EML-representable -/

private theorem c040_add_xy :
    ∃ t : EMLTerm₂, ∀ x y : ℝ, EMLTerm₂.eval x y t = x + y := by
  refine ⟨.eml
    (.eml .one (.eml (.eml .one (.eml .varX .one)) .one))
    (.eml
      (.eml (.eml .one (.eml (.eml .one (.eml .varX (.eml .varX .one))) .one))
            (.eml .varY .one))
      .one), ?_⟩
  intro x y
  simp only [EMLTerm₂.eval, Real.log_one, sub_zero, Real.log_exp]
  have h1 : Real.exp 1 - (Real.exp 1 - x) = x := by ring
  have h2 : Real.exp 1 - (Real.exp 1 - Real.log (Real.exp x - x)) =
      Real.log (Real.exp x - x) := by ring
  rw [h1, h2, Real.exp_log (exp_sub_self_pos x)]
  ring

/-! ## Conjunct 10 (chunk 041): multiplication (positive case) is EML-representable -/

private theorem c041_mul_xy :
    ∃ t : EMLTerm₂, ∀ x y : ℝ, 0 < x → 0 < y → EMLTerm₂.eval x y t = x * y := by
  refine ⟨?_, fun x y hx hy => ?_⟩
  · exact .eml (.eml (.eml .one (.eml (.eml .one .varX) .one))
      (.eml (.eml (.eml .one (.eml (.eml .one
        (.eml (.eml .one (.eml (.eml .one .varX) .one))
          (.eml (.eml .one (.eml (.eml .one .varX) .one)) .one))) .one)) .varY) .one)) .one
  · simp only [EMLTerm₂.eval, Real.log_one, sub_zero, Real.log_exp]
    set e := Real.exp 1
    have h1 : e - (e - Real.log x) = Real.log x := by ring
    rw [h1]
    rw [Real.exp_log hx]
    have h3 : e - (e - Real.log (x - Real.log x)) = Real.log (x - Real.log x) := by ring
    rw [h3]
    rw [Real.exp_log (sub_log_pos hx)]
    have h5 : x - (x - Real.log x - Real.log y) = Real.log x + Real.log y := by ring
    rw [h5, Real.exp_add, Real.exp_log hx, Real.exp_log hy]

/-! ## Building blocks for Conjunct 11 (chunk 042) -/

private def pow_Z : EMLTerm₂ := .eml .one (.eml (.eml .one .one) .one)
private def pow_LOG (a : EMLTerm₂) : EMLTerm₂ :=
  .eml pow_Z (.eml (.eml pow_Z a) .one)
private def pow_NEG_LOG (v raw : EMLTerm₂) : EMLTerm₂ :=
  .eml (pow_LOG (.eml v raw)) (.eml raw .one)

private def pow_logx : EMLTerm₂ := pow_LOG .varX
private def pow_logy : EMLTerm₂ := pow_LOG .varY
private def pow_neg_logx : EMLTerm₂ := pow_NEG_LOG pow_logx .varX
private def pow_neg_logy : EMLTerm₂ := pow_NEG_LOG pow_logy .varY
private def pow_inv_y_plus_logy : EMLTerm₂ :=
  .eml pow_neg_logy (.eml pow_neg_logy .one)
private def pow_log_inv_y_plus_logy : EMLTerm₂ := pow_LOG pow_inv_y_plus_logy
private def pow_inv_x_plus_logx : EMLTerm₂ :=
  .eml pow_neg_logx (.eml pow_neg_logx .one)
private def pow_log_inv_x_plus_logx : EMLTerm₂ := pow_LOG pow_inv_x_plus_logx
private def pow_A_arg : EMLTerm₂ := .eml pow_log_inv_y_plus_logy
  (.eml (.eml pow_neg_logy (.eml pow_log_inv_x_plus_logx .one)) .one)
private def pow_B_arg : EMLTerm₂ := .eml pow_log_inv_y_plus_logy
  (.eml (.eml pow_neg_logy (.eml pow_neg_logx .one)) .one)
private def pow_A : EMLTerm₂ := .eml pow_A_arg .one
private def pow_B : EMLTerm₂ := .eml pow_B_arg .one
private def pow_y_logx : EMLTerm₂ := .eml (pow_LOG pow_A) (.eml pow_B .one)
private def pow_term : EMLTerm₂ := .eml pow_y_logx .one

private lemma eval_pow_Z (x y : ℝ) : EMLTerm₂.eval x y pow_Z = 0 := by
  simp [pow_Z, EMLTerm₂.eval, Real.log_one, Real.log_exp]

private lemma eval_pow_LOG (x y : ℝ) (a : EMLTerm₂)
    (_ha : 0 < EMLTerm₂.eval x y a) :
    EMLTerm₂.eval x y (pow_LOG a) = Real.log (EMLTerm₂.eval x y a) := by
  simp only [pow_LOG, EMLTerm₂.eval, eval_pow_Z, Real.exp_zero, Real.log_one,
    sub_zero, Real.log_exp]
  ring

private lemma eval_pow_NEG_LOG (x y : ℝ) (v raw : EMLTerm₂)
    (hraw : 0 < EMLTerm₂.eval x y raw)
    (hv : EMLTerm₂.eval x y v = Real.log (EMLTerm₂.eval x y raw)) :
    EMLTerm₂.eval x y (pow_NEG_LOG v raw) = -(EMLTerm₂.eval x y v) := by
  have h_inner_pos : 0 < EMLTerm₂.eval x y (.eml v raw) := by
    show 0 < Real.exp (EMLTerm₂.eval x y v) - Real.log (EMLTerm₂.eval x y raw)
    rw [hv]
    have : Real.log (EMLTerm₂.eval x y raw) + 1 ≤
        Real.exp (Real.log (EMLTerm₂.eval x y raw)) :=
      Real.add_one_le_exp _
    linarith
  show EMLTerm₂.eval x y (.eml (pow_LOG (.eml v raw)) (.eml raw .one)) = _
  simp only [EMLTerm₂.eval, Real.log_one, sub_zero]
  rw [eval_pow_LOG x y (.eml v raw) h_inner_pos]
  show Real.exp (Real.log (EMLTerm₂.eval x y (.eml v raw))) -
    Real.log (Real.exp (EMLTerm₂.eval x y raw)) = _
  rw [Real.log_exp, Real.exp_log h_inner_pos]
  show (Real.exp (EMLTerm₂.eval x y v) - Real.log (EMLTerm₂.eval x y raw)) -
    EMLTerm₂.eval x y raw = -(EMLTerm₂.eval x y v)
  rw [hv, Real.exp_log hraw]
  ring

private lemma eval_pow_term (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    EMLTerm₂.eval x y pow_term = Real.exp (y * Real.log x) := by
  -- evaluations of building blocks
  have h_var_x : EMLTerm₂.eval x y .varX = x := rfl
  have h_var_y : EMLTerm₂.eval x y .varY = y := rfl
  have h_logx : EMLTerm₂.eval x y pow_logx = Real.log x := by
    show EMLTerm₂.eval x y (pow_LOG .varX) = Real.log x
    rw [eval_pow_LOG x y .varX (h_var_x ▸ hx), h_var_x]
  have h_logy : EMLTerm₂.eval x y pow_logy = Real.log y := by
    show EMLTerm₂.eval x y (pow_LOG .varY) = Real.log y
    rw [eval_pow_LOG x y .varY (h_var_y ▸ hy), h_var_y]
  have h_neg_logx : EMLTerm₂.eval x y pow_neg_logx = -Real.log x := by
    have : EMLTerm₂.eval x y pow_neg_logx = -EMLTerm₂.eval x y pow_logx := by
      simp only [pow_neg_logx]
      exact eval_pow_NEG_LOG x y pow_logx .varX hx h_logx
    rw [this, h_logx]
  have h_neg_logy : EMLTerm₂.eval x y pow_neg_logy = -Real.log y := by
    have : EMLTerm₂.eval x y pow_neg_logy = -EMLTerm₂.eval x y pow_logy := by
      simp only [pow_neg_logy]
      exact eval_pow_NEG_LOG x y pow_logy .varY hy h_logy
    rw [this, h_logy]
  have h_inv_y_plus_logy :
      EMLTerm₂.eval x y pow_inv_y_plus_logy = y⁻¹ + Real.log y := by
    show Real.exp (EMLTerm₂.eval x y pow_neg_logy) -
        Real.log (Real.exp (EMLTerm₂.eval x y pow_neg_logy) - Real.log 1) = _
    rw [Real.log_one, sub_zero, Real.log_exp, h_neg_logy, Real.exp_neg, Real.exp_log hy]
    ring
  have h_inv_x_plus_logx :
      EMLTerm₂.eval x y pow_inv_x_plus_logx = x⁻¹ + Real.log x := by
    show Real.exp (EMLTerm₂.eval x y pow_neg_logx) -
        Real.log (Real.exp (EMLTerm₂.eval x y pow_neg_logx) - Real.log 1) = _
    rw [Real.log_one, sub_zero, Real.log_exp, h_neg_logx, Real.exp_neg, Real.exp_log hx]
    ring
  have h_inv_y_pos : 0 < EMLTerm₂.eval x y pow_inv_y_plus_logy := by
    rw [h_inv_y_plus_logy]; exact inv_add_log_pos hy
  have h_inv_x_pos : 0 < EMLTerm₂.eval x y pow_inv_x_plus_logx := by
    rw [h_inv_x_plus_logx]; exact inv_add_log_pos hx
  have h_log_inv_y :
      EMLTerm₂.eval x y pow_log_inv_y_plus_logy =
        Real.log (y⁻¹ + Real.log y) := by
    simp only [pow_log_inv_y_plus_logy]
    rw [eval_pow_LOG x y pow_inv_y_plus_logy h_inv_y_pos, h_inv_y_plus_logy]
  have h_log_inv_x :
      EMLTerm₂.eval x y pow_log_inv_x_plus_logx =
        Real.log (x⁻¹ + Real.log x) := by
    simp only [pow_log_inv_x_plus_logx]
    rw [eval_pow_LOG x y pow_inv_x_plus_logx h_inv_x_pos, h_inv_x_plus_logx]
  -- inner_y_x := .eml pow_neg_logy (.eml pow_log_inv_x_plus_logx .one)
  --   = exp(-log y) - log(exp(log(x⁻¹ + log x)) - log 1)
  --   = 1/y - log(x⁻¹ + log x)
  have h_xinv_logx_pos : 0 < x⁻¹ + Real.log x := inv_add_log_pos hx
  have h_inner_y_x :
      EMLTerm₂.eval x y (.eml pow_neg_logy (.eml pow_log_inv_x_plus_logx .one)) =
        y⁻¹ - Real.log (x⁻¹ + Real.log x) := by
    show Real.exp (EMLTerm₂.eval x y pow_neg_logy) -
      Real.log (Real.exp (EMLTerm₂.eval x y pow_log_inv_x_plus_logx) -
        Real.log 1) = _
    rw [Real.log_one, sub_zero, Real.log_exp, h_log_inv_x, h_neg_logy,
        Real.exp_neg, Real.exp_log hy]
  have h_A_arg :
      EMLTerm₂.eval x y pow_A_arg = Real.log y + Real.log (x⁻¹ + Real.log x) := by
    show Real.exp (EMLTerm₂.eval x y pow_log_inv_y_plus_logy) -
      Real.log (Real.exp
        (EMLTerm₂.eval x y (.eml pow_neg_logy (.eml pow_log_inv_x_plus_logx .one)))
        - Real.log 1) = _
    rw [Real.log_one, sub_zero, Real.log_exp, h_log_inv_y,
        Real.exp_log (inv_add_log_pos hy), h_inner_y_x]
    ring
  have h_A : EMLTerm₂.eval x y pow_A = y * (x⁻¹ + Real.log x) := by
    show Real.exp (EMLTerm₂.eval x y pow_A_arg) - Real.log 1 = _
    rw [Real.log_one, sub_zero, h_A_arg, Real.exp_add,
        Real.exp_log hy, Real.exp_log h_xinv_logx_pos]
  have h_inner_y_x_2 :
      EMLTerm₂.eval x y (.eml pow_neg_logy (.eml pow_neg_logx .one)) =
        y⁻¹ + Real.log x := by
    show Real.exp (EMLTerm₂.eval x y pow_neg_logy) -
      Real.log (Real.exp (EMLTerm₂.eval x y pow_neg_logx) - Real.log 1) = _
    rw [Real.log_one, sub_zero, Real.log_exp, h_neg_logx, h_neg_logy,
        Real.exp_neg, Real.exp_log hy]
    ring
  have h_B_arg : EMLTerm₂.eval x y pow_B_arg = Real.log y - Real.log x := by
    show Real.exp (EMLTerm₂.eval x y pow_log_inv_y_plus_logy) -
      Real.log (Real.exp
        (EMLTerm₂.eval x y (.eml pow_neg_logy (.eml pow_neg_logx .one)))
        - Real.log 1) = _
    rw [Real.log_one, sub_zero, Real.log_exp, h_log_inv_y,
        Real.exp_log (inv_add_log_pos hy), h_inner_y_x_2]
    ring
  have h_B : EMLTerm₂.eval x y pow_B = y / x := by
    show Real.exp (EMLTerm₂.eval x y pow_B_arg) - Real.log 1 = _
    rw [Real.log_one, sub_zero, h_B_arg, Real.exp_sub,
        Real.exp_log hy, Real.exp_log hx]
  have h_A_pos : 0 < EMLTerm₂.eval x y pow_A := by
    rw [h_A]; exact mul_pos hy h_xinv_logx_pos
  have h_log_A : EMLTerm₂.eval x y (pow_LOG pow_A) =
      Real.log (y * (x⁻¹ + Real.log x)) := by
    rw [eval_pow_LOG x y pow_A h_A_pos, h_A]
  have h_y_logx : EMLTerm₂.eval x y pow_y_logx = y * Real.log x := by
    show Real.exp (EMLTerm₂.eval x y (pow_LOG pow_A)) -
      Real.log (Real.exp (EMLTerm₂.eval x y pow_B) - Real.log 1) = _
    rw [Real.log_one, sub_zero, Real.log_exp, h_log_A, h_B,
        Real.exp_log (mul_pos hy h_xinv_logx_pos)]
    field_simp
    ring
  show Real.exp (EMLTerm₂.eval x y pow_y_logx) - Real.log 1 = _
  rw [Real.log_one, sub_zero, h_y_logx]

/-! ## Conjunct 11 (chunk 042): real power (positive case) is EML-representable -/

private theorem c042_pow_xy :
    ∃ t : EMLTerm₂, ∀ x y : ℝ, 0 < x → 0 < y → EMLTerm₂.eval x y t = x ^ y := by
  refine ⟨pow_term, fun x y hx hy => ?_⟩
  rw [eval_pow_term x y hx hy, Real.rpow_def_of_pos hx]
  ring_nf

/-! ## Umbrella theorem -/

/-- Main completeness umbrella: each of the eleven constructive sub-cases
of the EML decomposition has a witnessing term whose evaluation realises
the target value or function. Conjuncts in order:

1. zero (chunk 030)
2. −1 (chunk 031)
3. 2 (chunk 032)
4. 1/2 (chunk 033)
5. e (chunk 022)
6. negation, x ↦ −x (chunk 036)
7. reciprocal on positives, x ↦ 1/x (chunk 037)
8. square on positives, x ↦ x² (chunk 038)
9. addition, (x,y) ↦ x+y (chunk 040)
10. multiplication on positive quadrant, (x,y) ↦ x·y (chunk 041)
11. real power on positive quadrant, (x,y) ↦ x^y (chunk 042)

NOT included: π (chunk 034), i (chunk 035), √x (chunk 039) — their
constructions require the paper's Supplementary trees and remain
permanent sorries. -/
theorem main_completeness :
    (∃ t : EMLTerm, EMLTerm.eval t = 0) ∧
    (∃ t : EMLTerm, EMLTerm.eval t = -1) ∧
    (∃ t : EMLTerm, EMLTerm.eval t = 2) ∧
    (∃ t : EMLTerm, EMLTerm.eval t = 1 / 2) ∧
    (∃ t : EMLTerm, EMLTerm.eval t = Real.exp 1) ∧
    (∃ t : EMLTerm₁, ∀ x : ℝ, EMLTerm₁.eval x t = -x) ∧
    (∃ t : EMLTerm₁, ∀ x : ℝ, 0 < x → EMLTerm₁.eval x t = 1 / x) ∧
    (∃ t : EMLTerm₁, ∀ x : ℝ, 0 < x → EMLTerm₁.eval x t = x ^ 2) ∧
    (∃ t : EMLTerm₂, ∀ x y : ℝ, EMLTerm₂.eval x y t = x + y) ∧
    (∃ t : EMLTerm₂, ∀ x y : ℝ, 0 < x → 0 < y → EMLTerm₂.eval x y t = x * y) ∧
    (∃ t : EMLTerm₂, ∀ x y : ℝ, 0 < x → 0 < y → EMLTerm₂.eval x y t = x ^ y) :=
  ⟨c030_zero, c031_neg_one, c032_two, c033_half, c022_e,
   c036_neg_x, c037_inv_x, c038_sq_x,
   c040_add_xy, c041_mul_xy, c042_pow_xy⟩

end EML
