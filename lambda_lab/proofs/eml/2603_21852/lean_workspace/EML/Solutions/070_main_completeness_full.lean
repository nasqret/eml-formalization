import Mathlib

/-!
# Main completeness umbrella, Round 2 (chunk 070).

This file is **self-contained**: it redefines the EML term shapes
(`EMLTerm`, `EMLTerm₁`, `EMLTerm₂`) and their `eval` functions, then
inlines the constructive witnesses harvested from the round-1 chunks
(030, 031, 032, 033, 022, 036, 037, 038, 040, 041, 042) plus a
selection of round-2 chunks (050, 051, 052, 055, 056, 057, 058, 060,
069).  Everything is bundled into one big existential.

Conjuncts skipped (with reason):
* 034 (π), 035 (i), 039 (√x): require the paper's Supplementary trees
  (permanent sorries).
* 053 (log_x y): the upstream witness uses `simp +decide` and a
  bespoke `mkDiv` that handles a possibly-negative numerator.  The
  generic `mkDIV` packaged here requires `eval(numerator) > 0`, which
  forces `1 < y` — narrower than the upstream `0 < y`.  Dropped to keep
  the umbrella honest.
* 054 (hypot), 059 (arsinh): rely on √x, hence on 039.
* 061 (artanh): marked `partial` upstream.
* 062 (cos), 063 (sin), 064 (tan), 065 (arctan), 066 (arcsin), 067
  (arccos): live in the COMPLEX `EMLTermℂ₁` grammar, not the real
  `EMLTerm₁` grammar bundled here. Chunks 062 and 063 carry actual
  EMLTermℂ₁ witnesses (sealed via Euler / iπ-shift); chunks 064, 065,
  066, 067 expose closed-form complex-log identities (the math
  content the EMLTermℂ₁ witness would prove). Inlining the ~700-line
  EMLTermℂ₁ scaffolding from 062/063 into this umbrella was deferred
  to keep this file at a manageable size; downstream work can import
  those Solutions files directly to access the witnesses.
* 068 (Wolfram → Calc 3 complex): off-topic for the umbrella; uses a
  different inductive grammar.
-/

namespace EML

/-! ## Term shapes -/

inductive EMLTerm : Type
  | one : EMLTerm
  | eml : EMLTerm → EMLTerm → EMLTerm
  deriving Repr

inductive EMLTerm₁ : Type
  | one : EMLTerm₁
  | var : EMLTerm₁
  | eml : EMLTerm₁ → EMLTerm₁ → EMLTerm₁
  deriving Repr

inductive EMLTerm₂ : Type
  | one  : EMLTerm₂
  | varX : EMLTerm₂
  | varY : EMLTerm₂
  | eml  : EMLTerm₂ → EMLTerm₂ → EMLTerm₂
  deriving Repr

noncomputable def EMLTerm.eval : EMLTerm → ℝ
  | .one      => 1
  | .eml t u  => Real.exp (EMLTerm.eval t) - Real.log (EMLTerm.eval u)

noncomputable def EMLTerm₁.eval (x : ℝ) : EMLTerm₁ → ℝ
  | .one      => 1
  | .var      => x
  | .eml t u  => Real.exp (EMLTerm₁.eval x t) - Real.log (EMLTerm₁.eval x u)

noncomputable def EMLTerm₂.eval (x y : ℝ) : EMLTerm₂ → ℝ
  | .one      => 1
  | .varX     => x
  | .varY     => y
  | .eml t u  => Real.exp (EMLTerm₂.eval x y t) - Real.log (EMLTerm₂.eval x y u)

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

private lemma log_two_le_one : Real.log 2 ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  linarith

/-! # Section 1 — Round 1 conjuncts (chunks 022, 030–033, 036–038, 040–042)

The proofs are ported verbatim from `Solutions/045_main_completeness_stub.lean`.
-/

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
  refine ⟨.eml
    (.eml .one (.eml (.eml .one (.eml .var (.eml .var .one))) .one))
    (.eml (.eml .var .one) .one), ?_⟩
  intro x
  show Real.exp (EMLTerm₁.eval x
        (.eml .one (.eml (.eml .one (.eml .var (.eml .var .one))) .one))) -
      Real.log (EMLTerm₁.eval x (.eml (.eml .var .one) .one)) = -x
  simp only [EMLTerm₁.eval, Real.log_one, sub_zero, Real.log_exp]
  rw [show Real.exp 1 - (Real.exp 1 - Real.log (Real.exp x - x)) =
        Real.log (Real.exp x - x) from by ring]
  rw [Real.exp_log (exp_sub_self_pos x)]
  ring

/-! ## Conjunct 7 (chunk 037): reciprocal (positive case) -/

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

/-! ## Conjunct 8 (chunk 038): square (positive case) -/

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

/-! ## Conjunct 10 (chunk 041): multiplication (positive case) -/

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

/-! ## Building blocks for Conjunct 11 (chunk 042): x^y -/

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

private theorem c042_pow_xy :
    ∃ t : EMLTerm₂, ∀ x y : ℝ, 0 < x → 0 < y → EMLTerm₂.eval x y t = x ^ y := by
  refine ⟨pow_term, fun x y hx hy => ?_⟩
  rw [eval_pow_term x y hx hy, Real.rpow_def_of_pos hx]
  ring_nf

/-! # Section 2 — Round 2 unary combinators

For the round-2 chunks dealing with one-variable functions, we factor the
common building blocks (`mkEXP`, `mkLOG`, `mkSUB`, `mkNEG`, `mkADD`,
`mkHALVE`, `mkDIV` and the constant `2`) into reusable definitions on
`EMLTerm₁`.
-/

namespace U

def mkEXP (T : EMLTerm₁) : EMLTerm₁ := .eml T .one

lemma eval_mkEXP (x : ℝ) (T : EMLTerm₁) :
    EMLTerm₁.eval x (mkEXP T) = Real.exp (EMLTerm₁.eval x T) := by
  simp [mkEXP, EMLTerm₁.eval, Real.log_one]

def mkLOG (T : EMLTerm₁) : EMLTerm₁ := .eml .one (.eml (.eml .one T) .one)

lemma eval_mkLOG (x : ℝ) (T : EMLTerm₁) :
    EMLTerm₁.eval x (mkLOG T) = Real.log (EMLTerm₁.eval x T) := by
  show Real.exp 1 - Real.log (Real.exp (Real.exp 1 - Real.log (EMLTerm₁.eval x T))
        - Real.log 1) = _
  rw [Real.log_one, sub_zero, Real.log_exp]; ring

def mkSUB (A B : EMLTerm₁) : EMLTerm₁ := .eml (mkLOG A) (mkEXP B)

lemma eval_mkSUB (x : ℝ) (A B : EMLTerm₁) (hA : 0 < EMLTerm₁.eval x A) :
    EMLTerm₁.eval x (mkSUB A B) = EMLTerm₁.eval x A - EMLTerm₁.eval x B := by
  show Real.exp (EMLTerm₁.eval x (mkLOG A)) -
       Real.log (EMLTerm₁.eval x (mkEXP B)) = _
  rw [eval_mkLOG, eval_mkEXP, Real.exp_log hA, Real.log_exp]

def mkNEG (T : EMLTerm₁) : EMLTerm₁ :=
  .eml (mkLOG (.eml T (.eml T .one))) (.eml (.eml T .one) .one)

lemma eval_mkNEG (x : ℝ) (T : EMLTerm₁) :
    EMLTerm₁.eval x (mkNEG T) = -(EMLTerm₁.eval x T) := by
  set t := EMLTerm₁.eval x T with ht
  have h1 : EMLTerm₁.eval x (.eml T .one) = Real.exp t := by
    show Real.exp t - Real.log (EMLTerm₁.eval x .one) = _
    show Real.exp t - Real.log 1 = _
    rw [Real.log_one, sub_zero]
  have h2 : EMLTerm₁.eval x (.eml T (.eml T .one)) = Real.exp t - t := by
    show Real.exp t - Real.log (EMLTerm₁.eval x (.eml T .one)) = _
    rw [h1, Real.log_exp]
  have h3 : EMLTerm₁.eval x (mkLOG (.eml T (.eml T .one)))
      = Real.log (Real.exp t - t) := by
    rw [eval_mkLOG, h2]
  show Real.exp (EMLTerm₁.eval x (mkLOG (.eml T (.eml T .one)))) -
       Real.log (EMLTerm₁.eval x (.eml (.eml T .one) .one)) = _
  rw [h3]
  show Real.exp (Real.log (Real.exp t - t)) -
       Real.log (Real.exp (EMLTerm₁.eval x (.eml T .one)) - Real.log 1) = _
  rw [h1, Real.log_one, sub_zero, Real.exp_log (exp_sub_self_pos t), Real.log_exp]
  ring

/-! ### Constant `2` term -/

def E_term : EMLTerm₁ := .eml .one .one
def EM1_term : EMLTerm₁ := .eml .one E_term
def EM2_term : EMLTerm₁ := mkSUB EM1_term .one
def TWO_term : EMLTerm₁ := mkSUB E_term EM2_term

lemma eval_E (x : ℝ) : EMLTerm₁.eval x E_term = Real.exp 1 := by
  simp [E_term, EMLTerm₁.eval, Real.log_one]

lemma eval_EM1 (x : ℝ) : EMLTerm₁.eval x EM1_term = Real.exp 1 - 1 := by
  simp [EM1_term, E_term, EMLTerm₁.eval, Real.log_one, Real.log_exp]

lemma eval_EM2 (x : ℝ) : EMLTerm₁.eval x EM2_term = Real.exp 1 - 2 := by
  show EMLTerm₁.eval x (mkSUB EM1_term .one) = _
  rw [eval_mkSUB x EM1_term .one (by rw [eval_EM1]; exact exp_one_sub_one_pos)]
  rw [eval_EM1]; show (Real.exp 1 - 1) - 1 = Real.exp 1 - 2; ring

lemma eval_TWO (x : ℝ) : EMLTerm₁.eval x TWO_term = 2 := by
  show EMLTerm₁.eval x (mkSUB E_term EM2_term) = _
  rw [eval_mkSUB x E_term EM2_term (by rw [eval_E]; exact Real.exp_pos _)]
  rw [eval_E, eval_EM2]; ring

/-! ### `mkADD A B` (chunk 040 style, unconditional) -/

def mkADD (A B : EMLTerm₁) : EMLTerm₁ :=
  .eml
    (.eml .one (.eml (.eml .one (.eml A .one)) .one))
    (.eml
      (.eml (.eml .one (.eml (.eml .one (.eml A (.eml A .one))) .one))
            (.eml B .one))
      .one)

lemma eval_mkADD (x : ℝ) (A B : EMLTerm₁) :
    EMLTerm₁.eval x (mkADD A B) = EMLTerm₁.eval x A + EMLTerm₁.eval x B := by
  set a := EMLTerm₁.eval x A with ha
  set b := EMLTerm₁.eval x B with hb
  have hOne : EMLTerm₁.eval x .one = 1 := rfl
  have hExpA : EMLTerm₁.eval x (.eml A .one) = Real.exp a := by
    show Real.exp a - Real.log (EMLTerm₁.eval x .one) = _
    rw [hOne, Real.log_one, sub_zero]
  have hEmA : EMLTerm₁.eval x (.eml .one (.eml A .one)) = Real.exp 1 - a := by
    show Real.exp 1 - Real.log (EMLTerm₁.eval x (.eml A .one)) = _
    rw [hExpA, Real.log_exp]
  have hExpEmA : EMLTerm₁.eval x (.eml (.eml .one (.eml A .one)) .one) =
      Real.exp (Real.exp 1 - a) := by
    show Real.exp (EMLTerm₁.eval x (.eml .one (.eml A .one)))
      - Real.log (EMLTerm₁.eval x .one) = _
    rw [hEmA, hOne, Real.log_one, sub_zero]
  have hLHS : EMLTerm₁.eval x (.eml .one (.eml (.eml .one (.eml A .one)) .one))
      = a := by
    show Real.exp 1 - Real.log (EMLTerm₁.eval x
        (.eml (.eml .one (.eml A .one)) .one)) = _
    rw [hExpEmA, Real.log_exp]; ring
  have h4 : EMLTerm₁.eval x (.eml A (.eml A .one)) = Real.exp a - a := by
    show Real.exp a - Real.log (EMLTerm₁.eval x (.eml A .one)) = _
    rw [hExpA, Real.log_exp]
  have h5 : EMLTerm₁.eval x (.eml .one (.eml A (.eml A .one))) =
      Real.exp 1 - Real.log (Real.exp a - a) := by
    show Real.exp 1 - Real.log (EMLTerm₁.eval x (.eml A (.eml A .one))) = _
    rw [h4]
  have h6 : EMLTerm₁.eval x (.eml (.eml .one (.eml A (.eml A .one))) .one) =
      Real.exp (Real.exp 1 - Real.log (Real.exp a - a)) := by
    show Real.exp (EMLTerm₁.eval x (.eml .one (.eml A (.eml A .one))))
      - Real.log (EMLTerm₁.eval x .one) = _
    rw [h5, hOne, Real.log_one, sub_zero]
  have h7 : EMLTerm₁.eval x
      (.eml .one (.eml (.eml .one (.eml A (.eml A .one))) .one)) =
      Real.log (Real.exp a - a) := by
    show Real.exp 1 - Real.log
      (EMLTerm₁.eval x (.eml (.eml .one (.eml A (.eml A .one))) .one)) = _
    rw [h6, Real.log_exp]; ring
  have h8 : EMLTerm₁.eval x (.eml B .one) = Real.exp b := by
    show Real.exp b - Real.log (EMLTerm₁.eval x .one) = _
    rw [hOne, Real.log_one, sub_zero]
  have h9 : EMLTerm₁.eval x
      (.eml (.eml .one (.eml (.eml .one (.eml A (.eml A .one))) .one))
            (.eml B .one)) = Real.exp a - a - b := by
    show Real.exp (EMLTerm₁.eval x
        (.eml .one (.eml (.eml .one (.eml A (.eml A .one))) .one))) -
      Real.log (EMLTerm₁.eval x (.eml B .one)) = _
    rw [h7, h8, Real.exp_log (exp_sub_self_pos a), Real.log_exp]
  have h10 : EMLTerm₁.eval x (.eml
      (.eml (.eml .one (.eml (.eml .one (.eml A (.eml A .one))) .one))
            (.eml B .one)) .one) = Real.exp (Real.exp a - a - b) := by
    show Real.exp (EMLTerm₁.eval x
        (.eml (.eml .one (.eml (.eml .one (.eml A (.eml A .one))) .one))
              (.eml B .one))) - Real.log (EMLTerm₁.eval x .one) = _
    rw [h9, hOne, Real.log_one, sub_zero]
  show Real.exp (EMLTerm₁.eval x
        (.eml .one (.eml (.eml .one (.eml A .one)) .one))) -
       Real.log (EMLTerm₁.eval x (.eml
        (.eml (.eml .one (.eml (.eml .one (.eml A (.eml A .one))) .one))
              (.eml B .one))
        .one)) = _
  rw [hLHS, h10, Real.log_exp]; ring

/-! ### `mkHALVE P` (eval P > 0) -/

def mkHALVE (P : EMLTerm₁) : EMLTerm₁ :=
  let Pplus2 := mkADD P TWO_term
  let aT := .eml (mkLOG Pplus2) (mkEXP (mkLOG TWO_term))
  let bT := .eml (mkLOG Pplus2) (mkEXP (mkLOG P))
  let logDiff := EMLTerm₁.eml (mkLOG aT) (mkEXP bT)
  mkEXP logDiff

lemma eval_mkHALVE (x : ℝ) (P : EMLTerm₁) (hP : 0 < EMLTerm₁.eval x P) :
    EMLTerm₁.eval x (mkHALVE P) = EMLTerm₁.eval x P / 2 := by
  set p := EMLTerm₁.eval x P with hp
  have hPp2 : EMLTerm₁.eval x (mkADD P TWO_term) = p + 2 := by
    rw [eval_mkADD, eval_TWO]
  have hPp2_pos : 0 < EMLTerm₁.eval x (mkADD P TWO_term) := by
    rw [hPp2]; linarith
  have haT : EMLTerm₁.eval x
      (.eml (mkLOG (mkADD P TWO_term)) (mkEXP (mkLOG TWO_term))) = (p + 2) - Real.log 2 := by
    show Real.exp (EMLTerm₁.eval x (mkLOG (mkADD P TWO_term))) -
      Real.log (EMLTerm₁.eval x (mkEXP (mkLOG TWO_term))) = _
    rw [eval_mkLOG, eval_mkEXP, eval_mkLOG, Real.exp_log hPp2_pos, hPp2,
        eval_TWO, Real.log_exp]
  have haT_pos : 0 < (p + 2) - Real.log 2 := by linarith [log_two_le_one]
  have hbT : EMLTerm₁.eval x
      (.eml (mkLOG (mkADD P TWO_term)) (mkEXP (mkLOG P))) = (p + 2) - Real.log p := by
    show Real.exp (EMLTerm₁.eval x (mkLOG (mkADD P TWO_term))) -
      Real.log (EMLTerm₁.eval x (mkEXP (mkLOG P))) = _
    rw [eval_mkLOG, eval_mkEXP, eval_mkLOG, Real.exp_log hPp2_pos, hPp2,
        Real.exp_log hP]
  have hlogDiff : EMLTerm₁.eval x
      (EMLTerm₁.eml (mkLOG (.eml (mkLOG (mkADD P TWO_term)) (mkEXP (mkLOG TWO_term))))
                    (mkEXP (.eml (mkLOG (mkADD P TWO_term)) (mkEXP (mkLOG P))))) =
      Real.log p - Real.log 2 := by
    show Real.exp (EMLTerm₁.eval x
        (mkLOG (.eml (mkLOG (mkADD P TWO_term)) (mkEXP (mkLOG TWO_term))))) -
      Real.log (EMLTerm₁.eval x
        (mkEXP (.eml (mkLOG (mkADD P TWO_term)) (mkEXP (mkLOG P))))) = _
    rw [eval_mkLOG, eval_mkEXP, Real.exp_log (by rw [haT]; exact haT_pos),
        Real.log_exp, haT, hbT]
    ring
  show EMLTerm₁.eval x (mkHALVE P) = p / 2
  unfold mkHALVE
  show EMLTerm₁.eval x (mkEXP _) = _
  rw [eval_mkEXP, hlogDiff]
  rw [Real.exp_sub, Real.exp_log hP, Real.exp_log (by norm_num : (0:ℝ) < 2)]

/-! ### `mkDIV A B` (eval A > 0, eval B > 0) -/

def mkDIV (A B : EMLTerm₁) : EMLTerm₁ :=
  mkEXP (mkADD (mkLOG A) (mkNEG (mkLOG B)))

lemma eval_mkDIV (x : ℝ) (A B : EMLTerm₁)
    (hA : 0 < EMLTerm₁.eval x A) (hB : 0 < EMLTerm₁.eval x B) :
    EMLTerm₁.eval x (mkDIV A B) = EMLTerm₁.eval x A / EMLTerm₁.eval x B := by
  show EMLTerm₁.eval x (mkEXP (mkADD (mkLOG A) (mkNEG (mkLOG B)))) = _
  rw [eval_mkEXP, eval_mkADD, eval_mkNEG, eval_mkLOG, eval_mkLOG]
  rw [Real.exp_add, Real.exp_log hA, Real.exp_neg, Real.exp_log hB]
  rw [div_eq_mul_inv]

end U

/-! # Section 3 — Round 2 binary combinators (same recipe on `EMLTerm₂`) -/

namespace B2

def mkEXP (T : EMLTerm₂) : EMLTerm₂ := .eml T .one

lemma eval_mkEXP (x y : ℝ) (T : EMLTerm₂) :
    EMLTerm₂.eval x y (mkEXP T) = Real.exp (EMLTerm₂.eval x y T) := by
  simp [mkEXP, EMLTerm₂.eval, Real.log_one]

def mkLOG (T : EMLTerm₂) : EMLTerm₂ := .eml .one (.eml (.eml .one T) .one)

lemma eval_mkLOG (x y : ℝ) (T : EMLTerm₂) :
    EMLTerm₂.eval x y (mkLOG T) = Real.log (EMLTerm₂.eval x y T) := by
  show Real.exp 1 - Real.log (Real.exp (Real.exp 1 - Real.log (EMLTerm₂.eval x y T))
        - Real.log 1) = _
  rw [Real.log_one, sub_zero, Real.log_exp]; ring

def mkSUB (A B : EMLTerm₂) : EMLTerm₂ := .eml (mkLOG A) (mkEXP B)

lemma eval_mkSUB (x y : ℝ) (A B : EMLTerm₂) (hA : 0 < EMLTerm₂.eval x y A) :
    EMLTerm₂.eval x y (mkSUB A B) = EMLTerm₂.eval x y A - EMLTerm₂.eval x y B := by
  show Real.exp (EMLTerm₂.eval x y (mkLOG A)) -
       Real.log (EMLTerm₂.eval x y (mkEXP B)) = _
  rw [eval_mkLOG, eval_mkEXP, Real.exp_log hA, Real.log_exp]

def mkNEG (T : EMLTerm₂) : EMLTerm₂ :=
  .eml (mkLOG (.eml T (.eml T .one))) (.eml (.eml T .one) .one)

lemma eval_mkNEG (x y : ℝ) (T : EMLTerm₂) :
    EMLTerm₂.eval x y (mkNEG T) = -(EMLTerm₂.eval x y T) := by
  set t := EMLTerm₂.eval x y T with ht
  have h1 : EMLTerm₂.eval x y (.eml T .one) = Real.exp t := by
    show Real.exp t - Real.log (EMLTerm₂.eval x y .one) = _
    show Real.exp t - Real.log 1 = _
    rw [Real.log_one, sub_zero]
  have h2 : EMLTerm₂.eval x y (.eml T (.eml T .one)) = Real.exp t - t := by
    show Real.exp t - Real.log (EMLTerm₂.eval x y (.eml T .one)) = _
    rw [h1, Real.log_exp]
  have h3 : EMLTerm₂.eval x y (mkLOG (.eml T (.eml T .one)))
      = Real.log (Real.exp t - t) := by
    rw [eval_mkLOG, h2]
  show Real.exp (EMLTerm₂.eval x y (mkLOG (.eml T (.eml T .one)))) -
       Real.log (EMLTerm₂.eval x y (.eml (.eml T .one) .one)) = _
  rw [h3]
  show Real.exp (Real.log (Real.exp t - t)) -
       Real.log (Real.exp (EMLTerm₂.eval x y (.eml T .one)) - Real.log 1) = _
  rw [h1, Real.log_one, sub_zero, Real.exp_log (exp_sub_self_pos t), Real.log_exp]
  ring

def E_term : EMLTerm₂ := .eml .one .one
def EM1_term : EMLTerm₂ := .eml .one E_term
def EM2_term : EMLTerm₂ := mkSUB EM1_term .one
def TWO_term : EMLTerm₂ := mkSUB E_term EM2_term

lemma eval_E (x y : ℝ) : EMLTerm₂.eval x y E_term = Real.exp 1 := by
  simp [E_term, EMLTerm₂.eval, Real.log_one]

lemma eval_EM1 (x y : ℝ) : EMLTerm₂.eval x y EM1_term = Real.exp 1 - 1 := by
  simp [EM1_term, E_term, EMLTerm₂.eval, Real.log_one, Real.log_exp]

lemma eval_EM2 (x y : ℝ) : EMLTerm₂.eval x y EM2_term = Real.exp 1 - 2 := by
  show EMLTerm₂.eval x y (mkSUB EM1_term .one) = _
  rw [eval_mkSUB x y EM1_term .one (by rw [eval_EM1]; exact exp_one_sub_one_pos)]
  rw [eval_EM1]; show (Real.exp 1 - 1) - 1 = Real.exp 1 - 2; ring

lemma eval_TWO (x y : ℝ) : EMLTerm₂.eval x y TWO_term = 2 := by
  show EMLTerm₂.eval x y (mkSUB E_term EM2_term) = _
  rw [eval_mkSUB x y E_term EM2_term (by rw [eval_E]; exact Real.exp_pos _)]
  rw [eval_E, eval_EM2]; ring

def mkADD (A B : EMLTerm₂) : EMLTerm₂ :=
  .eml
    (.eml .one (.eml (.eml .one (.eml A .one)) .one))
    (.eml
      (.eml (.eml .one (.eml (.eml .one (.eml A (.eml A .one))) .one))
            (.eml B .one))
      .one)

lemma eval_mkADD (x y : ℝ) (A B : EMLTerm₂) :
    EMLTerm₂.eval x y (mkADD A B) = EMLTerm₂.eval x y A + EMLTerm₂.eval x y B := by
  set a := EMLTerm₂.eval x y A with ha
  set b := EMLTerm₂.eval x y B with hb
  have hOne : EMLTerm₂.eval x y .one = 1 := rfl
  have hExpA : EMLTerm₂.eval x y (.eml A .one) = Real.exp a := by
    show Real.exp a - Real.log (EMLTerm₂.eval x y .one) = _
    rw [hOne, Real.log_one, sub_zero]
  have hEmA : EMLTerm₂.eval x y (.eml .one (.eml A .one)) = Real.exp 1 - a := by
    show Real.exp 1 - Real.log (EMLTerm₂.eval x y (.eml A .one)) = _
    rw [hExpA, Real.log_exp]
  have hExpEmA : EMLTerm₂.eval x y (.eml (.eml .one (.eml A .one)) .one) =
      Real.exp (Real.exp 1 - a) := by
    show Real.exp (EMLTerm₂.eval x y (.eml .one (.eml A .one)))
      - Real.log (EMLTerm₂.eval x y .one) = _
    rw [hEmA, hOne, Real.log_one, sub_zero]
  have hLHS : EMLTerm₂.eval x y (.eml .one (.eml (.eml .one (.eml A .one)) .one))
      = a := by
    show Real.exp 1 - Real.log (EMLTerm₂.eval x y
        (.eml (.eml .one (.eml A .one)) .one)) = _
    rw [hExpEmA, Real.log_exp]; ring
  have h4 : EMLTerm₂.eval x y (.eml A (.eml A .one)) = Real.exp a - a := by
    show Real.exp a - Real.log (EMLTerm₂.eval x y (.eml A .one)) = _
    rw [hExpA, Real.log_exp]
  have h5 : EMLTerm₂.eval x y (.eml .one (.eml A (.eml A .one))) =
      Real.exp 1 - Real.log (Real.exp a - a) := by
    show Real.exp 1 - Real.log (EMLTerm₂.eval x y (.eml A (.eml A .one))) = _
    rw [h4]
  have h6 : EMLTerm₂.eval x y (.eml (.eml .one (.eml A (.eml A .one))) .one) =
      Real.exp (Real.exp 1 - Real.log (Real.exp a - a)) := by
    show Real.exp (EMLTerm₂.eval x y (.eml .one (.eml A (.eml A .one))))
      - Real.log (EMLTerm₂.eval x y .one) = _
    rw [h5, hOne, Real.log_one, sub_zero]
  have h7 : EMLTerm₂.eval x y
      (.eml .one (.eml (.eml .one (.eml A (.eml A .one))) .one)) =
      Real.log (Real.exp a - a) := by
    show Real.exp 1 - Real.log
      (EMLTerm₂.eval x y (.eml (.eml .one (.eml A (.eml A .one))) .one)) = _
    rw [h6, Real.log_exp]; ring
  have h8 : EMLTerm₂.eval x y (.eml B .one) = Real.exp b := by
    show Real.exp b - Real.log (EMLTerm₂.eval x y .one) = _
    rw [hOne, Real.log_one, sub_zero]
  have h9 : EMLTerm₂.eval x y
      (.eml (.eml .one (.eml (.eml .one (.eml A (.eml A .one))) .one))
            (.eml B .one)) = Real.exp a - a - b := by
    show Real.exp (EMLTerm₂.eval x y
        (.eml .one (.eml (.eml .one (.eml A (.eml A .one))) .one))) -
      Real.log (EMLTerm₂.eval x y (.eml B .one)) = _
    rw [h7, h8, Real.exp_log (exp_sub_self_pos a), Real.log_exp]
  have h10 : EMLTerm₂.eval x y (.eml
      (.eml (.eml .one (.eml (.eml .one (.eml A (.eml A .one))) .one))
            (.eml B .one)) .one) = Real.exp (Real.exp a - a - b) := by
    show Real.exp (EMLTerm₂.eval x y
        (.eml (.eml .one (.eml (.eml .one (.eml A (.eml A .one))) .one))
              (.eml B .one))) - Real.log (EMLTerm₂.eval x y .one) = _
    rw [h9, hOne, Real.log_one, sub_zero]
  show Real.exp (EMLTerm₂.eval x y
        (.eml .one (.eml (.eml .one (.eml A .one)) .one))) -
       Real.log (EMLTerm₂.eval x y (.eml
        (.eml (.eml .one (.eml (.eml .one (.eml A (.eml A .one))) .one))
              (.eml B .one))
        .one)) = _
  rw [hLHS, h10, Real.log_exp]; ring

def mkHALVE (P : EMLTerm₂) : EMLTerm₂ :=
  let Pplus2 := mkADD P TWO_term
  let aT := .eml (mkLOG Pplus2) (mkEXP (mkLOG TWO_term))
  let bT := .eml (mkLOG Pplus2) (mkEXP (mkLOG P))
  let logDiff := EMLTerm₂.eml (mkLOG aT) (mkEXP bT)
  mkEXP logDiff

lemma eval_mkHALVE (x y : ℝ) (P : EMLTerm₂) (hP : 0 < EMLTerm₂.eval x y P) :
    EMLTerm₂.eval x y (mkHALVE P) = EMLTerm₂.eval x y P / 2 := by
  set p := EMLTerm₂.eval x y P with hp
  have hPp2 : EMLTerm₂.eval x y (mkADD P TWO_term) = p + 2 := by
    rw [eval_mkADD, eval_TWO]
  have hPp2_pos : 0 < EMLTerm₂.eval x y (mkADD P TWO_term) := by
    rw [hPp2]; linarith
  have haT : EMLTerm₂.eval x y
      (.eml (mkLOG (mkADD P TWO_term)) (mkEXP (mkLOG TWO_term))) = (p + 2) - Real.log 2 := by
    show Real.exp (EMLTerm₂.eval x y (mkLOG (mkADD P TWO_term))) -
      Real.log (EMLTerm₂.eval x y (mkEXP (mkLOG TWO_term))) = _
    rw [eval_mkLOG, eval_mkEXP, eval_mkLOG, Real.exp_log hPp2_pos, hPp2,
        eval_TWO, Real.log_exp]
  have haT_pos : 0 < (p + 2) - Real.log 2 := by linarith [log_two_le_one]
  have hbT : EMLTerm₂.eval x y
      (.eml (mkLOG (mkADD P TWO_term)) (mkEXP (mkLOG P))) = (p + 2) - Real.log p := by
    show Real.exp (EMLTerm₂.eval x y (mkLOG (mkADD P TWO_term))) -
      Real.log (EMLTerm₂.eval x y (mkEXP (mkLOG P))) = _
    rw [eval_mkLOG, eval_mkEXP, eval_mkLOG, Real.exp_log hPp2_pos, hPp2,
        Real.exp_log hP]
  have hlogDiff : EMLTerm₂.eval x y
      (EMLTerm₂.eml (mkLOG (.eml (mkLOG (mkADD P TWO_term)) (mkEXP (mkLOG TWO_term))))
                    (mkEXP (.eml (mkLOG (mkADD P TWO_term)) (mkEXP (mkLOG P))))) =
      Real.log p - Real.log 2 := by
    show Real.exp (EMLTerm₂.eval x y
        (mkLOG (.eml (mkLOG (mkADD P TWO_term)) (mkEXP (mkLOG TWO_term))))) -
      Real.log (EMLTerm₂.eval x y
        (mkEXP (.eml (mkLOG (mkADD P TWO_term)) (mkEXP (mkLOG P))))) = _
    rw [eval_mkLOG, eval_mkEXP, Real.exp_log (by rw [haT]; exact haT_pos),
        Real.log_exp, haT, hbT]
    ring
  show EMLTerm₂.eval x y (mkHALVE P) = p / 2
  unfold mkHALVE
  show EMLTerm₂.eval x y (mkEXP _) = _
  rw [eval_mkEXP, hlogDiff]
  rw [Real.exp_sub, Real.exp_log hP, Real.exp_log (by norm_num : (0:ℝ) < 2)]

def mkDIV (A B : EMLTerm₂) : EMLTerm₂ :=
  mkEXP (mkADD (mkLOG A) (mkNEG (mkLOG B)))

lemma eval_mkDIV (x y : ℝ) (A B : EMLTerm₂)
    (hA : 0 < EMLTerm₂.eval x y A) (hB : 0 < EMLTerm₂.eval x y B) :
    EMLTerm₂.eval x y (mkDIV A B) = EMLTerm₂.eval x y A / EMLTerm₂.eval x y B := by
  show EMLTerm₂.eval x y (mkEXP (mkADD (mkLOG A) (mkNEG (mkLOG B)))) = _
  rw [eval_mkEXP, eval_mkADD, eval_mkNEG, eval_mkLOG, eval_mkLOG]
  rw [Real.exp_add, Real.exp_log hA, Real.exp_neg, Real.exp_log hB]
  rw [div_eq_mul_inv]

end B2

/-! # Section 4 — Round 2 conjuncts (chunks 050, 051, 052, 055–058, 060) -/

/-! ## Conjunct 12 (chunk 050): division (positive case) -/

private theorem c050_div_xy :
    ∃ t : EMLTerm₂, ∀ x y : ℝ, 0 < x → 0 < y →
      EMLTerm₂.eval x y t = x / y := by
  refine ⟨B2.mkDIV .varX .varY, fun x y hx hy => ?_⟩
  have hVx : EMLTerm₂.eval x y .varX = x := rfl
  have hVy : EMLTerm₂.eval x y .varY = y := rfl
  rw [B2.eval_mkDIV x y .varX .varY (hVx ▸ hx) (hVy ▸ hy)]
  rw [hVx, hVy]

/-! ## Conjunct 13 (chunk 051): average on the positive quadrant -/

private theorem c051_avg_xy :
    ∃ t : EMLTerm₂, ∀ x y : ℝ, 0 < x → 0 < y →
      EMLTerm₂.eval x y t = (x + y) / 2 := by
  refine ⟨B2.mkHALVE (B2.mkADD .varX .varY), fun x y hx hy => ?_⟩
  have hsum : EMLTerm₂.eval x y (B2.mkADD .varX .varY) = x + y := by
    rw [B2.eval_mkADD]; rfl
  have hsum_pos : 0 < EMLTerm₂.eval x y (B2.mkADD .varX .varY) := by
    rw [hsum]; linarith
  rw [B2.eval_mkHALVE x y _ hsum_pos, hsum]

/-! ## Conjunct 14 (chunk 052): half on the positive ray -/

private theorem c052_half_x :
    ∃ t : EMLTerm₁, ∀ x : ℝ, 0 < x → EMLTerm₁.eval x t = x / 2 := by
  refine ⟨U.mkHALVE .var, fun x hx => ?_⟩
  have hV : EMLTerm₁.eval x .var = x := rfl
  rw [U.eval_mkHALVE x _ (hV ▸ hx), hV]

/-! ## Conjunct 15 (chunk 055): sigmoid σ(x) -/

/-- `1 + exp(-x)` term, using the unconditional `mkADD`. -/
private def sig_onePlusExpNegX : EMLTerm₁ :=
  U.mkADD .one (U.mkEXP (U.mkNEG .var))

private lemma sig_onePlusExpNegX_eval (x : ℝ) :
    EMLTerm₁.eval x sig_onePlusExpNegX = 1 + Real.exp (-x) := by
  show EMLTerm₁.eval x (U.mkADD .one (U.mkEXP (U.mkNEG .var))) = _
  rw [U.eval_mkADD, U.eval_mkEXP, U.eval_mkNEG]
  show (1 : ℝ) + Real.exp (-(EMLTerm₁.eval x .var)) = _
  show (1 : ℝ) + Real.exp (-x) = _
  rfl

private lemma sig_onePlusExpNegX_pos (x : ℝ) :
    0 < EMLTerm₁.eval x sig_onePlusExpNegX := by
  rw [sig_onePlusExpNegX_eval]; positivity

private theorem c055_sigmoid_x :
    ∃ t : EMLTerm₁, ∀ x : ℝ,
      EMLTerm₁.eval x t = 1 / (1 + Real.exp (-x)) := by
  refine ⟨U.mkEXP (U.mkNEG (U.mkLOG sig_onePlusExpNegX)), fun x => ?_⟩
  show EMLTerm₁.eval x (U.mkEXP (U.mkNEG (U.mkLOG sig_onePlusExpNegX))) = _
  rw [U.eval_mkEXP, U.eval_mkNEG, U.eval_mkLOG, sig_onePlusExpNegX_eval]
  rw [Real.exp_neg, Real.exp_log (by positivity : (0:ℝ) < 1 + Real.exp (-x))]
  rw [one_div]

/-! ## Conjunct 16 (chunk 056): cosh(x) -/

private def expxTerm : EMLTerm₁ := .eml .var .one

private lemma eval_expxTerm (x : ℝ) :
    EMLTerm₁.eval x expxTerm = Real.exp x := by
  simp [expxTerm, EMLTerm₁.eval, Real.log_one]

/-- `exp(-x)` via the unconditional `mkNEG`. -/
private def expnegxTerm : EMLTerm₁ := .eml (U.mkNEG .var) .one

private lemma eval_expnegxTerm (x : ℝ) :
    EMLTerm₁.eval x expnegxTerm = Real.exp (-x) := by
  show Real.exp (EMLTerm₁.eval x (U.mkNEG .var)) - Real.log 1 = _
  rw [U.eval_mkNEG, Real.log_one, sub_zero]
  show Real.exp (-(EMLTerm₁.eval x .var)) = _
  rfl

private theorem c056_cosh_x :
    ∃ t : EMLTerm₁, ∀ x : ℝ, EMLTerm₁.eval x t = Real.cosh x := by
  refine ⟨U.mkHALVE (U.mkADD expxTerm expnegxTerm), fun x => ?_⟩
  have hsum : EMLTerm₁.eval x (U.mkADD expxTerm expnegxTerm) =
      Real.exp x + Real.exp (-x) := by
    rw [U.eval_mkADD, eval_expxTerm, eval_expnegxTerm]
  have hsum_pos : 0 < EMLTerm₁.eval x (U.mkADD expxTerm expnegxTerm) := by
    rw [hsum]; positivity
  show EMLTerm₁.eval x (U.mkHALVE (U.mkADD expxTerm expnegxTerm)) = _
  rw [U.eval_mkHALVE x _ hsum_pos, hsum, Real.cosh_eq]

/-! ## Conjunct 17 (chunk 057): sinh(x) -/

private theorem c057_sinh_x :
    ∃ t : EMLTerm₁, ∀ x : ℝ, EMLTerm₁.eval x t = Real.sinh x := by
  refine ⟨U.mkSUB (U.mkHALVE expxTerm) (U.mkHALVE expnegxTerm), fun x => ?_⟩
  have hA_eval : EMLTerm₁.eval x (U.mkHALVE expxTerm) = Real.exp x / 2 := by
    rw [U.eval_mkHALVE x _ (by rw [eval_expxTerm]; exact Real.exp_pos _),
        eval_expxTerm]
  have hB_eval : EMLTerm₁.eval x (U.mkHALVE expnegxTerm) = Real.exp (-x) / 2 := by
    rw [U.eval_mkHALVE x _ (by rw [eval_expnegxTerm]; exact Real.exp_pos _),
        eval_expnegxTerm]
  have hA_pos : 0 < EMLTerm₁.eval x (U.mkHALVE expxTerm) := by
    rw [hA_eval]; positivity
  show EMLTerm₁.eval x (U.mkSUB (U.mkHALVE expxTerm) (U.mkHALVE expnegxTerm)) = _
  rw [U.eval_mkSUB x _ _ hA_pos, hA_eval, hB_eval, Real.sinh_eq]
  ring

/-! ## Conjunct 18 (chunk 058): tanh(x)

`tanh x = sinh x / cosh x`, and both numerator and denominator are positive
(after we use the absolute value form `sinh = (1/2)(exp x − exp(−x))`,
positive only for `x > 0`). To stay consistent with the upstream chunk
which works for all real `x`, we instead express `tanh x = exp x / cosh x − 1`. -/

private def coshDef : EMLTerm₁ := U.mkHALVE (U.mkADD expxTerm expnegxTerm)

private lemma eval_coshDef (x : ℝ) :
    EMLTerm₁.eval x coshDef = Real.cosh x := by
  have hsum : EMLTerm₁.eval x (U.mkADD expxTerm expnegxTerm) =
      Real.exp x + Real.exp (-x) := by
    rw [U.eval_mkADD, eval_expxTerm, eval_expnegxTerm]
  have hsum_pos : 0 < EMLTerm₁.eval x (U.mkADD expxTerm expnegxTerm) := by
    rw [hsum]; positivity
  show EMLTerm₁.eval x (U.mkHALVE (U.mkADD expxTerm expnegxTerm)) = _
  rw [U.eval_mkHALVE x _ hsum_pos, hsum, Real.cosh_eq]

private lemma cosh_pos (x : ℝ) : 0 < Real.cosh x := by
  rw [Real.cosh_eq]; positivity

private lemma coshDef_pos (x : ℝ) : 0 < EMLTerm₁.eval x coshDef := by
  rw [eval_coshDef]; exact cosh_pos x

private def tanhPlusTerm : EMLTerm₁ := U.mkDIV expxTerm coshDef

private lemma eval_tanhPlusTerm (x : ℝ) :
    EMLTerm₁.eval x tanhPlusTerm = Real.exp x / Real.cosh x := by
  show EMLTerm₁.eval x (U.mkDIV expxTerm coshDef) = _
  have hA : 0 < EMLTerm₁.eval x expxTerm := by
    rw [eval_expxTerm]; exact Real.exp_pos _
  have hB : 0 < EMLTerm₁.eval x coshDef := coshDef_pos x
  rw [U.eval_mkDIV x expxTerm coshDef hA hB, eval_expxTerm, eval_coshDef]

private lemma tanhPlus_eq_tanh_add_one (x : ℝ) :
    Real.exp x / Real.cosh x = Real.tanh x + 1 := by
  have hc : Real.cosh x ≠ 0 := (cosh_pos x).ne'
  rw [Real.tanh_eq_sinh_div_cosh]
  rw [div_add_one hc]
  rw [Real.sinh_eq, Real.cosh_eq]
  field_simp
  ring

private lemma tanhPlusTerm_pos (x : ℝ) : 0 < EMLTerm₁.eval x tanhPlusTerm := by
  rw [eval_tanhPlusTerm]
  exact div_pos (Real.exp_pos _) (cosh_pos x)

private theorem c058_tanh_x :
    ∃ t : EMLTerm₁, ∀ x : ℝ, EMLTerm₁.eval x t = Real.tanh x := by
  refine ⟨U.mkSUB tanhPlusTerm .one, fun x => ?_⟩
  show EMLTerm₁.eval x (U.mkSUB tanhPlusTerm .one) = _
  rw [U.eval_mkSUB x tanhPlusTerm .one (tanhPlusTerm_pos x), eval_tanhPlusTerm]
  show Real.exp x / Real.cosh x - EMLTerm₁.eval x .one = _
  show Real.exp x / Real.cosh x - 1 = _
  have h := tanhPlus_eq_tanh_add_one x
  linarith

/-! ## Conjunct 19 (chunk 060): arcosh(x) on `√2 < x` -/

/-- Squaring construction restricted to `0 < x`. -/
private def xSqTerm : EMLTerm₁ := U.mkEXP (U.mkADD (U.mkLOG .var) (U.mkLOG .var))

private lemma eval_xSqTerm (x : ℝ) (hx : 0 < x) :
    EMLTerm₁.eval x xSqTerm = x ^ 2 := by
  show EMLTerm₁.eval x (U.mkEXP (U.mkADD (U.mkLOG .var) (U.mkLOG .var))) = _
  rw [U.eval_mkEXP, U.eval_mkADD]
  show Real.exp (EMLTerm₁.eval x (U.mkLOG .var) + EMLTerm₁.eval x (U.mkLOG .var)) = _
  rw [U.eval_mkLOG]
  show Real.exp (Real.log (EMLTerm₁.eval x .var) + Real.log (EMLTerm₁.eval x .var)) = _
  show Real.exp (Real.log x + Real.log x) = _
  rw [show Real.log x + Real.log x = 2 * Real.log x from by ring]
  rw [mul_comm 2 (Real.log x), Real.exp_mul, Real.exp_log hx]
  norm_num

private lemma xSqMinus1_pos {x : ℝ} (hx : 1 < x) : 0 < x ^ 2 - 1 := by
  have h1 : (1 : ℝ) < x ^ 2 := by nlinarith
  linarith

private def xSqMinus1 : EMLTerm₁ := U.mkSUB xSqTerm .one

private lemma eval_xSqMinus1 (x : ℝ) (hx : 1 < x) :
    EMLTerm₁.eval x xSqMinus1 = x ^ 2 - 1 := by
  have hxpos : 0 < x := by linarith
  show EMLTerm₁.eval x (U.mkSUB xSqTerm .one) = _
  rw [U.eval_mkSUB x xSqTerm .one (by rw [eval_xSqTerm x hxpos]; positivity),
      eval_xSqTerm x hxpos]
  rfl

private def sqrtXSqMinus1 : EMLTerm₁ := U.mkEXP (U.mkHALVE (U.mkLOG xSqMinus1))

private lemma sqrt_two_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

private lemma sqrt_two_gt_one : (1 : ℝ) < Real.sqrt 2 := by
  have h : Real.sqrt 1 < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [Real.sqrt_one] at h; exact h

private lemma log_xSqMinus1_pos {x : ℝ} (hx : Real.sqrt 2 < x) :
    0 < Real.log (x ^ 2 - 1) := by
  have h1 : 1 < x ^ 2 - 1 := by
    have hx2 : 2 < x ^ 2 := by
      have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
      nlinarith [sqrt_two_pos]
    linarith
  exact Real.log_pos h1

private lemma eval_sqrtXSqMinus1 (x : ℝ) (hx : Real.sqrt 2 < x) :
    EMLTerm₁.eval x sqrtXSqMinus1 = Real.sqrt (x ^ 2 - 1) := by
  have hx1 : 1 < x := lt_trans sqrt_two_gt_one hx
  have hxpos : 0 < x := by linarith
  have hSqM1_pos : 0 < x ^ 2 - 1 := xSqMinus1_pos hx1
  have hLog_pos : 0 < Real.log (x ^ 2 - 1) := log_xSqMinus1_pos hx
  show EMLTerm₁.eval x (U.mkEXP (U.mkHALVE (U.mkLOG xSqMinus1))) = _
  rw [U.eval_mkEXP]
  have hLOG_eval : EMLTerm₁.eval x (U.mkLOG xSqMinus1) = Real.log (x ^ 2 - 1) := by
    rw [U.eval_mkLOG, eval_xSqMinus1 x hx1]
  have hLOG_pos' : 0 < EMLTerm₁.eval x (U.mkLOG xSqMinus1) := by
    rw [hLOG_eval]; exact hLog_pos
  rw [U.eval_mkHALVE x _ hLOG_pos', hLOG_eval]
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hSqM1_pos]
  ring_nf

private def xPlusSqrt : EMLTerm₁ := U.mkADD .var sqrtXSqMinus1

private lemma eval_xPlusSqrt (x : ℝ) (hx : Real.sqrt 2 < x) :
    EMLTerm₁.eval x xPlusSqrt = x + Real.sqrt (x ^ 2 - 1) := by
  show EMLTerm₁.eval x (U.mkADD .var sqrtXSqMinus1) = _
  rw [U.eval_mkADD, eval_sqrtXSqMinus1 x hx]
  rfl

private theorem c060_arcosh_x :
    ∃ t : EMLTerm₁, ∀ x : ℝ, Real.sqrt 2 < x →
      EMLTerm₁.eval x t = Real.arcosh x := by
  refine ⟨U.mkLOG xPlusSqrt, fun x hx => ?_⟩
  show EMLTerm₁.eval x (U.mkLOG xPlusSqrt) = _
  rw [U.eval_mkLOG, eval_xPlusSqrt x hx]
  rw [Real.arcosh]

/-! ## Conjunct 20 (chunk 069): universal minimality

A 2-primitive calculator (constant `c` plus a single binary `op`) cannot
represent the identity function as a function of a free variable, because
every closed term evaluates to a constant.  This is a general structural
corollary that strengthens chunk 029.
-/

inductive TwoPrimCalc : Type
  | const : TwoPrimCalc
  | apply : TwoPrimCalc → TwoPrimCalc → TwoPrimCalc
  deriving Repr

def TwoPrimCalc.eval (c : ℝ) (op : ℝ → ℝ → ℝ) : TwoPrimCalc → ℝ
  | .const     => c
  | .apply a b => op (eval c op a) (eval c op b)

private theorem c069_universal_minimality
    (c : ℝ) (op : ℝ → ℝ → ℝ) :
    ¬ ∃ t : TwoPrimCalc, ∀ x : ℝ, TwoPrimCalc.eval c op t = x := by
  by_contra h
  obtain ⟨t, ht⟩ := h
  linarith [ht 0, ht 1]

/-! # Section 5 — Umbrella theorem -/

/-- **Main completeness — full umbrella (Round 2).**

Bundles 19 constructive `EMLTerm` / `EMLTerm₁` / `EMLTerm₂` witnesses
plus a structural minimality corollary into a single proof.  Conjuncts
in order:

1. `0` (chunk 030)
2. `−1` (chunk 031)
3. `2` (chunk 032)
4. `1/2` (chunk 033)
5. `e` (chunk 022)
6. negation `x ↦ −x` (chunk 036)
7. reciprocal on positives `x ↦ 1/x` (chunk 037)
8. square on positives `x ↦ x²` (chunk 038)
9. addition (chunk 040)
10. multiplication on the positive quadrant (chunk 041)
11. real power on the positive quadrant (chunk 042)
12. division on the positive quadrant (chunk 050)
13. average on the positive quadrant (chunk 051)
14. half on the positive ray (chunk 052)
15. sigmoid σ (chunk 055)
16. `cosh` (chunk 056)
17. `sinh` (chunk 057)
18. `tanh` (chunk 058)
19. `arcosh` on `√2 < x` (chunk 060)
20. universal minimality (chunk 069): a `{constant, binary}` calculator
    cannot realise the identity function.

NOT included: π (chunk 034), i (chunk 035), √x (chunk 039), hypot
(chunk 054), arsinh (chunk 059), artanh (chunk 061), trig + inverse
trig (chunks 062–067), Wolfram→Calc 3 complex (chunk 068).  See file
header for per-chunk reasons. -/
theorem main_completeness_full :
    (∃ t : EMLTerm,  EMLTerm.eval t = 0) ∧
    (∃ t : EMLTerm,  EMLTerm.eval t = -1) ∧
    (∃ t : EMLTerm,  EMLTerm.eval t = 2) ∧
    (∃ t : EMLTerm,  EMLTerm.eval t = 1 / 2) ∧
    (∃ t : EMLTerm,  EMLTerm.eval t = Real.exp 1) ∧
    (∃ t : EMLTerm₁, ∀ x : ℝ, EMLTerm₁.eval x t = -x) ∧
    (∃ t : EMLTerm₁, ∀ x : ℝ, 0 < x → EMLTerm₁.eval x t = 1 / x) ∧
    (∃ t : EMLTerm₁, ∀ x : ℝ, 0 < x → EMLTerm₁.eval x t = x ^ 2) ∧
    (∃ t : EMLTerm₂, ∀ x y : ℝ, EMLTerm₂.eval x y t = x + y) ∧
    (∃ t : EMLTerm₂, ∀ x y : ℝ, 0 < x → 0 < y → EMLTerm₂.eval x y t = x * y) ∧
    (∃ t : EMLTerm₂, ∀ x y : ℝ, 0 < x → 0 < y → EMLTerm₂.eval x y t = x ^ y) ∧
    (∃ t : EMLTerm₂, ∀ x y : ℝ, 0 < x → 0 < y → EMLTerm₂.eval x y t = x / y) ∧
    (∃ t : EMLTerm₂, ∀ x y : ℝ, 0 < x → 0 < y → EMLTerm₂.eval x y t = (x + y) / 2) ∧
    (∃ t : EMLTerm₁, ∀ x : ℝ, 0 < x → EMLTerm₁.eval x t = x / 2) ∧
    (∃ t : EMLTerm₁, ∀ x : ℝ, EMLTerm₁.eval x t = 1 / (1 + Real.exp (-x))) ∧
    (∃ t : EMLTerm₁, ∀ x : ℝ, EMLTerm₁.eval x t = Real.cosh x) ∧
    (∃ t : EMLTerm₁, ∀ x : ℝ, EMLTerm₁.eval x t = Real.sinh x) ∧
    (∃ t : EMLTerm₁, ∀ x : ℝ, EMLTerm₁.eval x t = Real.tanh x) ∧
    (∃ t : EMLTerm₁, ∀ x : ℝ, Real.sqrt 2 < x → EMLTerm₁.eval x t = Real.arcosh x) ∧
    (∀ (c : ℝ) (op : ℝ → ℝ → ℝ),
       ¬ ∃ t : TwoPrimCalc, ∀ x : ℝ, TwoPrimCalc.eval c op t = x) :=
  ⟨c030_zero, c031_neg_one, c032_two, c033_half, c022_e,
   c036_neg_x, c037_inv_x, c038_sq_x,
   c040_add_xy, c041_mul_xy, c042_pow_xy,
   c050_div_xy, c051_avg_xy, c052_half_x,
   c055_sigmoid_x, c056_cosh_x, c057_sinh_x, c058_tanh_x,
   c060_arcosh_x, c069_universal_minimality⟩

end EML
