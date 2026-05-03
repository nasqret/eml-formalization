import Mathlib

namespace EML

/-- Two-variable EML term grammar. -/
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

/-- Substitution: replace varX with A, varY with B. -/
def subst (t : EMLTerm₂) (A B : EMLTerm₂) : EMLTerm₂ :=
  match t with
  | .one      => .one
  | .varX     => A
  | .varY     => B
  | .eml u v  => .eml (subst u A B) (subst v A B)

lemma eval_subst (x y : ℝ) (t A B : EMLTerm₂) :
    EMLTerm₂.eval x y (subst t A B) =
    EMLTerm₂.eval (EMLTerm₂.eval x y A) (EMLTerm₂.eval x y B) t := by
  induction t with
  | one => rfl
  | varX => rfl
  | varY => rfl
  | eml u v ihu ihv =>
    show Real.exp (EMLTerm₂.eval x y (subst u A B)) -
         Real.log (EMLTerm₂.eval x y (subst v A B)) =
         Real.exp (EMLTerm₂.eval (EMLTerm₂.eval x y A) (EMLTerm₂.eval x y B) u) -
         Real.log (EMLTerm₂.eval (EMLTerm₂.eval x y A) (EMLTerm₂.eval x y B) v)
    rw [ihu, ihv]

/-! ### chunk 042's pow_term, lifted in -/

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

/-! ### chunk 040 mkADD adapted (works for any A, B). -/

def mkADD₂ (A B : EMLTerm₂) : EMLTerm₂ :=
  .eml
    (.eml .one (.eml (.eml .one (.eml A .one)) .one))
    (.eml
      (.eml (.eml .one (.eml (.eml .one (.eml A (.eml A .one))) .one))
            (.eml B .one))
      .one)

lemma exp_sub_self_pos (t : ℝ) : 0 < Real.exp t - t := by
  linarith [Real.add_one_le_exp t]

lemma eval_mkADD₂ (x y : ℝ) (A B : EMLTerm₂) :
    EMLTerm₂.eval x y (mkADD₂ A B) = EMLTerm₂.eval x y A + EMLTerm₂.eval x y B := by
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
    show Real.exp (EMLTerm₂.eval x y (.eml .one (.eml A .one))) -
      Real.log (EMLTerm₂.eval x y .one) = _
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
    show Real.exp (EMLTerm₂.eval x y (.eml .one (.eml A (.eml A .one)))) -
      Real.log (EMLTerm₂.eval x y .one) = _
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

/-! ### `mkSQ A` evaluating to `(eval A)^2` for `eval A > 0`. (chunk 038 style) -/

private def Z₂ : EMLTerm₂ := .eml .one (.eml (.eml .one .one) .one)
private def logTerm₂ (T : EMLTerm₂) : EMLTerm₂ :=
  .eml Z₂ (.eml (.eml Z₂ T) .one)

private lemma eval_Z₂ (x y : ℝ) : EMLTerm₂.eval x y Z₂ = 0 := by
  simp [Z₂, EMLTerm₂.eval]

private lemma eval_logTerm₂ (x y : ℝ) (T : EMLTerm₂)
    (hT : 0 < EMLTerm₂.eval x y T) :
    EMLTerm₂.eval x y (logTerm₂ T) = Real.log (EMLTerm₂.eval x y T) := by
  show Real.exp (EMLTerm₂.eval x y Z₂) -
       Real.log (EMLTerm₂.eval x y (.eml (.eml Z₂ T) .one)) = _
  rw [eval_Z₂]
  show Real.exp 0 -
       Real.log (Real.exp (EMLTerm₂.eval x y (.eml Z₂ T)) - Real.log 1) = _
  rw [Real.log_one, sub_zero]
  show Real.exp 0 -
       Real.log (Real.exp (Real.exp (EMLTerm₂.eval x y Z₂) -
         Real.log (EMLTerm₂.eval x y T))) = _
  rw [eval_Z₂, Real.exp_zero, Real.log_exp]
  ring

/-- `mkSQ A` = `(eval A)^2` for `eval A > 0`.  Uses the same trick as chunk 038
   (`x^2 = exp(2 log x)`) but with `LOG` and arithmetic via `eml`. -/
def mkSQ (A : EMLTerm₂) : EMLTerm₂ :=
  let logA := logTerm₂ A
  let xMinusLogA := .eml logA A
  let logXMinusLogA := logTerm₂ xMinusLogA
  let xMinus2LogA := EMLTerm₂.eml logXMinusLogA (.eml logA .one)
  let twoLogA := EMLTerm₂.eml logA (.eml xMinus2LogA .one)
  EMLTerm₂.eml twoLogA .one

private lemma x_minus_log_pos (a : ℝ) (ha : 0 < a) : 0 < a - Real.log a := by
  linarith [Real.log_le_sub_one_of_pos ha]

lemma eval_mkSQ (x y : ℝ) (A : EMLTerm₂) (hA : 0 < EMLTerm₂.eval x y A) :
    EMLTerm₂.eval x y (mkSQ A) = (EMLTerm₂.eval x y A) ^ 2 := by
  set a := EMLTerm₂.eval x y A with ha_def
  -- log A.
  have hlogA : EMLTerm₂.eval x y (logTerm₂ A) = Real.log a := by
    rw [eval_logTerm₂ x y A hA]
  -- xMinusLogA = eml(logA, A) → exp(log a) - log a = a - log a.
  have hxMlogA : EMLTerm₂.eval x y (.eml (logTerm₂ A) A) = a - Real.log a := by
    show Real.exp (EMLTerm₂.eval x y (logTerm₂ A)) -
         Real.log (EMLTerm₂.eval x y A) = _
    rw [hlogA, Real.exp_log hA]
  have hxMlogA_pos : 0 < a - Real.log a := x_minus_log_pos a hA
  -- log(xMinusLogA) = log(a - log a).
  have hlogXMlogA : EMLTerm₂.eval x y (logTerm₂ (.eml (logTerm₂ A) A)) =
      Real.log (a - Real.log a) := by
    rw [eval_logTerm₂ x y _ (by rw [hxMlogA]; exact hxMlogA_pos), hxMlogA]
  -- xMinus2LogA = eml(logXMinusLogA, eml(logA, .one))
  --   = exp(log(a - log a)) - log(exp(log a) - log 1)
  --   = (a - log a) - log a
  --   = a - 2 log a.
  have hxM2logA : EMLTerm₂.eval x y
      (EMLTerm₂.eml (logTerm₂ (.eml (logTerm₂ A) A))
        (.eml (logTerm₂ A) .one)) = a - 2 * Real.log a := by
    show Real.exp (EMLTerm₂.eval x y (logTerm₂ (.eml (logTerm₂ A) A))) -
         Real.log (EMLTerm₂.eval x y (.eml (logTerm₂ A) .one)) = _
    rw [hlogXMlogA, Real.exp_log hxMlogA_pos]
    show (a - Real.log a) -
         Real.log (Real.exp (EMLTerm₂.eval x y (logTerm₂ A)) -
           Real.log (EMLTerm₂.eval x y .one)) = _
    rw [hlogA]
    show (a - Real.log a) -
         Real.log (Real.exp (Real.log a) - Real.log 1) = _
    rw [Real.log_one, sub_zero, Real.exp_log hA]; ring
  -- twoLogA = eml(logA, eml(xMinus2LogA, .one)).
  have htwoLogA : EMLTerm₂.eval x y
      (EMLTerm₂.eml (logTerm₂ A)
        (.eml (EMLTerm₂.eml (logTerm₂ (.eml (logTerm₂ A) A))
          (.eml (logTerm₂ A) .one)) .one)) = 2 * Real.log a := by
    show Real.exp (EMLTerm₂.eval x y (logTerm₂ A)) -
         Real.log (EMLTerm₂.eval x y
            (.eml (EMLTerm₂.eml (logTerm₂ (.eml (logTerm₂ A) A))
              (.eml (logTerm₂ A) .one)) .one)) = _
    rw [hlogA, Real.exp_log hA]
    show a - Real.log (Real.exp (EMLTerm₂.eval x y
        (EMLTerm₂.eml (logTerm₂ (.eml (logTerm₂ A) A))
          (.eml (logTerm₂ A) .one))) - Real.log 1) = _
    rw [Real.log_one, sub_zero, hxM2logA, Real.log_exp]; ring
  -- Final: eml(twoLogA, .one) = exp(2 log a) - log 1 = exp(2 log a) = a^2.
  show EMLTerm₂.eval x y (mkSQ A) = a ^ 2
  unfold mkSQ
  show Real.exp (EMLTerm₂.eval x y
        (EMLTerm₂.eml (logTerm₂ A)
          (.eml (EMLTerm₂.eml (logTerm₂ (.eml (logTerm₂ A) A))
            (.eml (logTerm₂ A) .one)) .one))) -
       Real.log (EMLTerm₂.eval x y .one) = _
  rw [htwoLogA]
  show Real.exp (2 * Real.log a) - Real.log (EMLTerm₂.eval x y .one) = _
  show Real.exp (2 * Real.log a) - Real.log 1 = _
  rw [Real.log_one, sub_zero, mul_comm, Real.exp_mul, Real.exp_log hA]
  norm_cast

/-! ### Half-term: a closed `EMLTerm₂` evaluating to `1/2`. -/

/-- Build `1/2` via the chunk 033 trick (lifted to EMLTerm₂). -/
def E_t : EMLTerm₂ := .eml .one .one
def E_minus_one_t : EMLTerm₂ := .eml .one E_t
def log_em1_t : EMLTerm₂ := logTerm₂ E_minus_one_t
def E_minus_two_t : EMLTerm₂ := .eml log_em1_t E_t
def exp_em2_t : EMLTerm₂ := .eml E_minus_two_t .one
def TWO_t : EMLTerm₂ := .eml .one exp_em2_t
def eml2_t : EMLTerm₂ := .eml .one TWO_t
def log_eml2_t : EMLTerm₂ := logTerm₂ eml2_t
def neg_log2_t : EMLTerm₂ := .eml log_eml2_t (.eml (.eml .one .one) .one)
def half_term : EMLTerm₂ := .eml neg_log2_t .one

lemma eval_E_t (x y : ℝ) : EMLTerm₂.eval x y E_t = Real.exp 1 := by
  simp [E_t, EMLTerm₂.eval, Real.log_one]

lemma eval_E_minus_one_t (x y : ℝ) :
    EMLTerm₂.eval x y E_minus_one_t = Real.exp 1 - 1 := by
  simp [E_minus_one_t, E_t, EMLTerm₂.eval, Real.log_one, Real.log_exp]

lemma exp_one_sub_one_pos : (0 : ℝ) < Real.exp 1 - 1 := by
  linarith [Real.add_one_le_exp (1:ℝ)]

lemma eval_log_em1_t (x y : ℝ) :
    EMLTerm₂.eval x y log_em1_t = Real.log (Real.exp 1 - 1) := by
  unfold log_em1_t
  rw [eval_logTerm₂ x y _ (by rw [eval_E_minus_one_t]; exact exp_one_sub_one_pos),
    eval_E_minus_one_t]

lemma eval_E_minus_two_t (x y : ℝ) :
    EMLTerm₂.eval x y E_minus_two_t = Real.exp 1 - 2 := by
  show Real.exp (EMLTerm₂.eval x y log_em1_t) -
       Real.log (EMLTerm₂.eval x y E_t) = _
  rw [eval_log_em1_t, eval_E_t, Real.exp_log exp_one_sub_one_pos, Real.log_exp]
  ring

lemma eval_exp_em2_t (x y : ℝ) :
    EMLTerm₂.eval x y exp_em2_t = Real.exp (Real.exp 1 - 2) := by
  show Real.exp (EMLTerm₂.eval x y E_minus_two_t) -
       Real.log (EMLTerm₂.eval x y .one) = _
  rw [eval_E_minus_two_t]
  show Real.exp (Real.exp 1 - 2) - Real.log 1 = _
  rw [Real.log_one, sub_zero]

lemma eval_TWO_t (x y : ℝ) : EMLTerm₂.eval x y TWO_t = 2 := by
  show Real.exp (EMLTerm₂.eval x y .one) -
       Real.log (EMLTerm₂.eval x y exp_em2_t) = _
  show Real.exp 1 - Real.log (EMLTerm₂.eval x y exp_em2_t) = _
  rw [eval_exp_em2_t, Real.log_exp]; ring

lemma eval_eml2_t (x y : ℝ) :
    EMLTerm₂.eval x y eml2_t = Real.exp 1 - Real.log 2 := by
  show Real.exp (EMLTerm₂.eval x y .one) -
       Real.log (EMLTerm₂.eval x y TWO_t) = _
  show Real.exp 1 - Real.log (EMLTerm₂.eval x y TWO_t) = _
  rw [eval_TWO_t]

lemma log_two_le_one : Real.log 2 ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  linarith

lemma exp_one_sub_log_two_pos : (0 : ℝ) < Real.exp 1 - Real.log 2 := by
  linarith [exp_one_sub_one_pos, log_two_le_one]

lemma eval_log_eml2_t (x y : ℝ) :
    EMLTerm₂.eval x y log_eml2_t = Real.log (Real.exp 1 - Real.log 2) := by
  unfold log_eml2_t
  rw [eval_logTerm₂ x y _ (by rw [eval_eml2_t]; exact exp_one_sub_log_two_pos),
    eval_eml2_t]

lemma eval_neg_log2_t (x y : ℝ) :
    EMLTerm₂.eval x y neg_log2_t = -Real.log 2 := by
  show Real.exp (EMLTerm₂.eval x y log_eml2_t) -
       Real.log (EMLTerm₂.eval x y (.eml (.eml .one .one) .one)) = _
  rw [eval_log_eml2_t, Real.exp_log exp_one_sub_log_two_pos]
  show Real.exp 1 - Real.log 2 -
    Real.log (Real.exp (EMLTerm₂.eval x y (.eml .one .one)) - Real.log 1) = _
  rw [show EMLTerm₂.eval x y (.eml .one .one) =
      Real.exp 1 - Real.log 1 from rfl, Real.log_one, sub_zero, Real.log_exp]
  ring

lemma eval_half_term (x y : ℝ) : EMLTerm₂.eval x y half_term = 1 / 2 := by
  show Real.exp (EMLTerm₂.eval x y neg_log2_t) -
       Real.log (EMLTerm₂.eval x y .one) = _
  rw [eval_neg_log2_t]
  show Real.exp (-Real.log 2) - Real.log 1 = _
  rw [Real.log_one, sub_zero, Real.exp_neg,
    Real.exp_log (by norm_num : (0:ℝ) < 2)]
  norm_num

/-! ### Sum-of-squares term. -/

/-- `x² + y²` for x, y > 0. -/
def sumSqTerm : EMLTerm₂ := mkADD₂ (mkSQ .varX) (mkSQ .varY)

lemma eval_sumSqTerm (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    EMLTerm₂.eval x y sumSqTerm = x ^ 2 + y ^ 2 := by
  unfold sumSqTerm
  rw [eval_mkADD₂]
  have hsqx : EMLTerm₂.eval x y (mkSQ .varX) = x ^ 2 := by
    have hx' : 0 < EMLTerm₂.eval x y EMLTerm₂.varX := by
      show 0 < x; exact hx
    rw [eval_mkSQ x y _ hx']
    rfl
  have hsqy : EMLTerm₂.eval x y (mkSQ .varY) = y ^ 2 := by
    have hy' : 0 < EMLTerm₂.eval x y EMLTerm₂.varY := by
      show 0 < y; exact hy
    rw [eval_mkSQ x y _ hy']
    rfl
  rw [hsqx, hsqy]

lemma sumSqTerm_pos (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    0 < EMLTerm₂.eval x y sumSqTerm := by
  rw [eval_sumSqTerm x y hx hy]; positivity

/-! ### Hypot term: `(x²+y²)^(1/2)` via substitution into `pow_term`. -/

/-- The hypot witness: substitute sumSqTerm for varX and half_term for varY into pow_term. -/
noncomputable def hypotTerm : EMLTerm₂ := subst pow_term sumSqTerm half_term

lemma eval_hypotTerm (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    EMLTerm₂.eval x y hypotTerm = Real.sqrt (x ^ 2 + y ^ 2) := by
  unfold hypotTerm
  rw [eval_subst]
  -- Now need eval at (eval sumSqTerm, eval half_term) = (x²+y², 1/2).
  have hsum : EMLTerm₂.eval x y sumSqTerm = x ^ 2 + y ^ 2 := eval_sumSqTerm x y hx hy
  have hhalf : EMLTerm₂.eval x y half_term = 1 / 2 := eval_half_term x y
  rw [hsum, hhalf]
  -- pow_term at (x²+y², 1/2) = exp((1/2) * log(x²+y²)) = √(x²+y²).
  rw [eval_pow_term_eq _ _ (by positivity) (by norm_num : (0:ℝ) < 1/2)]
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity)]
  ring_nf

theorem emlterm2_for_hypot :
    ∃ t : EMLTerm₂, ∀ x y : ℝ, 0 < x → 0 < y →
      EMLTerm₂.eval x y t = Real.sqrt (x ^ 2 + y ^ 2) :=
  ⟨hypotTerm, eval_hypotTerm⟩

end EML
