import Mathlib

namespace EML

inductive EMLTerm₁ : Type
  | one : EMLTerm₁
  | var : EMLTerm₁
  | eml : EMLTerm₁ → EMLTerm₁ → EMLTerm₁
  deriving Repr

noncomputable def EMLTerm₁.eval (x : ℝ) : EMLTerm₁ → ℝ
  | .one      => 1
  | .var      => x
  | .eml t u  => Real.exp (EMLTerm₁.eval x t) - Real.log (EMLTerm₁.eval x u)

/-! ### Generic combinators (chunk 052 style) -/

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

lemma exp_sub_self_pos (t : ℝ) : 0 < Real.exp t - t := by
  linarith [Real.add_one_le_exp t]

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

lemma EM1_pos : (0 : ℝ) < Real.exp 1 - 1 := by
  have h1 : Real.exp 0 < Real.exp 1 := Real.exp_strictMono (by norm_num)
  rw [Real.exp_zero] at h1; linarith

lemma eval_EM2 (x : ℝ) : EMLTerm₁.eval x EM2_term = Real.exp 1 - 2 := by
  show EMLTerm₁.eval x (mkSUB EM1_term .one) = _
  rw [eval_mkSUB x EM1_term .one (by rw [eval_EM1]; exact EM1_pos)]
  rw [eval_EM1]; show (Real.exp 1 - 1) - 1 = Real.exp 1 - 2; ring

lemma eval_TWO (x : ℝ) : EMLTerm₁.eval x TWO_term = 2 := by
  show EMLTerm₁.eval x (mkSUB E_term EM2_term) = _
  rw [eval_mkSUB x E_term EM2_term (by rw [eval_E]; exact Real.exp_pos _)]
  rw [eval_E, eval_EM2]; ring

/-! ### `mkADD A B` (chunk 040) and `mkADDPos`/`mkSUBPos` (positivity-aware
    forms reused below). -/

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

/-! ### `mkHALVE P` for positive P -/

def mkHALVE (P : EMLTerm₁) : EMLTerm₁ :=
  let Pplus2 := mkADD P TWO_term
  let aT := .eml (mkLOG Pplus2) (mkEXP (mkLOG TWO_term))
  let bT := .eml (mkLOG Pplus2) (mkEXP (mkLOG P))
  let logDiff := EMLTerm₁.eml (mkLOG aT) (mkEXP bT)
  mkEXP logDiff

lemma log_two_le_one : Real.log 2 ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  linarith

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

/-! ### Building blocks: `x²`, `x² − 1`, `√(x²−1)`, `x + √(x²−1)`. -/

/-- `x² = exp(log x + log x)` for `x > 0`. -/
def xSqTerm : EMLTerm₁ := mkEXP (mkADD (mkLOG .var) (mkLOG .var))

lemma eval_xSqTerm (x : ℝ) (hx : 0 < x) :
    EMLTerm₁.eval x xSqTerm = x ^ 2 := by
  show EMLTerm₁.eval x (mkEXP (mkADD (mkLOG .var) (mkLOG .var))) = _
  rw [eval_mkEXP, eval_mkADD, eval_mkLOG]
  have hvar : EMLTerm₁.eval x .var = x := rfl
  rw [hvar]
  rw [show Real.log x + Real.log x = 2 * Real.log x from by ring]
  rw [mul_comm 2 (Real.log x), Real.exp_mul, Real.exp_log hx]
  norm_num

/-- For `x > 1`, `x² − 1 > 0`. -/
lemma xSqMinus1_pos {x : ℝ} (hx : 1 < x) : 0 < x ^ 2 - 1 := by
  have h1 : (1 : ℝ) < x ^ 2 := by nlinarith
  linarith

/-- `x² − 1` term (uses `mkSUB`; positivity comes from `x > 1`). -/
def xSqMinus1 : EMLTerm₁ := mkSUB xSqTerm .one

lemma eval_xSqMinus1 (x : ℝ) (hx : 1 < x) :
    EMLTerm₁.eval x xSqMinus1 = x ^ 2 - 1 := by
  have hxpos : 0 < x := by linarith
  show EMLTerm₁.eval x (mkSUB xSqTerm .one) = _
  rw [eval_mkSUB x xSqTerm .one (by rw [eval_xSqTerm x hxpos]; positivity),
      eval_xSqTerm x hxpos]
  rfl

/-- `√(x² − 1)` term, via `exp(½ · log(x² − 1))`.  This requires
`log(x² − 1) > 0`, i.e. `x² − 1 > 1`, i.e. `x² > 2`, i.e. `√2 < x`. -/
def sqrtXSqMinus1 : EMLTerm₁ := mkEXP (mkHALVE (mkLOG xSqMinus1))

lemma sqrt_two_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

lemma sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  have h : Real.sqrt 2 < Real.sqrt 4 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  linarith

lemma sqrt_two_gt_one : (1 : ℝ) < Real.sqrt 2 := by
  have h : Real.sqrt 1 < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [Real.sqrt_one] at h; exact h

lemma log_xSqMinus1_pos {x : ℝ} (hx : Real.sqrt 2 < x) :
    0 < Real.log (x ^ 2 - 1) := by
  have h1 : 1 < x ^ 2 - 1 := by
    have hx0 : 0 < x := by linarith [sqrt_two_pos]
    have hx2 : 2 < x ^ 2 := by
      have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
      nlinarith [sqrt_two_pos]
    linarith
  exact Real.log_pos h1

lemma eval_sqrtXSqMinus1 (x : ℝ) (hx : Real.sqrt 2 < x) :
    EMLTerm₁.eval x sqrtXSqMinus1 = Real.sqrt (x ^ 2 - 1) := by
  have hx1 : 1 < x := lt_trans sqrt_two_gt_one hx
  have hxpos : 0 < x := by linarith
  have hSqM1_pos : 0 < x ^ 2 - 1 := xSqMinus1_pos hx1
  have hLog_pos : 0 < Real.log (x ^ 2 - 1) := log_xSqMinus1_pos hx
  show EMLTerm₁.eval x (mkEXP (mkHALVE (mkLOG xSqMinus1))) = _
  rw [eval_mkEXP]
  have hLOG_eval : EMLTerm₁.eval x (mkLOG xSqMinus1) = Real.log (x ^ 2 - 1) := by
    rw [eval_mkLOG, eval_xSqMinus1 x hx1]
  have hLOG_pos' : 0 < EMLTerm₁.eval x (mkLOG xSqMinus1) := by
    rw [hLOG_eval]; exact hLog_pos
  rw [eval_mkHALVE x _ hLOG_pos', hLOG_eval]
  -- Goal: exp(log(x² − 1) / 2) = √(x² − 1).
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hSqM1_pos]
  ring_nf

/-! ### Sum `x + √(x²−1)` and final logarithm. -/

def xPlusSqrt : EMLTerm₁ := mkADD .var sqrtXSqMinus1

lemma eval_xPlusSqrt (x : ℝ) (hx : Real.sqrt 2 < x) :
    EMLTerm₁.eval x xPlusSqrt = x + Real.sqrt (x ^ 2 - 1) := by
  show EMLTerm₁.eval x (mkADD .var sqrtXSqMinus1) = _
  rw [eval_mkADD, eval_sqrtXSqMinus1 x hx]
  rfl

/-- The arcosh witness: `log(x + √(x²−1))`. -/
def arcoshTerm : EMLTerm₁ := mkLOG xPlusSqrt

lemma eval_arcoshTerm (x : ℝ) (hx : Real.sqrt 2 < x) :
    EMLTerm₁.eval x arcoshTerm = Real.arcosh x := by
  show EMLTerm₁.eval x (mkLOG xPlusSqrt) = _
  rw [eval_mkLOG, eval_xPlusSqrt x hx]
  rw [Real.arcosh]

/--
The honest version (positivity hypothesis required because `mkHALVE` needs
its argument positive, which forces `log(x² − 1) > 0`, i.e. `x² > 2`, i.e.
`√2 < x`).  The stricter domain `x > √2` ⊂ `x ≥ 1` is sufficient for the
identity `arcosh x = log(x + √(x² − 1))` (which is the textbook formula).
-/
theorem emlterm1_for_arcosh :
    ∃ t : EMLTerm₁, ∀ x : ℝ, Real.sqrt 2 < x →
      EMLTerm₁.eval x t = Real.arcosh x :=
  ⟨arcoshTerm, eval_arcoshTerm⟩

end EML
