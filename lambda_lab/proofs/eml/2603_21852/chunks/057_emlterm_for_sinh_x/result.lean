import Mathlib

namespace EML

/-- One-variable EML term grammar. -/
inductive EMLTerm₁ : Type
  | one : EMLTerm₁
  | var : EMLTerm₁
  | eml : EMLTerm₁ → EMLTerm₁ → EMLTerm₁
  deriving Repr

noncomputable def EMLTerm₁.eval (x : ℝ) : EMLTerm₁ → ℝ
  | .one      => 1
  | .var      => x
  | .eml t u  => Real.exp (EMLTerm₁.eval x t) - Real.log (EMLTerm₁.eval x u)

/-! ### Generic combinators -/

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
  have h0 : Real.exp 0 = 1 := Real.exp_zero
  have h1 : Real.exp 0 < Real.exp 1 := Real.exp_strictMono (by norm_num)
  linarith

lemma eval_EM2 (x : ℝ) : EMLTerm₁.eval x EM2_term = Real.exp 1 - 2 := by
  show EMLTerm₁.eval x (mkSUB EM1_term .one) = _
  rw [eval_mkSUB x EM1_term .one (by rw [eval_EM1]; exact EM1_pos)]
  rw [eval_EM1]; show (Real.exp 1 - 1) - 1 = Real.exp 1 - 2; ring

lemma eval_TWO (x : ℝ) : EMLTerm₁.eval x TWO_term = 2 := by
  show EMLTerm₁.eval x (mkSUB E_term EM2_term) = _
  rw [eval_mkSUB x E_term EM2_term (by rw [eval_E]; exact Real.exp_pos _)]
  rw [eval_E, eval_EM2]; ring

/-! ### `mkADD A B` (chunk 040) -/

def mkADD (A B : EMLTerm₁) : EMLTerm₁ :=
  .eml
    (.eml .one (.eml (.eml .one (.eml A .one)) .one))
    (.eml
      (.eml (.eml .one (.eml (.eml .one (.eml A (.eml A .one))) .one))
            (.eml B .one))
      .one)

lemma exp_sub_self_pos (t : ℝ) : 0 < Real.exp t - t := by
  linarith [Real.add_one_le_exp t]

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

/-! ### `−x` term and `exp x`, `exp(-x)` -/

def expxTerm : EMLTerm₁ := .eml .var .one

lemma eval_expxTerm (x : ℝ) : EMLTerm₁.eval x expxTerm = Real.exp x := by
  simp [expxTerm, EMLTerm₁.eval, Real.log_one]

private def w' : EMLTerm₁ := .eml .var (.eml .var .one)
private def expx' : EMLTerm₁ := .eml .var .one
private def logw' : EMLTerm₁ := .eml .one (.eml (.eml .one w') .one)
def negXTerm : EMLTerm₁ := .eml logw' (.eml expx' .one)

lemma eval_negXTerm (x : ℝ) : EMLTerm₁.eval x negXTerm = -x := by
  have hw' : EMLTerm₁.eval x w' = Real.exp x - x := by
    simp [w', EMLTerm₁.eval, Real.log_one, Real.log_exp]
  have hlogw' : EMLTerm₁.eval x logw' = Real.log (Real.exp x - x) := by
    show Real.exp 1 - Real.log (EMLTerm₁.eval x (.eml (.eml .one w') .one)) = _
    show Real.exp 1 - Real.log
      (Real.exp (EMLTerm₁.eval x (.eml .one w')) - Real.log 1) = _
    show Real.exp 1 - Real.log
      (Real.exp (Real.exp 1 - Real.log (EMLTerm₁.eval x w')) - Real.log 1) = _
    rw [hw', Real.log_one, sub_zero, Real.log_exp]; ring
  have hexpx' : EMLTerm₁.eval x expx' = Real.exp x := by
    show Real.exp x - Real.log (EMLTerm₁.eval x .one) = _
    rw [show EMLTerm₁.eval x .one = 1 from rfl, Real.log_one, sub_zero]
  have hexpx : EMLTerm₁.eval x (.eml expx' .one) = Real.exp (Real.exp x) := by
    show Real.exp (EMLTerm₁.eval x expx') - Real.log (EMLTerm₁.eval x .one) = _
    rw [hexpx', show EMLTerm₁.eval x .one = 1 from rfl, Real.log_one, sub_zero]
  show Real.exp (EMLTerm₁.eval x logw') - Real.log (EMLTerm₁.eval x (.eml expx' .one)) = _
  rw [hlogw', hexpx, Real.exp_log (by linarith [Real.add_one_le_exp x]), Real.log_exp]
  ring

def expnegxTerm : EMLTerm₁ := .eml negXTerm .one

lemma eval_expnegxTerm (x : ℝ) : EMLTerm₁.eval x expnegxTerm = Real.exp (-x) := by
  show Real.exp (EMLTerm₁.eval x negXTerm) - Real.log 1 = _
  rw [eval_negXTerm, Real.log_one, sub_zero]

/-! ### Final witness: `sinh x = halve(exp x) − halve(exp(−x))` -/

def halfExpXTerm : EMLTerm₁ := mkHALVE expxTerm
def halfExpNegXTerm : EMLTerm₁ := mkHALVE expnegxTerm

lemma eval_halfExpX (x : ℝ) : EMLTerm₁.eval x halfExpXTerm = Real.exp x / 2 := by
  show EMLTerm₁.eval x (mkHALVE expxTerm) = _
  rw [eval_mkHALVE x _ (by rw [eval_expxTerm]; exact Real.exp_pos _), eval_expxTerm]

lemma eval_halfExpNegX (x : ℝ) :
    EMLTerm₁.eval x halfExpNegXTerm = Real.exp (-x) / 2 := by
  show EMLTerm₁.eval x (mkHALVE expnegxTerm) = _
  rw [eval_mkHALVE x _ (by rw [eval_expnegxTerm]; exact Real.exp_pos _),
      eval_expnegxTerm]

/-- `sinh x` term: mkSUB halfExpXTerm halfExpNegXTerm. -/
def sinhTerm : EMLTerm₁ := mkSUB halfExpXTerm halfExpNegXTerm

lemma eval_sinhTerm (x : ℝ) : EMLTerm₁.eval x sinhTerm = Real.sinh x := by
  have hA_pos : 0 < EMLTerm₁.eval x halfExpXTerm := by
    rw [eval_halfExpX]; positivity
  show EMLTerm₁.eval x (mkSUB halfExpXTerm halfExpNegXTerm) = _
  rw [eval_mkSUB x halfExpXTerm halfExpNegXTerm hA_pos,
      eval_halfExpX, eval_halfExpNegX, Real.sinh_eq]
  ring

theorem emlterm1_for_sinh :
    ∃ t : EMLTerm₁, ∀ x : ℝ, EMLTerm₁.eval x t = Real.sinh x :=
  ⟨sinhTerm, eval_sinhTerm⟩

end EML
