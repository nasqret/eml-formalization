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

/-! ### Generic `mkNEG Y` (chunk 036 generalized) -/

/-- `mkNEG Y` evaluates to `-eval Y` for any `Y` and any input `x`. -/
def mkNEG (Y : EMLTerm₁) : EMLTerm₁ :=
  let wY := EMLTerm₁.eml Y (.eml Y .one)
  let logwY := EMLTerm₁.eml .one (.eml (.eml .one wY) .one)
  let expY := EMLTerm₁.eml Y .one
  EMLTerm₁.eml logwY (.eml expY .one)

lemma eval_mkNEG (x : ℝ) (Y : EMLTerm₁) :
    EMLTerm₁.eval x (mkNEG Y) = -(EMLTerm₁.eval x Y) := by
  set y := EMLTerm₁.eval x Y with hy
  have hOne : EMLTerm₁.eval x .one = 1 := rfl
  -- expY := eml Y .one → exp y.
  have hExpY : EMLTerm₁.eval x (.eml Y .one) = Real.exp y := by
    show Real.exp y - Real.log (EMLTerm₁.eval x .one) = _
    rw [hOne, Real.log_one, sub_zero]
  -- wY := eml Y (eml Y .one) → exp y - y.
  have hwY : EMLTerm₁.eval x (.eml Y (.eml Y .one)) = Real.exp y - y := by
    show Real.exp y - Real.log (EMLTerm₁.eval x (.eml Y .one)) = _
    rw [hExpY, Real.log_exp]
  have hExpYmY_pos : 0 < Real.exp y - y := by
    linarith [Real.add_one_le_exp y]
  -- (eml .one wY) → exp 1 - log(exp y - y).
  have h1 : EMLTerm₁.eval x (.eml .one (.eml Y (.eml Y .one))) =
      Real.exp 1 - Real.log (Real.exp y - y) := by
    show Real.exp 1 - Real.log (EMLTerm₁.eval x (.eml Y (.eml Y .one))) = _
    rw [hwY]
  -- (eml (eml .one wY) .one) → exp(exp 1 - log(exp y - y)).
  have h2 : EMLTerm₁.eval x (.eml (.eml .one (.eml Y (.eml Y .one))) .one) =
      Real.exp (Real.exp 1 - Real.log (Real.exp y - y)) := by
    show Real.exp (EMLTerm₁.eval x (.eml .one (.eml Y (.eml Y .one)))) -
      Real.log (EMLTerm₁.eval x .one) = _
    rw [h1, hOne, Real.log_one, sub_zero]
  -- logwY := eml .one (eml (eml .one wY) .one) → log(exp y - y).
  have hlogwY : EMLTerm₁.eval x
      (EMLTerm₁.eml .one (.eml (.eml .one (.eml Y (.eml Y .one))) .one)) =
      Real.log (Real.exp y - y) := by
    show Real.exp 1 - Real.log
      (EMLTerm₁.eval x (.eml (.eml .one (.eml Y (.eml Y .one))) .one)) = _
    rw [h2, Real.log_exp]; ring
  -- (eml expY .one) → exp(exp y).
  have hExpExpY : EMLTerm₁.eval x (.eml (.eml Y .one) .one) =
      Real.exp (Real.exp y) := by
    show Real.exp (EMLTerm₁.eval x (.eml Y .one)) -
      Real.log (EMLTerm₁.eval x .one) = _
    rw [hExpY, hOne, Real.log_one, sub_zero]
  -- mkNEG Y = eml logwY (eml expY .one) → log(exp y - y) - exp y · (i.e., (exp y - y) - exp y = -y).
  show EMLTerm₁.eval x (mkNEG Y) = -y
  unfold mkNEG
  show Real.exp (EMLTerm₁.eval x
        (EMLTerm₁.eml .one (.eml (.eml .one (.eml Y (.eml Y .one))) .one))) -
       Real.log (EMLTerm₁.eval x (.eml (.eml Y .one) .one)) = -y
  rw [hlogwY, hExpExpY, Real.exp_log hExpYmY_pos, Real.log_exp]
  ring

/-! ### `mkADD A B` (chunk 040 style) -/

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

/-! ### Sigmoid construction -/

/-- `exp(-x)` term: `eml(mkNEG var, .one)`. -/
def expnegxTerm : EMLTerm₁ := mkEXP (mkNEG .var)

lemma eval_expnegxTerm (x : ℝ) : EMLTerm₁.eval x expnegxTerm = Real.exp (-x) := by
  show EMLTerm₁.eval x (mkEXP (mkNEG .var)) = _
  rw [eval_mkEXP, eval_mkNEG]
  rfl

/-- `1 + exp(-x)` term. -/
def onePlusExpNegX : EMLTerm₁ := mkADD .one expnegxTerm

lemma eval_onePlusExpNegX (x : ℝ) :
    EMLTerm₁.eval x onePlusExpNegX = 1 + Real.exp (-x) := by
  show EMLTerm₁.eval x (mkADD .one expnegxTerm) = _
  rw [eval_mkADD, eval_expnegxTerm]; rfl

lemma onePlusExpNegX_pos (x : ℝ) : 0 < EMLTerm₁.eval x onePlusExpNegX := by
  rw [eval_onePlusExpNegX]; positivity

/-- `log(1 + exp(-x))` term. -/
def logOnePlus : EMLTerm₁ := mkLOG onePlusExpNegX

lemma eval_logOnePlus (x : ℝ) :
    EMLTerm₁.eval x logOnePlus = Real.log (1 + Real.exp (-x)) := by
  show EMLTerm₁.eval x (mkLOG onePlusExpNegX) = _
  rw [eval_mkLOG, eval_onePlusExpNegX]

/-- `−log(1 + exp(-x))` term. -/
def negLogTerm : EMLTerm₁ := mkNEG logOnePlus

lemma eval_negLogTerm (x : ℝ) :
    EMLTerm₁.eval x negLogTerm = -Real.log (1 + Real.exp (-x)) := by
  show EMLTerm₁.eval x (mkNEG logOnePlus) = _
  rw [eval_mkNEG, eval_logOnePlus]

/-- Sigmoid: `exp(−log(1 + exp(−x))) = 1/(1 + exp(−x))`. -/
def sigmoidTerm : EMLTerm₁ := mkEXP negLogTerm

lemma eval_sigmoidTerm (x : ℝ) :
    EMLTerm₁.eval x sigmoidTerm = 1 / (1 + Real.exp (-x)) := by
  show EMLTerm₁.eval x (mkEXP negLogTerm) = _
  rw [eval_mkEXP, eval_negLogTerm]
  rw [Real.exp_neg]
  rw [Real.exp_log (by positivity : (0:ℝ) < 1 + Real.exp (-x))]
  rw [one_div]

theorem emlterm1_for_sigmoid :
    ∃ t : EMLTerm₁, ∀ x : ℝ, EMLTerm₁.eval x t = 1 / (1 + Real.exp (-x)) :=
  ⟨sigmoidTerm, eval_sigmoidTerm⟩

end EML
