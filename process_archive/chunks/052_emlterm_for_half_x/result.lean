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

/-! ### Helper combinators -/

/-- `mkEXP T` evaluates to `exp(eval T)` unconditionally. -/
def mkEXP (T : EMLTerm₁) : EMLTerm₁ := .eml T .one

lemma eval_mkEXP (x : ℝ) (T : EMLTerm₁) :
    EMLTerm₁.eval x (mkEXP T) = Real.exp (EMLTerm₁.eval x T) := by
  simp [mkEXP, EMLTerm₁.eval, Real.log_one]

/-- `mkLOG T` evaluates to `log(eval T)` unconditionally. -/
def mkLOG (T : EMLTerm₁) : EMLTerm₁ := .eml .one (.eml (.eml .one T) .one)

lemma eval_mkLOG (x : ℝ) (T : EMLTerm₁) :
    EMLTerm₁.eval x (mkLOG T) = Real.log (EMLTerm₁.eval x T) := by
  show Real.exp 1 - Real.log (Real.exp (Real.exp 1 - Real.log (EMLTerm₁.eval x T))
        - Real.log 1) = _
  rw [Real.log_one, sub_zero, Real.log_exp]; ring

/-- `mkSUB A B` evaluates to `eval A - eval B` when `eval A > 0`. -/
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

/-! ### `x + 2` for x > 0 (chunk 040 add adapted) -/

/-- `x + 2` for x > 0. Uses chunk 040's add trick with `varY := TWO_term`. -/
def xPlusTwoTerm : EMLTerm₁ :=
  .eml
    (.eml .one (.eml (.eml .one (.eml .var .one)) .one))
    (.eml
      (.eml (.eml .one (.eml (.eml .one (.eml .var (.eml .var .one))) .one))
            (.eml TWO_term .one))
      .one)

lemma exp_sub_self_pos (x : ℝ) : 0 < Real.exp x - x := by
  linarith [Real.add_one_le_exp x]

lemma eval_xPlusTwo (x : ℝ) :
    EMLTerm₁.eval x xPlusTwoTerm = x + 2 := by
  -- Manual unfolding to keep control of intermediate forms.
  have hx_term : EMLTerm₁.eval x .var = x := rfl
  have hone_term : EMLTerm₁.eval x .one = 1 := rfl
  have h_TWO : EMLTerm₁.eval x TWO_term = 2 := eval_TWO x
  -- Subterm 1: `eml var one` → exp x.
  have h1 : EMLTerm₁.eval x (.eml .var .one) = Real.exp x := by
    show Real.exp x - Real.log 1 = Real.exp x
    rw [Real.log_one, sub_zero]
  -- Subterm 2: `eml one (eml var one)` → exp 1 - x.
  have h2 : EMLTerm₁.eval x (.eml .one (.eml .var .one)) = Real.exp 1 - x := by
    show Real.exp 1 - Real.log (EMLTerm₁.eval x (.eml .var .one)) = _
    rw [h1, Real.log_exp]
  -- Subterm 3: `eml (eml one (eml var one)) one` → exp(exp 1 - x).
  have h3 : EMLTerm₁.eval x (.eml (.eml .one (.eml .var .one)) .one)
      = Real.exp (Real.exp 1 - x) := by
    show Real.exp (EMLTerm₁.eval x (.eml .one (.eml .var .one))) - Real.log 1 = _
    rw [h2, Real.log_one, sub_zero]
  -- LHS: `eml one (eml (eml one (eml var one)) one)` → x.
  have hLHS : EMLTerm₁.eval x
      (.eml .one (.eml (.eml .one (.eml .var .one)) .one)) = x := by
    show Real.exp 1 - Real.log
      (EMLTerm₁.eval x (.eml (.eml .one (.eml .var .one)) .one)) = x
    rw [h3, Real.log_exp]; ring
  -- Subterm 4: `eml var (eml var one)` → exp x - x.
  have h4 : EMLTerm₁.eval x (.eml .var (.eml .var .one)) = Real.exp x - x := by
    show Real.exp x - Real.log (EMLTerm₁.eval x (.eml .var .one)) = _
    rw [h1, Real.log_exp]
  -- Subterm 5: `eml one (eml var (eml var one))` → exp 1 - log(exp x - x).
  have h5 : EMLTerm₁.eval x (.eml .one (.eml .var (.eml .var .one)))
      = Real.exp 1 - Real.log (Real.exp x - x) := by
    show Real.exp 1 - Real.log (EMLTerm₁.eval x (.eml .var (.eml .var .one))) = _
    rw [h4]
  -- Subterm 6: `eml (eml one (eml var (eml var one))) one`
  --         → exp(exp 1 - log(exp x - x)).
  have h6 : EMLTerm₁.eval x
      (.eml (.eml .one (.eml .var (.eml .var .one))) .one) =
      Real.exp (Real.exp 1 - Real.log (Real.exp x - x)) := by
    show Real.exp (EMLTerm₁.eval x (.eml .one (.eml .var (.eml .var .one))))
      - Real.log 1 = _
    rw [h5, Real.log_one, sub_zero]
  -- Subterm 7: `eml one (eml (eml one (eml var (eml var one))) one)`
  --         → log(exp x - x).
  have h7 : EMLTerm₁.eval x
      (.eml .one (.eml (.eml .one (.eml .var (.eml .var .one))) .one)) =
      Real.log (Real.exp x - x) := by
    show Real.exp 1 - Real.log
      (EMLTerm₁.eval x (.eml (.eml .one (.eml .var (.eml .var .one))) .one)) = _
    rw [h6, Real.log_exp]; ring
  -- Subterm 8: `eml TWO_term .one` → exp 2.
  have h8 : EMLTerm₁.eval x (.eml TWO_term .one) = Real.exp 2 := by
    show Real.exp (EMLTerm₁.eval x TWO_term) - Real.log 1 = _
    rw [h_TWO, Real.log_one, sub_zero]
  -- Subterm 9: `eml (eml one (eml (eml one (eml var (eml var one))) one)) (eml TWO_term one)`
  --         → exp(log(exp x - x)) - log(exp 2) = (exp x - x) - 2.
  have h9 : EMLTerm₁.eval x
      (.eml (.eml .one (.eml (.eml .one (.eml .var (.eml .var .one))) .one))
            (.eml TWO_term .one)) = Real.exp x - x - 2 := by
    show Real.exp (EMLTerm₁.eval x
        (.eml .one (.eml (.eml .one (.eml .var (.eml .var .one))) .one))) -
      Real.log (EMLTerm₁.eval x (.eml TWO_term .one)) = _
    rw [h7, h8, Real.exp_log (exp_sub_self_pos x), Real.log_exp]
  -- Subterm 10: RHS_inner = `eml (subterm9) one` → exp(exp x - x - 2).
  have h10 : EMLTerm₁.eval x (.eml
      (.eml (.eml .one (.eml (.eml .one (.eml .var (.eml .var .one))) .one))
            (.eml TWO_term .one))
      .one) = Real.exp (Real.exp x - x - 2) := by
    show Real.exp (EMLTerm₁.eval x
        (.eml (.eml .one (.eml (.eml .one (.eml .var (.eml .var .one))) .one))
              (.eml TWO_term .one))) - Real.log 1 = _
    rw [h9, Real.log_one, sub_zero]
  -- Outer: eml(LHS, RHS) = exp(x) - log(RHS).
  show Real.exp (EMLTerm₁.eval x
        (.eml .one (.eml (.eml .one (.eml .var .one)) .one))) -
       Real.log (EMLTerm₁.eval x (.eml
        (.eml (.eml .one (.eml (.eml .one (.eml .var (.eml .var .one))) .one))
              (.eml TWO_term .one))
        .one)) = _
  rw [hLHS, h10, Real.log_exp]; ring

lemma xPlusTwo_pos (x : ℝ) (hx : 0 < x) : 0 < EMLTerm₁.eval x xPlusTwoTerm := by
  rw [eval_xPlusTwo]; linarith

/-! ### `(x+2) − log 2` and `(x+2) − log x` -/

def aTerm : EMLTerm₁ := .eml (mkLOG xPlusTwoTerm) (mkEXP (mkLOG TWO_term))

lemma eval_aTerm (x : ℝ) (hx : 0 < x) :
    EMLTerm₁.eval x aTerm = (x + 2) - Real.log 2 := by
  show Real.exp (EMLTerm₁.eval x (mkLOG xPlusTwoTerm)) -
       Real.log (EMLTerm₁.eval x (mkEXP (mkLOG TWO_term))) = _
  rw [eval_mkLOG, eval_mkEXP, eval_mkLOG]
  rw [Real.exp_log (xPlusTwo_pos x hx), eval_xPlusTwo, eval_TWO, Real.log_exp]

def bTerm : EMLTerm₁ := .eml (mkLOG xPlusTwoTerm) (mkEXP (mkLOG .var))

lemma eval_bTerm (x : ℝ) (hx : 0 < x) :
    EMLTerm₁.eval x bTerm = (x + 2) - Real.log x := by
  show Real.exp (EMLTerm₁.eval x (mkLOG xPlusTwoTerm)) -
       Real.log (EMLTerm₁.eval x (mkEXP (mkLOG .var))) = _
  rw [eval_mkLOG, eval_mkEXP, eval_mkLOG]
  rw [Real.exp_log (xPlusTwo_pos x hx), eval_xPlusTwo]
  show (x + 2) - Real.log (Real.exp (Real.log (EMLTerm₁.eval x .var))) = _
  rw [show EMLTerm₁.eval x .var = x from rfl, Real.exp_log hx]

lemma aTerm_pos (x : ℝ) (hx : 0 < x) : 0 < EMLTerm₁.eval x aTerm := by
  rw [eval_aTerm x hx]
  have : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  linarith

lemma bTerm_pos (x : ℝ) (hx : 0 < x) : 0 < EMLTerm₁.eval x bTerm := by
  rw [eval_bTerm x hx]
  have h := Real.log_le_sub_one_of_pos hx
  linarith

/-! ### `log x − log 2` -/

def logDiffTerm : EMLTerm₁ := .eml (mkLOG aTerm) (mkEXP bTerm)

lemma eval_logDiffTerm (x : ℝ) (hx : 0 < x) :
    EMLTerm₁.eval x logDiffTerm = Real.log x - Real.log 2 := by
  show Real.exp (EMLTerm₁.eval x (mkLOG aTerm)) -
       Real.log (EMLTerm₁.eval x (mkEXP bTerm)) = _
  rw [eval_mkLOG, eval_mkEXP]
  rw [Real.exp_log (aTerm_pos x hx), Real.log_exp, eval_aTerm x hx, eval_bTerm x hx]
  ring

/-! ### Final witness: `x / 2` -/

def halfXTerm : EMLTerm₁ := mkEXP logDiffTerm

lemma eval_halfXTerm (x : ℝ) (hx : 0 < x) :
    EMLTerm₁.eval x halfXTerm = x / 2 := by
  show EMLTerm₁.eval x (mkEXP logDiffTerm) = _
  rw [eval_mkEXP, eval_logDiffTerm x hx]
  rw [Real.exp_sub, Real.exp_log hx, Real.exp_log (by norm_num : (0:ℝ) < 2)]

theorem emlterm1_for_half :
    ∃ t : EMLTerm₁, ∀ x : ℝ, 0 < x → EMLTerm₁.eval x t = x / 2 :=
  ⟨halfXTerm, eval_halfXTerm⟩

end EML
