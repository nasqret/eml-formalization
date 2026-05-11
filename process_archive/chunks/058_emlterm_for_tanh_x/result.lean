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

/-- `mkEXP T` evaluates to `exp(eval T)` unconditionally. -/
def mkEXP (T : EMLTerm₁) : EMLTerm₁ := .eml T .one

lemma eval_mkEXP (x : ℝ) (T : EMLTerm₁) :
    EMLTerm₁.eval x (mkEXP T) = Real.exp (EMLTerm₁.eval x T) := by
  simp [mkEXP, EMLTerm₁.eval, Real.log_one]

/-- `mkLOG T` evaluates to `log(eval T)` unconditionally
    (uses the chunk 052 trick). -/
def mkLOG (T : EMLTerm₁) : EMLTerm₁ := .eml .one (.eml (.eml .one T) .one)

lemma eval_mkLOG (x : ℝ) (T : EMLTerm₁) :
    EMLTerm₁.eval x (mkLOG T) = Real.log (EMLTerm₁.eval x T) := by
  show Real.exp 1 - Real.log (Real.exp (Real.exp 1 - Real.log (EMLTerm₁.eval x T))
        - Real.log 1) = _
  rw [Real.log_one, sub_zero, Real.log_exp]; ring

/-- `mkSUB A B` for positive A. -/
def mkSUB (A B : EMLTerm₁) : EMLTerm₁ := .eml (mkLOG A) (mkEXP B)

lemma eval_mkSUB (x : ℝ) (A B : EMLTerm₁) (hA : 0 < EMLTerm₁.eval x A) :
    EMLTerm₁.eval x (mkSUB A B) = EMLTerm₁.eval x A - EMLTerm₁.eval x B := by
  show Real.exp (EMLTerm₁.eval x (mkLOG A)) -
       Real.log (EMLTerm₁.eval x (mkEXP B)) = _
  rw [eval_mkLOG, eval_mkEXP, Real.exp_log hA, Real.log_exp]

/-- `mkNEG T` evaluates to `-(eval T)` unconditionally
    (uses the `(exp t - t) - exp t = -t` trick). -/
def mkNEG (T : EMLTerm₁) : EMLTerm₁ :=
  .eml (mkLOG (.eml T (.eml T .one))) (.eml (.eml T .one) .one)

lemma exp_sub_self_pos (t : ℝ) : 0 < Real.exp t - t := by
  linarith [Real.add_one_le_exp t]

lemma eval_mkNEG (x : ℝ) (T : EMLTerm₁) :
    EMLTerm₁.eval x (mkNEG T) = -(EMLTerm₁.eval x T) := by
  set t := EMLTerm₁.eval x T with ht
  -- inner1 := eml T one → exp t.
  have h1 : EMLTerm₁.eval x (.eml T .one) = Real.exp t := by
    show Real.exp t - Real.log (EMLTerm₁.eval x .one) = _
    show Real.exp t - Real.log 1 = _
    rw [Real.log_one, sub_zero]
  -- inner2 := eml T (eml T one) → exp t - t.
  have h2 : EMLTerm₁.eval x (.eml T (.eml T .one)) = Real.exp t - t := by
    show Real.exp t - Real.log (EMLTerm₁.eval x (.eml T .one)) = _
    rw [h1, Real.log_exp]
  -- mkLOG inner2 → log(exp t - t).
  have h3 : EMLTerm₁.eval x (mkLOG (.eml T (.eml T .one)))
      = Real.log (Real.exp t - t) := by
    rw [eval_mkLOG, h2]
  -- exp(eval (mkLOG ...)) - log(eval (eml (eml T one) one))
  --   = exp(log(exp t - t)) - log(exp(exp t)) = (exp t - t) - exp t = -t.
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

/-! ### `mkHALVE P` for positive P (chunk 052 style) -/

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

/-! ### exp x, exp(-x), cosh x, etc. -/

def expxTerm : EMLTerm₁ := .eml .var .one

lemma eval_expxTerm (x : ℝ) : EMLTerm₁.eval x expxTerm = Real.exp x := by
  simp [expxTerm, EMLTerm₁.eval, Real.log_one]

/-- `exp(-x)` term using `mkNEG`. -/
def expnegxTerm : EMLTerm₁ := .eml (mkNEG .var) .one

lemma eval_expnegxTerm (x : ℝ) : EMLTerm₁.eval x expnegxTerm = Real.exp (-x) := by
  show Real.exp (EMLTerm₁.eval x (mkNEG .var)) - Real.log 1 = _
  rw [eval_mkNEG, Real.log_one, sub_zero]
  show Real.exp (-(EMLTerm₁.eval x .var)) = _
  rfl

/-- `cosh x` term: halve(exp x + exp(-x)). -/
def coshTerm : EMLTerm₁ := mkHALVE (mkADD expxTerm expnegxTerm)

lemma eval_coshTerm (x : ℝ) : EMLTerm₁.eval x coshTerm = Real.cosh x := by
  have hsum : EMLTerm₁.eval x (mkADD expxTerm expnegxTerm) = Real.exp x + Real.exp (-x) := by
    rw [eval_mkADD, eval_expxTerm, eval_expnegxTerm]
  have hsum_pos : 0 < EMLTerm₁.eval x (mkADD expxTerm expnegxTerm) := by
    rw [hsum]; positivity
  show EMLTerm₁.eval x (mkHALVE (mkADD expxTerm expnegxTerm)) = _
  rw [eval_mkHALVE x _ hsum_pos, hsum, Real.cosh_eq]

lemma cosh_pos (x : ℝ) : 0 < Real.cosh x := by
  rw [Real.cosh_eq]; positivity

lemma coshTerm_pos (x : ℝ) : 0 < EMLTerm₁.eval x coshTerm := by
  rw [eval_coshTerm]; exact cosh_pos x

/-! ### Division of two positive terms via `mkADD` and `mkNEG` of logs.

`mkDIV A B` evaluates to `eval A / eval B` when `eval A > 0` and `eval B > 0`. -/
def mkDIV (A B : EMLTerm₁) : EMLTerm₁ :=
  mkEXP (mkADD (mkLOG A) (mkNEG (mkLOG B)))

lemma eval_mkDIV (x : ℝ) (A B : EMLTerm₁)
    (hA : 0 < EMLTerm₁.eval x A) (hB : 0 < EMLTerm₁.eval x B) :
    EMLTerm₁.eval x (mkDIV A B) = EMLTerm₁.eval x A / EMLTerm₁.eval x B := by
  show EMLTerm₁.eval x (mkEXP (mkADD (mkLOG A) (mkNEG (mkLOG B)))) = _
  rw [eval_mkEXP, eval_mkADD, eval_mkNEG, eval_mkLOG, eval_mkLOG]
  rw [Real.exp_add, Real.exp_log hA, Real.exp_neg, Real.exp_log hB]
  rw [div_eq_mul_inv]

/-! ### `tanhTerm := mkSUB (exp x / cosh x) one`, since `tanh x = exp x / cosh x − 1`. -/

/-- The "tanh+1" helper: `exp x / cosh x = tanh x + 1`. -/
def tanhPlusTerm : EMLTerm₁ := mkDIV expxTerm coshTerm

lemma eval_tanhPlusTerm (x : ℝ) :
    EMLTerm₁.eval x tanhPlusTerm = Real.exp x / Real.cosh x := by
  show EMLTerm₁.eval x (mkDIV expxTerm coshTerm) = _
  have hA : 0 < EMLTerm₁.eval x expxTerm := by
    rw [eval_expxTerm]; exact Real.exp_pos _
  have hB : 0 < EMLTerm₁.eval x coshTerm := coshTerm_pos x
  rw [eval_mkDIV x expxTerm coshTerm hA hB, eval_expxTerm, eval_coshTerm]

lemma tanhPlus_eq_tanh_add_one (x : ℝ) :
    Real.exp x / Real.cosh x = Real.tanh x + 1 := by
  have hc : Real.cosh x ≠ 0 := (cosh_pos x).ne'
  rw [Real.tanh_eq_sinh_div_cosh]
  rw [div_add_one hc]
  rw [Real.sinh_eq, Real.cosh_eq]
  field_simp
  ring

lemma tanhPlusTerm_pos (x : ℝ) : 0 < EMLTerm₁.eval x tanhPlusTerm := by
  rw [eval_tanhPlusTerm]
  exact div_pos (Real.exp_pos _) (cosh_pos x)

/-- The final `tanh x` term. -/
def tanhTerm : EMLTerm₁ := mkSUB tanhPlusTerm .one

lemma eval_tanhTerm (x : ℝ) : EMLTerm₁.eval x tanhTerm = Real.tanh x := by
  show EMLTerm₁.eval x (mkSUB tanhPlusTerm .one) = _
  rw [eval_mkSUB x tanhPlusTerm .one (tanhPlusTerm_pos x), eval_tanhPlusTerm]
  show Real.exp x / Real.cosh x - 1 = _
  have h := tanhPlus_eq_tanh_add_one x
  linarith

theorem emlterm1_for_tanh :
    ∃ t : EMLTerm₁, ∀ x : ℝ, EMLTerm₁.eval x t = Real.tanh x :=
  ⟨tanhTerm, eval_tanhTerm⟩

end EML
