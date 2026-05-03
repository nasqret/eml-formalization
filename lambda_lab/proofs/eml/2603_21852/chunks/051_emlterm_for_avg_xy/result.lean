import Mathlib

namespace EML

/-- Two-variable EML term grammar (lifted from chunk 041). -/
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

/-! ### Generic combinators (chunk 052 style, lifted to two variables) -/

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

/-! ### Constant `2` term -/

def E_term : EMLTerm₂ := .eml .one .one
def EM1_term : EMLTerm₂ := .eml .one E_term
def EM2_term : EMLTerm₂ := mkSUB EM1_term .one
def TWO_term : EMLTerm₂ := mkSUB E_term EM2_term

lemma eval_E (x y : ℝ) : EMLTerm₂.eval x y E_term = Real.exp 1 := by
  simp [E_term, EMLTerm₂.eval, Real.log_one]

lemma eval_EM1 (x y : ℝ) : EMLTerm₂.eval x y EM1_term = Real.exp 1 - 1 := by
  simp [EM1_term, E_term, EMLTerm₂.eval, Real.log_one, Real.log_exp]

lemma EM1_pos : (0 : ℝ) < Real.exp 1 - 1 := by
  have h1 : Real.exp 0 < Real.exp 1 := Real.exp_strictMono (by norm_num)
  rw [Real.exp_zero] at h1; linarith

lemma eval_EM2 (x y : ℝ) : EMLTerm₂.eval x y EM2_term = Real.exp 1 - 2 := by
  show EMLTerm₂.eval x y (mkSUB EM1_term .one) = _
  rw [eval_mkSUB x y EM1_term .one (by rw [eval_EM1]; exact EM1_pos)]
  rw [eval_EM1]; show (Real.exp 1 - 1) - 1 = Real.exp 1 - 2; ring

lemma eval_TWO (x y : ℝ) : EMLTerm₂.eval x y TWO_term = 2 := by
  show EMLTerm₂.eval x y (mkSUB E_term EM2_term) = _
  rw [eval_mkSUB x y E_term EM2_term (by rw [eval_E]; exact Real.exp_pos _)]
  rw [eval_E, eval_EM2]; ring

/-! ### `mkADD A B` (chunk 040 style, unconditional) -/

def mkADD (A B : EMLTerm₂) : EMLTerm₂ :=
  .eml
    (.eml .one (.eml (.eml .one (.eml A .one)) .one))
    (.eml
      (.eml (.eml .one (.eml (.eml .one (.eml A (.eml A .one))) .one))
            (.eml B .one))
      .one)

lemma exp_sub_self_pos (t : ℝ) : 0 < Real.exp t - t := by
  linarith [Real.add_one_le_exp t]

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

/-! ### `mkHALVE P` for positive P -/

def mkHALVE (P : EMLTerm₂) : EMLTerm₂ :=
  let Pplus2 := mkADD P TWO_term
  let aT := .eml (mkLOG Pplus2) (mkEXP (mkLOG TWO_term))
  let bT := .eml (mkLOG Pplus2) (mkEXP (mkLOG P))
  let logDiff := EMLTerm₂.eml (mkLOG aT) (mkEXP bT)
  mkEXP logDiff

lemma log_two_le_one : Real.log 2 ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  linarith

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

/-! ### Final: avgTerm = mkHALVE(mkADD varX varY) when x + y > 0 -/

def avgTerm : EMLTerm₂ := mkHALVE (mkADD .varX .varY)

lemma eval_avgTerm (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    EMLTerm₂.eval x y avgTerm = (x + y) / 2 := by
  have hsum : EMLTerm₂.eval x y (mkADD .varX .varY) = x + y := by
    rw [eval_mkADD]; rfl
  have hsum_pos : 0 < EMLTerm₂.eval x y (mkADD .varX .varY) := by
    rw [hsum]; linarith
  show EMLTerm₂.eval x y (mkHALVE (mkADD .varX .varY)) = _
  rw [eval_mkHALVE x y _ hsum_pos, hsum]

/--
The honest version (positivity hypothesis required because the underlying
`mkHALVE` combinator divides by `2` via `exp(log p − log 2)`, which needs
`p = x + y > 0`). The textbook identity `avg(x, y) = (x + y)/2` extends to
all reals by case analysis, but the EML `mkHALVE` combinator is only
positivity-safe.
-/
theorem emlterm2_for_avg :
    ∃ t : EMLTerm₂, ∀ x y : ℝ, 0 < x → 0 < y →
      EMLTerm₂.eval x y t = (x + y) / 2 :=
  ⟨avgTerm, eval_avgTerm⟩

end EML
