import Mathlib

namespace EML

inductive EMLTerm₁ : Type
  | one : EMLTerm₁
  | var : EMLTerm₁
  | eml : EMLTerm₁ → EMLTerm₁ → EMLTerm₁
  deriving Repr

noncomputable def EMLTerm₁.eval (x : ℝ) : EMLTerm₁ → ℝ
  | .one => 1
  | .var => x
  | .eml t u => Real.exp (EMLTerm₁.eval x t) - Real.log (EMLTerm₁.eval x u)

/-- Term that evaluates to `Real.log (eval x T)` for any `T` (unconditionally). -/
def mkLOG (T : EMLTerm₁) : EMLTerm₁ := .eml .one (.eml (.eml .one T) .one)

/-- Term that evaluates to `Real.exp (eval x T)` for any `T` (unconditionally). -/
def mkEXP (T : EMLTerm₁) : EMLTerm₁ := .eml T .one

/-- Term that evaluates to `eval x A - eval x B` when `eval x A > 0`. -/
def mkSUB (A B : EMLTerm₁) : EMLTerm₁ := .eml (mkLOG A) (mkEXP B)

-- ═══════════════════════════════════════════════════════════
-- Evaluation lemmas for helpers
-- ═══════════════════════════════════════════════════════════

lemma eval_mkEXP (x : ℝ) (T : EMLTerm₁) :
    EMLTerm₁.eval x (mkEXP T) = Real.exp (EMLTerm₁.eval x T) := by
  simp [mkEXP, EMLTerm₁.eval, Real.log_one]

/-
`mkLOG T` evaluates to `log(eval T)` unconditionally.
    Proof: eval = exp(1) - log(exp(exp(1) - log(eval T)) - log(1))
         = e - log(exp(e - log(eval T)))  (log 1 = 0)
         = e - (e - log(eval T))          (log ∘ exp = id)
         = log(eval T)                    (ring)
-/
lemma eval_mkLOG (x : ℝ) (T : EMLTerm₁) :
    EMLTerm₁.eval x (mkLOG T) = Real.log (EMLTerm₁.eval x T) := by
  -- By definition of $eval$, we know that $eval x (mkLOG T) = exp(1) - log(exp(exp(1) - log(eval T)) - log(1))$.
  have h_eval_mkLOG : EMLTerm₁.eval x (mkLOG T) = Real.exp 1 - Real.log (Real.exp (Real.exp 1 - Real.log (EMLTerm₁.eval x T)) - Real.log 1) := by
    rfl;
  by_cases h : EMLTerm₁.eval x T = 0 <;> simp_all +decide [ Real.exp_ne_zero, sub_eq_add_neg ]

/-
`mkSUB A B` evaluates to `eval A - eval B` when `eval A > 0`.
    Proof: uses `eval_mkLOG`, `eval_mkEXP`, `exp(log(a)) = a` for `a > 0`,
    and `log(exp(b)) = b`.
-/
lemma eval_mkSUB (x : ℝ) (A B : EMLTerm₁) (hA : 0 < EMLTerm₁.eval x A) :
    EMLTerm₁.eval x (mkSUB A B) = EMLTerm₁.eval x A - EMLTerm₁.eval x B := by
  unfold mkSUB; simp +decide [ *, EMLTerm₁.eval ] ; ring;
  rw [ eval_mkLOG, eval_mkEXP, Real.exp_log hA, Real.log_exp ]

-- ═══════════════════════════════════════════════════════════
-- Constant terms and evaluation lemmas
-- ═══════════════════════════════════════════════════════════

def E_term : EMLTerm₁ := .eml .one .one

def EM1_term : EMLTerm₁ := .eml .one E_term

def EM2_term : EMLTerm₁ := mkSUB EM1_term .one

def TWO_term : EMLTerm₁ := mkSUB E_term EM2_term

lemma eval_E (x : ℝ) : EMLTerm₁.eval x E_term = Real.exp 1 := by
  simp [E_term, EMLTerm₁.eval, Real.log_one]

lemma eval_EM1 (x : ℝ) : EMLTerm₁.eval x EM1_term = Real.exp 1 - 1 := by
  simp [EM1_term, E_term, EMLTerm₁.eval, Real.log_one, Real.log_exp]

lemma EM1_pos : (0 : ℝ) < Real.exp 1 - 1 := by
  norm_num [ Real.exp_pos ]

lemma eval_EM2 (x : ℝ) : EMLTerm₁.eval x EM2_term = Real.exp 1 - 2 := by
  rw [ show EM2_term = mkSUB EM1_term .one from rfl, eval_mkSUB ];
  · linarith [ eval_EM1 x, show EMLTerm₁.eval x EMLTerm₁.one = 1 from by rfl ];
  · exact eval_EM1 x ▸ EM1_pos

lemma eval_TWO (x : ℝ) : EMLTerm₁.eval x TWO_term = 2 := by
  rw [ show TWO_term = mkSUB E_term EM2_term from rfl, eval_mkSUB ];
  · rw [ eval_E, eval_EM2 ] ; ring;
  · exact eval_E x ▸ Real.exp_pos _

-- ═══════════════════════════════════════════════════════════
-- ONE_PLUS_LOG2_term: evaluates to 1 + log 2
-- ═══════════════════════════════════════════════════════════

/-- `eml(one, exp(sub(EM1, log(TWO))))` evaluates to `1 + log 2`.
    Proof: eval = exp(1) - log(exp((e-1) - log(2)))
         = e - ((e-1) - log(2))
         = 1 + log(2) -/
def ONE_PLUS_LOG2_term : EMLTerm₁ :=
  .eml .one (mkEXP (mkSUB EM1_term (mkLOG TWO_term)))

lemma eval_ONE_PLUS_LOG2 (x : ℝ) :
    EMLTerm₁.eval x ONE_PLUS_LOG2_term = 1 + Real.log 2 := by
  unfold ONE_PLUS_LOG2_term;
  rw [ show EMLTerm₁.eval x ( EMLTerm₁.one.eml ( mkEXP ( mkSUB EM1_term ( mkLOG TWO_term ) ) ) ) = Real.exp ( EMLTerm₁.eval x EMLTerm₁.one ) - Real.log ( EMLTerm₁.eval x ( mkEXP ( mkSUB EM1_term ( mkLOG TWO_term ) ) ) ) by rfl ] ; norm_num [ eval_mkEXP, eval_mkLOG, eval_mkSUB, eval_EM1, eval_TWO ] ; ring;
  rw [ show EMLTerm₁.eval x EMLTerm₁.one = 1 by rfl ] ; ring

lemma one_plus_log_two_pos : (0 : ℝ) < 1 + Real.log 2 := by
  positivity

-- ═══════════════════════════════════════════════════════════
-- Variable-dependent terms
-- ═══════════════════════════════════════════════════════════

/-- Evaluates to `(1 + log 2) - log(log x)` for `x > 1`.
    Uses `eml(mkLOG(ONE_PLUS_LOG2_term), mkLOG(var))`, which computes
    `exp(log(1+log 2)) - log(log x) = (1+log 2) - log(log x)`. -/
def one_plus_c_term : EMLTerm₁ :=
  .eml (mkLOG ONE_PLUS_LOG2_term) (mkLOG .var)

lemma eval_one_plus_c (x : ℝ) (hx : 1 < x) :
    EMLTerm₁.eval x one_plus_c_term =
    (1 + Real.log 2) - Real.log (Real.log x) := by
  -- Apply the definition of `eval` for `eml` terms.
  simp [one_plus_c_term, EMLTerm₁.eval];
  rw [ eval_mkLOG, eval_ONE_PLUS_LOG2, Real.exp_log one_plus_log_two_pos, eval_mkLOG, EMLTerm₁.eval ]

/-- The sqrt term: `mkEXP(mkEXP(mkSUB(one, one_plus_c_term)))`.
    For `x > 1`:
    eval = exp(exp(1 - ((1+log 2) - log(log x))))
         = exp(exp(log(log x) - log 2))
         = exp(exp(log(log x / 2)))        (log_div)
         = exp(log x / 2)                  (exp_log, log x / 2 > 0)
         = √x                              (exp(log x / 2) = x^(1/2) = √x) -/
def sqrt_term₂ : EMLTerm₁ := mkEXP (mkEXP (mkSUB .one one_plus_c_term))

lemma eval_sqrt₂ (x : ℝ) (hx : 1 < x) :
    EMLTerm₁.eval x sqrt_term₂ = Real.sqrt x := by
  convert eval_mkEXP x ( mkEXP ( mkSUB .one one_plus_c_term ) ) using 1;
  rw [ eval_mkEXP, eval_mkSUB ];
  · rw [ eval_one_plus_c x hx ] ; ring;
    rw [ Real.sqrt_eq_rpow, Real.rpow_def_of_pos ( by positivity ) ] ; norm_num [ EMLTerm₁.eval ] ; ring;
    rw [ Real.exp_add, Real.exp_neg, Real.exp_log, Real.exp_log ] <;> ring <;> norm_num [ Real.log_pos hx ];
  · exact zero_lt_one

-- ═══════════════════════════════════════════════════════════
-- Main theorem
-- ═══════════════════════════════════════════════════════════

theorem emlterm1_for_sqrt_x_gt_one :
    ∃ t : EMLTerm₁, ∀ x : ℝ, 1 < x → EMLTerm₁.eval x t = Real.sqrt x :=
  ⟨sqrt_term₂, fun x hx => eval_sqrt₂ x hx⟩

end EML
