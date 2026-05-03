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

/-! ## Building blocks -/

/-- `exp(a)` -/
def mkExp (t : EMLTerm₂) : EMLTerm₂ := .eml t .one

/-- `log(a)` for `a > 0` -/
def mkLog (t : EMLTerm₂) : EMLTerm₂ := .eml .one (.eml (.eml .one t) .one)

/-- The constant `0 = log(1)` -/
def mkZero : EMLTerm₂ := mkLog .one

/-- `1 - a` via `exp(0) - log(exp(a))` -/
def mkOneMinus (t : EMLTerm₂) : EMLTerm₂ := .eml mkZero (mkExp t)

/-- `-a` via `(exp(a) - a) - exp(a)` -/
def mkNeg (t : EMLTerm₂) : EMLTerm₂ :=
  .eml (mkLog (.eml t (mkExp t))) (mkExp (mkExp t))

/-- General subtraction `a - b` via `(a + exp(1-a)) - (b + exp(1-a))` -/
def mkSub (a b : EMLTerm₂) : EMLTerm₂ :=
  let oma := mkOneMinus a
  let apk := .eml oma (mkExp (mkNeg a))
  let bpk := .eml oma (mkExp (mkNeg b))
  .eml (mkLog apk) (mkExp bpk)

/-- Division `a/c` for `c > 0` via
    `exp(log(a+K) - log(c)) - exp((1-a) - log(c))` where `K = exp(1-a)` -/
def mkDiv (a c : EMLTerm₂) : EMLTerm₂ :=
  let oma := mkOneMinus a
  let apk := .eml oma (mkExp (mkNeg a))
  let logApk := mkLog apk
  let logC := mkLog c
  let f := .eml (mkLog logApk) (mkExp logC)
  let g := mkSub oma logC
  .eml f (mkExp (mkExp g))

/-- The witness term for `log_x(y)` -/
def logTerm : EMLTerm₂ := mkDiv (mkLog .varY) (mkLog .varX)

/-! ## Key inequalities -/

lemma exp_sub_self_pos (v : ℝ) : 0 < Real.exp v - v := by
  linarith [Real.add_one_le_exp v]

lemma add_exp_one_sub_ge_two (a : ℝ) : 2 ≤ a + Real.exp (1 - a) := by
  linarith [Real.add_one_le_exp (1 - a)]

lemma add_exp_one_sub_pos (a : ℝ) : 0 < a + Real.exp (1 - a) := by
  linarith [add_exp_one_sub_ge_two a]

lemma log_add_exp_one_sub_pos (a : ℝ) : 0 < Real.log (a + Real.exp (1 - a)) := by
  apply Real.log_pos
  linarith [add_exp_one_sub_ge_two a]

/-! ## Evaluation lemmas -/

lemma eval_mkExp (x y : ℝ) (t : EMLTerm₂) :
    EMLTerm₂.eval x y (mkExp t) = Real.exp (EMLTerm₂.eval x y t) := by
  simp [mkExp, EMLTerm₂.eval, Real.log_one]

lemma eval_mkLog (x y : ℝ) (t : EMLTerm₂) (_h : 0 < EMLTerm₂.eval x y t) :
    EMLTerm₂.eval x y (mkLog t) = Real.log (EMLTerm₂.eval x y t) := by
  unfold mkLog;
  norm_num [ EMLTerm₂.eval ]

lemma eval_mkZero (x y : ℝ) :
    EMLTerm₂.eval x y mkZero = 0 := by
  rw [ show mkZero = mkLog .one by rfl, eval_mkLog ] <;> norm_num;
  · exact Or.inr <| Or.inl rfl;
  · exact zero_lt_one

lemma eval_mkOneMinus (x y : ℝ) (t : EMLTerm₂) :
    EMLTerm₂.eval x y (mkOneMinus t) = 1 - EMLTerm₂.eval x y t := by
  unfold mkOneMinus;
  unfold mkZero;
  unfold mkLog mkExp;
  simp [EMLTerm₂.eval]

lemma eval_mkNeg (x y : ℝ) (t : EMLTerm₂) :
    EMLTerm₂.eval x y (mkNeg t) = -(EMLTerm₂.eval x y t) := by
  -- By definition of mkNeg, we have mkNeg t = .eml (mkLog (.eml t (mkExp t))) (mkExp (mkExp t)).
  unfold mkNeg;
  -- Let's simplify the expression using the definitions of `mkLog` and `mkExp`.
  have h_simp : EMLTerm₂.eval x y ((mkLog (t.eml (mkExp t))).eml (mkExp (mkExp t))) = Real.exp (Real.log (Real.exp (EMLTerm₂.eval x y t) - EMLTerm₂.eval x y t)) - Real.log (Real.exp (Real.exp (EMLTerm₂.eval x y t))) := by
    -- By definition of `eval`, we can rewrite the right-hand side of the equation.
    simp [EMLTerm₂.eval, mkLog, mkExp];
  linarith [ Real.exp_log ( exp_sub_self_pos ( EMLTerm₂.eval x y t ) ), Real.log_exp ( Real.exp ( EMLTerm₂.eval x y t ) ) ]

lemma eval_mkSub (x y : ℝ) (a b : EMLTerm₂) :
    EMLTerm₂.eval x y (mkSub a b) =
      EMLTerm₂.eval x y a - EMLTerm₂.eval x y b := by
  unfold mkSub;
  simp +decide [ EMLTerm₂.eval, mkLog, mkExp, mkNeg, mkOneMinus ];
  rw [ Real.exp_log ] <;> norm_num;
  · rw [ Real.exp_log, Real.exp_log ] <;> linarith [ exp_sub_self_pos ( EMLTerm₂.eval x y a ), exp_sub_self_pos ( EMLTerm₂.eval x y b ) ];
  · rw [ Real.exp_log ] <;> norm_num [ eval_mkZero ];
    · linarith [ Real.add_one_le_exp ( 1 - EMLTerm₂.eval x y a ) ];
    · linarith [ Real.add_one_le_exp ( EMLTerm₂.eval x y a ) ]

private lemma eval_apk (x y : ℝ) (a : EMLTerm₂) :
    EMLTerm₂.eval x y (.eml (mkOneMinus a) (mkExp (mkNeg a))) =
      EMLTerm₂.eval x y a + Real.exp (1 - EMLTerm₂.eval x y a) := by
  -- By definition of `EMLTerm₂.eval`, we can expand the left-hand side.
  have h_expand : EMLTerm₂.eval x y ((mkOneMinus a).eml (mkExp (mkNeg a))) = Real.exp (EMLTerm₂.eval x y (mkOneMinus a)) - Real.log (EMLTerm₂.eval x y (mkExp (mkNeg a))) := by
    rfl;
  rw [ h_expand, eval_mkOneMinus, eval_mkExp, eval_mkNeg ] ; ring;
  rw [ Real.log_exp ] ; ring

lemma eval_mkDiv (x y : ℝ) (a c : EMLTerm₂) (hc : 0 < EMLTerm₂.eval x y c) :
    EMLTerm₂.eval x y (mkDiv a c) =
      EMLTerm₂.eval x y a / EMLTerm₂.eval x y c := by
  unfold mkDiv;
  simp +decide [ EMLTerm₂.eval ];
  rw [ eval_mkExp, eval_mkLog, eval_mkLog, eval_mkExp, eval_mkExp, eval_mkSub, eval_mkOneMinus, eval_mkLog ];
  · rw [ eval_apk ];
    rw [ Real.exp_sub, Real.exp_log ( log_add_exp_one_sub_pos _ ), Real.exp_log ( add_exp_one_sub_pos _ ), Real.exp_log hc ];
    norm_num [ Real.exp_add, Real.exp_sub, Real.exp_neg, Real.exp_log hc ] ; ring;
  · assumption;
  · convert add_exp_one_sub_pos ( EMLTerm₂.eval x y a ) using 1;
    convert eval_apk x y a using 1;
  · convert log_add_exp_one_sub_pos ( EMLTerm₂.eval x y a ) using 1;
    convert eval_mkLog x y _ _ using 1;
    · exact congr_arg _ (Eq.symm (eval_apk x y a));
    · convert add_exp_one_sub_pos ( EMLTerm₂.eval x y a ) using 1;
      convert eval_apk x y a using 1

/-! ## Main theorem -/

theorem emlterm2_for_log :
    ∃ t : EMLTerm₂, ∀ x y : ℝ, 1 < x → 0 < y →
      EMLTerm₂.eval x y t = Real.log y / Real.log x := by
  constructor;
  case w => exact mkDiv ( mkLog .varY ) ( mkLog .varX );
  intros x y hx hy;
  rw [ eval_mkDiv, eval_mkLog, eval_mkLog ];
  · rfl;
  · exact lt_trans zero_lt_one hx;
  · exact hy;
  · rw [ eval_mkLog ] <;> norm_num [ EMLTerm₂.eval ] ; linarith [ Real.log_pos hx ];
    linarith

end EML
