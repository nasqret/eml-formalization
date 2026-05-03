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

/-! ### Key EML algebraic identity

For the EML operation `eml(a,b) = exp(eval a) − log(eval b)`:
  • If eval(a) = log(A) and eval(b) = exp(B), then eml(a,b) = A − B.
  • If eval(b) = 1, then eml(a,b) = exp(eval a).

We build:
  1. A constant-zero term Z such that eval(Z) = 0.
  2. A "log extractor" mkLog(f) such that eval(mkLog(f)) = log(eval(f)) when eval(f) > 0.
  3. Using these, we construct −y, x+y, and finally x/y.
-/

/-! ### Step 1: Zero constant -/

/-- Evaluates to 0 for all x, y. -/
noncomputable def zTerm : EMLTerm₂ :=
  .eml .one (.eml (.eml .one .one) .one)

lemma eval_zTerm (x y : ℝ) : zTerm.eval x y = 0 := by
  simp [zTerm, EMLTerm₂.eval, Real.log_one, Real.log_exp]

/-! ### Step 2: Log extractor -/

/-- `mkLogTerm f` evaluates to `log(f.eval x y)` when `f.eval x y > 0`. -/
noncomputable def mkLogTerm (f : EMLTerm₂) : EMLTerm₂ :=
  .eml zTerm (.eml (.eml zTerm f) .one)

lemma eval_mkLogTerm (x y : ℝ) (f : EMLTerm₂) (hf : 0 < f.eval x y) :
    (mkLogTerm f).eval x y = Real.log (f.eval x y) := by
  unfold mkLogTerm;
  simp_all +decide [ EMLTerm₂.eval ]

/-! ### Positivity lemmas -/

lemma exp_sub_id_pos (t : ℝ) : 0 < Real.exp t - t := by
  linarith [Real.add_one_le_exp t]

/-! ### Step 3: Negation of y -/

/-- Evaluates to −y. -/
noncomputable def negY_term : EMLTerm₂ :=
  .eml (mkLogTerm (.eml .varY (.eml .varY .one))) (.eml (.eml .varY .one) .one)

lemma eval_negY_term (x y : ℝ) :
    negY_term.eval x y = -y := by
  simp +decide [ negY_term, EMLTerm₂.eval ];
  rw [ eval_mkLogTerm ] <;> norm_num [ EMLTerm₂.eval ];
  · rw [ Real.exp_log ] <;> linarith [ Real.add_one_le_exp y ];
  · linarith [ Real.add_one_le_exp y ]

/-! ### Step 4: x + y -/

/-- Evaluates to x + y for x > 0. -/
noncomputable def xpyTerm : EMLTerm₂ :=
  .eml (mkLogTerm .varX) (.eml negY_term .one)

lemma eval_xpyTerm (x y : ℝ) (hx : 0 < x) :
    xpyTerm.eval x y = x + y := by
  -- By definition of `mkLogTerm`, we have `mkLogTerm .varX = eml zTerm (eml (eml zTerm .varX) .one)`.
  have h_mkLogTerm : (mkLogTerm .varX).eval x y = Real.log x := by
    convert eval_mkLogTerm x y _ _ ; tauto;
  -- By definition of `negY_term`, we have `negY_term = eml (mkLogTerm (eml .varY (eml .varY .one))) (eml (eml .varY .one) .one)`.
  have h_negY_term : (negY_term.eml EMLTerm₂.one).eval x y = Real.exp (-y) := by
    exact show Real.exp ( negY_term.eval x y ) - Real.log ( EMLTerm₂.eval x y EMLTerm₂.one ) = Real.exp ( -y ) from by rw [ eval_negY_term ] ; norm_num [ EMLTerm₂.eval ] ;
  exact Eq.symm ( by erw [ show EMLTerm₂.eval x y ( ( mkLogTerm EMLTerm₂.varX ).eml ( negY_term.eml EMLTerm₂.one ) ) = Real.exp ( EMLTerm₂.eval x y ( mkLogTerm EMLTerm₂.varX ) ) - Real.log ( EMLTerm₂.eval x y ( negY_term.eml EMLTerm₂.one ) ) by rfl ] ; rw [ h_mkLogTerm, h_negY_term ] ; simp +decide [ Real.exp_neg, Real.exp_log hx ] )

/-! ### Step 5: log(x) − log(y) -/

/-- Evaluates to log(x) − log(y) for x, y > 0. -/
noncomputable def logDiffTerm : EMLTerm₂ :=
  .eml (mkLogTerm (.eml (mkLogTerm xpyTerm) (.eml (mkLogTerm .varY) .one)))
       (.eml (.eml (mkLogTerm xpyTerm) (.eml (mkLogTerm .varX) .one)) .one)

lemma eval_logDiffTerm (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    logDiffTerm.eval x y = Real.log x - Real.log y := by
  -- Evaluate the inner terms using the provided lemmas.
  have h_inner1 : (mkLogTerm xpyTerm).eval x y = Real.log (x + y) := by
    convert eval_mkLogTerm x y xpyTerm _ using 1;
    · rw [ eval_xpyTerm x y hx ];
    · exact eval_xpyTerm x y hx ▸ add_pos hx hy
  have h_inner2 : (mkLogTerm .varY).eval x y = Real.log y := by
    exact eval_mkLogTerm x y _ hy
  have h_inner3 : (mkLogTerm .varX).eval x y = Real.log x := by
    convert eval_mkLogTerm x y ( EMLTerm₂.varX ) hx using 1;
  -- Use the properties of logarithms and exponentials to simplify the expression.
  have h_exp_log : Real.exp (Real.log (x + y)) - Real.log y > 0 ∧ Real.exp (Real.log (x + y)) - Real.log x > 0 := by
    exact ⟨ by linarith [ Real.log_le_sub_one_of_pos hy, Real.exp_log ( add_pos hx hy ) ], by linarith [ Real.log_le_sub_one_of_pos hx, Real.exp_log ( add_pos hx hy ) ] ⟩;
  unfold logDiffTerm; simp_all +decide [ EMLTerm₂.eval ] ;
  unfold mkLogTerm at *; simp_all +decide [ EMLTerm₂.eval ] ;
  rw [ Real.exp_log ] <;> linarith

/-! ### Step 6: x / y -/

/-- Evaluates to x / y for x, y > 0. -/
noncomputable def divTerm : EMLTerm₂ :=
  .eml logDiffTerm .one

lemma eval_divTerm (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    divTerm.eval x y = x / y := by
  simp only [divTerm, EMLTerm₂.eval, Real.log_one, sub_zero]
  rw [eval_logDiffTerm x y hx hy, Real.exp_sub, Real.exp_log hx, Real.exp_log hy]

/-! ### Main theorem -/

theorem emlterm2_for_div :
    ∃ t : EMLTerm₂, ∀ x y : ℝ, 0 < x → 0 < y →
      EMLTerm₂.eval x y t = x / y :=
  ⟨divTerm, eval_divTerm⟩

end EML
