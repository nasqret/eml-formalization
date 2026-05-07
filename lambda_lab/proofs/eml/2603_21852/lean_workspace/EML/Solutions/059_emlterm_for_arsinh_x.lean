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

-- ═══════════════════════════════════════════════════════════════
-- Building-block term constructors
-- ═══════════════════════════════════════════════════════════════

/-- `mkExp t` evaluates to `exp(eval t)`. -/
def mkExp (t : EMLTerm₁) : EMLTerm₁ := .eml t .one

/-- `mkLog f` evaluates to `Real.log(eval f)` for ANY `f`. -/
def mkLog (f : EMLTerm₁) : EMLTerm₁ := .eml f (.eml (.eml f f) .one)

/-- `mkNeg f` evaluates to `-(eval f)` for ANY `f`. -/
def mkNeg (f : EMLTerm₁) : EMLTerm₁ :=
  .eml (mkLog (.eml f (.eml f .one))) (.eml (.eml f .one) .one)

/-- `mkAddPos f g` evaluates to `eval f + eval g` when `eval f > 0`. -/
def mkAddPos (f g : EMLTerm₁) : EMLTerm₁ := .eml (mkLog f) (.eml (mkNeg g) .one)

/-- `mkSubPos f g` evaluates to `eval f - eval g` when `eval f > 0`. -/
def mkSubPos (f g : EMLTerm₁) : EMLTerm₁ := .eml (mkLog f) (.eml g .one)

-- ═══════════════════════════════════════════════════════════════
-- Evaluation lemmas for building blocks
-- ═══════════════════════════════════════════════════════════════

@[simp] lemma mkExp_eval (x : ℝ) (t : EMLTerm₁) :
    EMLTerm₁.eval x (mkExp t) = Real.exp (EMLTerm₁.eval x t) := by
  simp [mkExp, EMLTerm₁.eval, Real.log_one]

@[simp] lemma mkLog_eval (x : ℝ) (f : EMLTerm₁) :
    EMLTerm₁.eval x (mkLog f) = Real.log (EMLTerm₁.eval x f) := by
  unfold mkLog; simp +decide [ EMLTerm₁.eval ] ;

lemma exp_sub_id_pos (v : ℝ) : 0 < Real.exp v - v := by
  linarith [Real.add_one_le_exp v]

@[simp] lemma mkNeg_eval (x : ℝ) (f : EMLTerm₁) :
    EMLTerm₁.eval x (mkNeg f) = -(EMLTerm₁.eval x f) := by
  unfold mkNeg; simp +decide [ EMLTerm₁.eval ] ;
  rw [ Real.exp_log ] <;> linarith [ Real.add_one_le_exp ( EMLTerm₁.eval x f ) ]

@[simp] lemma mkAddPos_eval (x : ℝ) (f g : EMLTerm₁) (hf : 0 < EMLTerm₁.eval x f) :
    EMLTerm₁.eval x (mkAddPos f g) = EMLTerm₁.eval x f + EMLTerm₁.eval x g := by
  unfold mkAddPos;
  simp +decide [ EMLTerm₁.eval, Real.exp_log hf ]

@[simp] lemma mkSubPos_eval (x : ℝ) (f g : EMLTerm₁) (hf : 0 < EMLTerm₁.eval x f) :
    EMLTerm₁.eval x (mkSubPos f g) = EMLTerm₁.eval x f - EMLTerm₁.eval x g := by
  unfold mkSubPos;
  simp_all +decide [ EMLTerm₁.eval ];
  rw [ Real.exp_log hf ]

-- ═══════════════════════════════════════════════════════════════
-- Arsinh construction: arsinh(x) = log(x + √(x²+1))
-- ═══════════════════════════════════════════════════════════════

-- 2·cosh(x) = exp(x) + exp(-x)
def twoCosh : EMLTerm₁ := mkAddPos (mkExp .var) (mkExp (mkNeg .var))

-- M₁ = 2·cosh(x) - log(x) + 1  (shift for computing 2·log(x))
def shiftM1 : EMLTerm₁ := mkAddPos (mkSubPos twoCosh (mkLog .var)) .one

-- 2·log(x) via shifted addition: (M₁ + log(x)) - (M₁ - log(x))
def twoLogX : EMLTerm₁ :=
  .eml (mkLog (mkAddPos shiftM1 (mkLog .var)))
       (mkExp (mkSubPos shiftM1 (mkLog .var)))

-- x² = exp(2·log(x))
def xSq : EMLTerm₁ := mkExp twoLogX

-- x² + 1
def xSqP1 : EMLTerm₁ := mkAddPos xSq .one

-- 2 = 1 + 1
def two : EMLTerm₁ := mkAddPos .one .one

-- log(x²+1)/2 = exp(log(log(x²+1)) - log(2))
-- Key trick: a - b = -(b - a), and b - a uses SUB with b > 0
-- log(2) > 0, so SUB_POS(log(2), log(log(x²+1))) works
def halfLogXSqP1 : EMLTerm₁ :=
  mkExp (mkNeg (mkSubPos (mkLog two) (mkLog (mkLog xSqP1))))

-- √(x²+1) = exp(log(x²+1)/2)
def sqrtXSqP1 : EMLTerm₁ := mkExp halfLogXSqP1

-- x + √(x²+1)
def xPlusSqrt : EMLTerm₁ := mkAddPos .var sqrtXSqP1

-- arsinh(x) = log(x + √(x²+1))
def arsinhTerm : EMLTerm₁ := mkLog xPlusSqrt

/-
═══════════════════════════════════════════════════════════════
Positivity lemmas and evaluation chain
═══════════════════════════════════════════════════════════════
-/
lemma twoCosh_eval (x : ℝ) (_hx : 0 < x) :
    EMLTerm₁.eval x twoCosh = Real.exp x + Real.exp (-x) := by
  have h_twoCosh : EMLTerm₁.eval x twoCosh = EMLTerm₁.eval x (mkAddPos (mkExp .var) (mkExp (mkNeg .var))) := by
    rfl;
  rw [ h_twoCosh, mkAddPos_eval ] <;> norm_num [ _hx ];
  · rfl;
  · positivity

lemma twoCosh_pos (x : ℝ) : 0 < Real.exp x + Real.exp (-x) := by
  linarith [Real.exp_pos x, Real.exp_pos (-x)]

lemma twoCosh_sub_log_pos (x : ℝ) (hx : 0 < x) :
    0 < (Real.exp x + Real.exp (-x)) - Real.log x := by
  linarith [ Real.add_one_le_exp x, Real.exp_pos ( -x ), Real.log_le_sub_one_of_pos hx ]

lemma shiftM1_eval (x : ℝ) (hx : 0 < x) :
    EMLTerm₁.eval x shiftM1 = (Real.exp x + Real.exp (-x) - Real.log x) + 1 := by
  convert mkAddPos_eval x ( mkSubPos twoCosh ( mkLog .var ) ) .one _ using 1;
  · rw [ mkSubPos_eval, twoCosh_eval ] <;> norm_num [ hx ];
    · rfl;
    · exact twoCosh_eval x hx ▸ twoCosh_pos x;
  · convert twoCosh_sub_log_pos x hx using 1;
    convert mkSubPos_eval x twoCosh ( mkLog .var ) _ using 1;
    · rw [ twoCosh_eval x hx, mkLog_eval ];
      rfl;
    · exact twoCosh_eval x hx ▸ twoCosh_pos x

lemma shiftM1_pos (x : ℝ) (hx : 0 < x) : 0 < EMLTerm₁.eval x shiftM1 := by
  rw [shiftM1_eval x hx]; linarith [twoCosh_sub_log_pos x hx]

lemma shiftM1_plus_log_pos (x : ℝ) (hx : 0 < x) :
    0 < EMLTerm₁.eval x shiftM1 + Real.log x := by
  rw [shiftM1_eval x hx]
  have := twoCosh_pos x
  linarith

lemma shiftM1_plus_log_eq (x : ℝ) (hx : 0 < x) :
    EMLTerm₁.eval x shiftM1 + Real.log x = Real.exp x + Real.exp (-x) + 1 := by
  rw [shiftM1_eval x hx]; ring

lemma twoLogX_eval (x : ℝ) (hx : 0 < x) :
    EMLTerm₁.eval x twoLogX = 2 * Real.log x := by
  unfold twoLogX;
  simp +decide [ EMLTerm₁.eval, mkLog, mkExp, mkSubPos, mkAddPos ];
  rw [ Real.exp_log ];
  · ring;
  · rw [ Real.exp_log ];
    · exact shiftM1_plus_log_pos x hx;
    · exact shiftM1_pos x hx

lemma xSq_eval (x : ℝ) (hx : 0 < x) :
    EMLTerm₁.eval x xSq = x ^ 2 := by
  -- By definition of exponentiation, we know that $e^{2 \log x} = x^2$ for $x > 0$.
  have h_exp_log : Real.exp (2 * Real.log x) = x^2 := by
    rw [ mul_comm, Real.exp_mul, Real.exp_log ] <;> norm_cast;
  rw [ ← h_exp_log, show xSq = mkExp twoLogX from rfl, mkExp_eval, twoLogX_eval x hx ]

lemma xSq_pos (x : ℝ) (hx : 0 < x) : 0 < EMLTerm₁.eval x xSq := by
  rw [xSq_eval x hx]; positivity

lemma xSqP1_eval (x : ℝ) (hx : 0 < x) :
    EMLTerm₁.eval x xSqP1 = x ^ 2 + 1 := by
  -- By definition of `mkAddPos`, we have `mkAddPos f g = .eml (mkLog f) (.eml (mkNeg g) .one)`.
  have h_mkAddPos : EMLTerm₁.eval x (mkAddPos xSq .one) = EMLTerm₁.eval x xSq + EMLTerm₁.eval x .one := by
    exact mkAddPos_eval x _ _ ( xSq_pos x hx );
  exact h_mkAddPos.trans ( by erw [ xSq_eval x hx ] ; erw [ show EMLTerm₁.eval x EMLTerm₁.one = 1 from rfl ] )

lemma xSqP1_pos (x : ℝ) (hx : 0 < x) : 0 < EMLTerm₁.eval x xSqP1 := by
  rw [xSqP1_eval x hx]; positivity

lemma two_eval (x : ℝ) : EMLTerm₁.eval x two = 2 := by
  convert mkAddPos_eval x .one .one _ using 1;
  · exact show ( 2 : ℝ ) = 1 + 1 by norm_num;
  · exact zero_lt_one

lemma logTwo_pos : 0 < Real.log 2 := by
  rw [Real.log_pos_iff (by norm_num : (0:ℝ) ≤ 2)]; norm_num

lemma log_xSqP1_pos (x : ℝ) (hx : 0 < x) : 0 < Real.log (x ^ 2 + 1) := by
  rw [Real.log_pos_iff (by positivity)]; nlinarith

lemma halfLogXSqP1_eval (x : ℝ) (hx : 0 < x) :
    EMLTerm₁.eval x halfLogXSqP1 = Real.log (x ^ 2 + 1) / 2 := by
  unfold halfLogXSqP1; simp +decide [*] ; (
  rw [ mkSubPos_eval ] <;> norm_num [ two_eval, xSqP1_eval ];
  · rw [ Real.exp_sub, Real.exp_log, Real.exp_log ] <;> norm_num [ xSqP1_eval, hx ];
    exact Real.log_pos <| by nlinarith;
  · positivity);

lemma sqrtXSqP1_eval (x : ℝ) (hx : 0 < x) :
    EMLTerm₁.eval x sqrtXSqP1 = Real.sqrt (x ^ 2 + 1) := by
  convert congr_arg Real.exp ( halfLogXSqP1_eval x hx ) using 1;
  · exact sub_eq_of_eq_add <| by norm_num [ EMLTerm₁.eval ] ;
  · rw [ Real.sqrt_eq_rpow, Real.rpow_def_of_pos ( by positivity ) ] ; ring

lemma sqrtXSqP1_pos (x : ℝ) (hx : 0 < x) : 0 < Real.sqrt (x ^ 2 + 1) := by
  exact Real.sqrt_pos_of_pos (by positivity)

lemma xPlusSqrt_eval (x : ℝ) (hx : 0 < x) :
    EMLTerm₁.eval x xPlusSqrt = x + Real.sqrt (x ^ 2 + 1) := by
  rw [ ← sqrtXSqP1_eval x hx ];
  apply mkAddPos_eval;
  exact hx

-- ═══════════════════════════════════════════════════════════════
-- Main theorem
-- ═══════════════════════════════════════════════════════════════

theorem emlterm1_for_arsinh :
    ∃ t : EMLTerm₁, ∀ x : ℝ, 0 < x → EMLTerm₁.eval x t = Real.arsinh x := by
  exact ⟨arsinhTerm, fun x hx => by
    unfold arsinhTerm
    rw [mkLog_eval, xPlusSqrt_eval x hx]
    simp [Real.arsinh, add_comm (1 : ℝ) (x ^ 2)]⟩

end EML
