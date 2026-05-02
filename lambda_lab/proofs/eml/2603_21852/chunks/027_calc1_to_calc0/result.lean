import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib

namespace EML

/-- Calc0: expressions built from variables, exp, and logb. -/
inductive Calc0 where
  | varX : Calc0
  | varY : Calc0
  | exp_ : Calc0 → Calc0
  | logb : Calc0 → Calc0 → Calc0
  deriving Repr

/-- Calc1: expressions built from variables, Euler's constant, logb, and pow. -/
inductive Calc1 where
  | varX : Calc1
  | varY : Calc1
  | eConst : Calc1
  | logb : Calc1 → Calc1 → Calc1
  | pow : Calc1 → Calc1 → Calc1
  deriving Repr

/-- Evaluation of a `Calc0` term at `(x, y)`. -/
noncomputable def Calc0.eval (x y : ℝ) : Calc0 → ℝ
  | .varX => x
  | .varY => y
  | .exp_ e => Real.exp (Calc0.eval x y e)
  | .logb a b => Real.log (Calc0.eval x y b) / Real.log (Calc0.eval x y a)

/-- Evaluation of a `Calc1` term at `(x, y)`. -/
noncomputable def Calc1.eval (x y : ℝ) : Calc1 → ℝ
  | .varX => x
  | .varY => y
  | .eConst => Real.exp 1
  | .logb a b => Real.log (Calc1.eval x y b) / Real.log (Calc1.eval x y a)
  | .pow a b => Real.exp (Calc1.eval x y b * Real.log (Calc1.eval x y a))

/-- A Calc0 term that evaluates to `1` for all `x, y`.
    Uses `logb (exp (exp x)) (exp (exp x))` = `exp x / exp x = 1`. -/
noncomputable def Calc0.one : Calc0 :=
  .logb (.exp_ (.exp_ .varX)) (.exp_ (.exp_ .varX))

/-- Translation from Calc1 to Calc0. -/
noncomputable def translate : Calc1 → Calc0
  | .varX => .varX
  | .varY => .varY
  | .eConst => .exp_ Calc0.one
  | .logb a b => .logb (translate a) (translate b)
  | .pow a b =>
    let tb := translate b
    let ta := translate a
    let inv_b := Calc0.logb (.exp_ tb) (.exp_ Calc0.one)
    .exp_ (.logb (.exp_ inv_b) ta)

lemma Calc0.one_eval (x y : ℝ) : Calc0.eval x y Calc0.one = 1 := by
  unfold one
  simp [EML.Calc0.eval]

private lemma div_inv_eq_mul (a b : ℝ) : a / (1 / b) = b * a := by
  group

lemma translate_correct (e : Calc1) (x y : ℝ) :
    Calc0.eval x y (translate e) = Calc1.eval x y e := by
  induction e with
  | varX => simp [translate, Calc0.eval, Calc1.eval]
  | varY => simp [translate, Calc0.eval, Calc1.eval]
  | eConst => simp [translate, Calc0.eval, Calc1.eval, Calc0.one_eval]
  | logb a b iha ihb => simp [translate, Calc0.eval, Calc1.eval, iha, ihb]
  | pow a b iha ihb =>
    simp only [translate, Calc0.eval, Calc1.eval]
    rw [Calc0.one_eval, Real.log_exp, Real.log_exp, iha, ihb, div_inv_eq_mul,
        Real.log_exp]

/-- **Calc 1 → Calc 0** (Table 2, row 4 → row 5). -/
theorem calc1_to_calc0 :
    ∀ e : Calc1, ∃ e' : Calc0,
      ∀ x y : ℝ, Calc0.eval x y e' = Calc1.eval x y e := by
  intro e
  exact ⟨translate e, translate_correct e⟩

end EML
