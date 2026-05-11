import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace EML

/-- Calc2: the "subtraction-based" calculator language.
    Operations: varX, varY, sub, exp_, ln_. -/
inductive Calc2 where
  | varX : Calc2
  | varY : Calc2
  | sub  : Calc2 → Calc2 → Calc2
  | exp_ : Calc2 → Calc2
  | ln_  : Calc2 → Calc2
  deriving Repr

/-- Evaluation of a Calc2 term at real numbers x, y. -/
noncomputable def Calc2.eval (x y : ℝ) : Calc2 → ℝ
  | .varX     => x
  | .varY     => y
  | .sub a b  => a.eval x y - b.eval x y
  | .exp_ a   => Real.exp (a.eval x y)
  | .ln_ a    => Real.log (a.eval x y)

/-- The "zero" constant in Calc2, encoded as `varX − varX`. -/
def Calc2.zero : Calc2 := .sub .varX .varX

theorem Calc2.eval_zero (x y : ℝ) : Calc2.eval x y Calc2.zero = 0 := by
  simp [Calc2.zero, Calc2.eval]

/-- Calc3: the "addition/negation-based" calculator language.
    Operations: varX, varY, add, neg, exp_, ln_. -/
inductive Calc3 where
  | varX : Calc3
  | varY : Calc3
  | add  : Calc3 → Calc3 → Calc3
  | neg  : Calc3 → Calc3
  | exp_ : Calc3 → Calc3
  | ln_  : Calc3 → Calc3
  deriving Repr

/-- Evaluation of a Calc3 term at real numbers x, y. -/
noncomputable def Calc3.eval (x y : ℝ) : Calc3 → ℝ
  | .varX     => x
  | .varY     => y
  | .add a b  => a.eval x y + b.eval x y
  | .neg a    => -(a.eval x y)
  | .exp_ a   => Real.exp (a.eval x y)
  | .ln_ a    => Real.log (a.eval x y)

/-- Translation from Calc3 to Calc2. -/
def Calc3.toCalc2 : Calc3 → Calc2
  | .varX     => .varX
  | .varY     => .varY
  | .add a b  => .sub a.toCalc2 (.sub .zero b.toCalc2)
  | .neg a    => .sub .zero a.toCalc2
  | .exp_ a   => .exp_ a.toCalc2
  | .ln_ a    => .ln_ a.toCalc2

/-- **Calc 3 → Calc 2** (Table 2, row 2 → row 3).

For every `Calc3` term `e` there exists a `Calc2` term `e'` whose
real-valued evaluation agrees with `e`'s.

**Translation strategy** (informal):
* `add a b ↦ a − (−b) = a − (0 − b)` — addition becomes subtraction.
* `neg a  ↦ 0 − a` — unary negation becomes subtraction.
* `exp_`, `ln_` translate as themselves.
* The constant `0` available everywhere via `varX − varX`.
-/
theorem calc3_to_calc2 :
    ∀ e : Calc3, ∃ e' : Calc2,
      ∀ x y : ℝ, Calc2.eval x y e' = Calc3.eval x y e := by
  intro e
  exact ⟨e.toCalc2, fun x y => by
    induction e with
    | varX => simp [Calc3.toCalc2, Calc2.eval, Calc3.eval]
    | varY => simp [Calc3.toCalc2, Calc2.eval, Calc3.eval]
    | add a b iha ihb =>
      simp only [Calc3.toCalc2, Calc2.eval, Calc3.eval, Calc2.eval_zero, iha, ihb]
      ring
    | neg a iha =>
      simp only [Calc3.toCalc2, Calc2.eval, Calc3.eval, Calc2.eval_zero, iha]
      ring
    | exp_ a iha => simp [Calc3.toCalc2, Calc2.eval, Calc3.eval, iha]
    | ln_ a iha => simp [Calc3.toCalc2, Calc2.eval, Calc3.eval, iha]⟩

end EML
