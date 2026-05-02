import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib

namespace EML

/-- Calc1 expressions: variables, literals, multiplication, `rpow`, and `logb`. -/
inductive Calc1
  | var_x : Calc1
  | var_y : Calc1
  | lit   : ℝ → Calc1
  | mul   : Calc1 → Calc1 → Calc1
  | pow   : Calc1 → Calc1 → Calc1
  | logb  : Calc1 → Calc1 → Calc1

/-- Calc2 expressions: variables, literals, multiplication, `exp`, `ln`, and subtraction. -/
inductive Calc2
  | var_x : Calc2
  | var_y : Calc2
  | lit   : ℝ → Calc2
  | mul   : Calc2 → Calc2 → Calc2
  | exp_  : Calc2 → Calc2
  | ln_   : Calc2 → Calc2
  | sub   : Calc2 → Calc2 → Calc2

noncomputable def Calc1.eval (x y : ℝ) : Calc1 → ℝ
  | .var_x      => x
  | .var_y      => y
  | .lit r      => r
  | .mul e₁ e₂  => e₁.eval x y * e₂.eval x y
  | .pow e₁ e₂  => (e₁.eval x y) ^ (e₂.eval x y)   -- Real.rpow
  | .logb e₁ e₂ => Real.logb (e₁.eval x y) (e₂.eval x y)

noncomputable def Calc2.eval (x y : ℝ) : Calc2 → ℝ
  | .var_x      => x
  | .var_y      => y
  | .lit r      => r
  | .mul e₁ e₂  => e₁.eval x y * e₂.eval x y
  | .exp_ e     => Real.exp (e.eval x y)
  | .ln_ e      => Real.log (e.eval x y)
  | .sub e₁ e₂  => e₁.eval x y - e₂.eval x y

/-- Euler's number as a Calc1 literal. -/
noncomputable def eConst : Calc1 := .lit (Real.exp 1)

/-- Translation from Calc2 to Calc1. -/
noncomputable def translate : Calc2 → Calc1
  | .var_x    => .var_x
  | .var_y    => .var_y
  | .lit r    => .lit r
  | .mul a b  => .mul (translate a) (translate b)
  | .exp_ a   => .pow eConst (translate a)
  | .ln_ a    => .logb eConst (translate a)
  | .sub a b  =>
      .logb eConst (.mul (.pow eConst (translate a))
                         (.pow (.pow eConst (translate b)) (.lit (-1))))

private lemma translate_correct (e : Calc2) (x y : ℝ) :
    Calc1.eval x y (translate e) = Calc2.eval x y e := by
  induction' e with e₁ e₂ ih₁ ih₂;
  all_goals simp_all +decide [ Calc1.eval, Calc2.eval, translate ];
  · unfold eConst;
    simp +decide [ Real.rpow_def_of_pos ( Real.exp_pos _ ), Calc1.eval ];
  · unfold eConst; norm_num [ Real.logb ] ;
    unfold Calc1.eval; norm_num;
  · unfold eConst; norm_num [ Real.logb, Real.log_rpow ] ; ring;
    unfold Calc1.eval; norm_num [ Real.rpow_neg_one, Real.log_mul, Real.exp_ne_zero ] ; ring;

/-- **Calc 2 → Calc 1** (Table 2, row 3 → row 4).

For every `Calc2` term `e` there exists a `Calc1` term `e'` whose
real-valued evaluation agrees with `e`'s. -/
theorem calc2_to_calc1 :
    ∀ e : Calc2, ∃ e' : Calc1,
      ∀ x y : ℝ, Calc1.eval x y e' = Calc2.eval x y e := by
  intro e
  exact ⟨translate e, translate_correct e⟩

end EML
