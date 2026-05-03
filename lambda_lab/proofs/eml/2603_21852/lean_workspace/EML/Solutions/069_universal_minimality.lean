import Mathlib

namespace EML

/-- Generic 2-primitive calculator with a constant `c` and a binary `op`. -/
inductive TwoPrimCalc : Type
  | const : TwoPrimCalc
  | apply : TwoPrimCalc → TwoPrimCalc → TwoPrimCalc
  deriving Repr

/-- Evaluation of a constant-only / binary-only calculator: it simply
re-applies the binary `op` over a single constant. The variable `x`
never enters. -/
def TwoPrimCalc.eval (c : ℝ) (op : ℝ → ℝ → ℝ) : TwoPrimCalc → ℝ
  | .const     => c
  | .apply a b => op (eval c op a) (eval c op b)

/-
Universal minimality: no 2-primitive calculator (constant + binary)
can represent the identity `x ↦ x` as a function of one variable.
-/
theorem two_prim_cannot_represent_identity
    (c : ℝ) (op : ℝ → ℝ → ℝ) :
    ¬ ∃ t : TwoPrimCalc, ∀ x : ℝ, TwoPrimCalc.eval c op t = x := by
  -- Assume for contradiction that there exists a term t such that for all x, TwoPrimCalc.eval c op t = x.
  by_contra h
  obtain ⟨t, ht⟩ := h;
  linarith [ ht 0, ht 1 ]

/-- Variant: constant + unary. Closed terms again do not depend on `x`. -/
inductive TwoPrimCalcU : Type
  | const : TwoPrimCalcU
  | apply : TwoPrimCalcU → TwoPrimCalcU
  deriving Repr

def TwoPrimCalcU.eval (c : ℝ) (f : ℝ → ℝ) : TwoPrimCalcU → ℝ
  | .const   => c
  | .apply a => f (eval c f a)

theorem two_prim_unary_cannot_represent_identity
    (c : ℝ) (f : ℝ → ℝ) :
    ¬ ∃ t : TwoPrimCalcU, ∀ x : ℝ, TwoPrimCalcU.eval c f t = x := by
  -- Suppose for contradiction that there exists a calculator $t$ such that $t.eval c f = x$ for all $x$.
  intro h
  obtain ⟨t, ht⟩ := h
  have h0 := ht 0
  have h1 := ht 1
  linarith [h0, h1]

end EML
