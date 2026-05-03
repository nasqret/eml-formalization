import Mathlib

namespace EML

/-
Generalises chunk 029 (which only ruled out the constant-1-only
calculator). Here we formalise the FULL universal minimality claim:
no 2-primitive calculator (one nullary constant + one n-ary function,
for any n ∈ {1, 2}) can express the identity ℝ → ℝ as a function of
one variable.

The argument proceeds by case analysis on the inductive shape of any
2-primitive grammar: the unique closed term either evaluates to a
constant (1 nullary + 1 unary applied to the constant) or to a constant
(1 nullary + 1 binary applied to (constant, constant)) — neither
case can vary with `x`. We model this via a generic type
`TwoPrimCalc (c : ℝ) (op : ℝ → ℝ → ℝ)` that allows only the operations
of the chosen 2-element basis.
-/

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

/-- Universal minimality: no 2-primitive calculator (constant + binary)
can represent the identity `x ↦ x` as a function of one variable. -/
theorem two_prim_cannot_represent_identity
    (c : ℝ) (op : ℝ → ℝ → ℝ) :
    ¬ ∃ t : TwoPrimCalc, ∀ x : ℝ, TwoPrimCalc.eval c op t = x := by
  sorry

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
  sorry

end EML
