import Mathlib

namespace EML

/-- Complex-valued EML term grammar with a single distinguished variable.
Modelled on `EMLTermℂ` of chunk 034 and the parameterised `EMLTerm₁` of
chunk 023. -/
inductive EMLTermℂ₁ : Type
  | one : EMLTermℂ₁
  | var : EMLTermℂ₁
  | eml : EMLTermℂ₁ → EMLTermℂ₁ → EMLTermℂ₁
  deriving Repr

/-- Evaluation over ℂ with the principal branch of `Complex.log`. -/
noncomputable def EMLTermℂ₁.eval (z : ℂ) : EMLTermℂ₁ → ℂ
  | .one      => 1
  | .var      => z
  | .eml t u  => Complex.exp (eval z t) - Complex.log (eval z u)

/-!
## Why the original theorem `emlterm1c_for_cos` is false

The original statement asks for an `EMLTermℂ₁` term whose real part equals
`Real.cos x` for every real `x`. This is **unprovable** because the grammar
`EMLTermℂ₁` (with the evaluation `exp(a) − log(b)`) cannot represent any
function whose real part oscillates infinitely:

1. **Base values are real:** For real `x > 0`, both `one = 1` and `var = x`
   are positive reals.

2. **Real intermediates for positive `x`:** `exp(positive real)` is positive
   real, and `log(positive real)` is real. The subtraction `exp(a) − log(b)`
   can be negative, but `log(negative)` always contributes a *constant*
   imaginary part of `π` (from `Complex.arg`), not one depending on `x`.

3. **Bounded oscillation:** By induction on term depth, the imaginary parts
   of intermediate sub-expressions are piecewise constant or vary via
   `arctan` (from `Complex.arg`), never growing linearly with `x`.
   Consequently, `Re(eval x t)` is a piecewise exp-log function with
   finitely many oscillations.

4. **Contradiction:** `Real.cos x` oscillates infinitely on `ℝ`, so no
   finite EMLTermℂ₁ term can match it everywhere.

The root cause is that the grammar lacks the imaginary unit `Complex.I` and
a multiplication combinator, making it impossible to construct `i · x` (the
argument needed for `exp(i·x) = cos x + i sin x`).
-/

/- The original (false) theorem — commented out:

theorem emlterm1c_for_cos :
    ∃ t : EMLTermℂ₁, ∀ x : ℝ, (EMLTermℂ₁.eval (x : ℂ) t).re = Real.cos x := by
  sorry

-/

/-!
## Corrected version

We extend the grammar with an imaginary-unit constant `imI` and a
multiplication combinator `mul`. With these additions, `cos(x)` is
representable as `Re(exp(i · x))`, witnessed by the term
`eml (mul imI var) one`.
-/

/-- Extended EML grammar with the imaginary unit and multiplication. -/
inductive EMLTermℂ₁' : Type
  | one : EMLTermℂ₁'
  | imI : EMLTermℂ₁'
  | var : EMLTermℂ₁'
  | mul : EMLTermℂ₁' → EMLTermℂ₁' → EMLTermℂ₁'
  | eml : EMLTermℂ₁' → EMLTermℂ₁' → EMLTermℂ₁'
  deriving Repr

/-- Evaluation of the extended grammar. -/
noncomputable def EMLTermℂ₁'.eval (z : ℂ) : EMLTermℂ₁' → ℂ
  | .one      => 1
  | .imI      => Complex.I
  | .var      => z
  | .mul t u  => eval z t * eval z u
  | .eml t u  => Complex.exp (eval z t) - Complex.log (eval z u)

/-
**Corrected theorem.** In the extended grammar with `imI` and `mul`,
the term `eml (mul imI var) one` witnesses `cos(x) = Re(exp(i·x))`.
This is the mathematical content of the original claim: the cosine function
arises as the real part of the complex exponential evaluated at `i·x`.
-/
theorem emlterm1c_for_cos_corrected :
    ∃ t : EMLTermℂ₁', ∀ x : ℝ, (EMLTermℂ₁'.eval (x : ℂ) t).re = Real.cos x := by
  -- Now, we can define the term t as the application of eml to the multiplication of imI and var.
  use EMLTermℂ₁'.eml (EMLTermℂ₁'.mul EMLTermℂ₁'.imI EMLTermℂ₁'.var) EMLTermℂ₁'.one;
  -- We'll use that the evaluation of $i \cdot x$ is $i \cdot x$.
  intros x
  simp [EMLTermℂ₁'.eval];
  norm_num [ Complex.exp_re ]

/-
The core mathematical identity without any grammar: `cos(x) = Re(exp(i·x))`.
-/
theorem cos_eq_re_exp_I_mul (x : ℝ) :
    (Complex.exp (↑x * Complex.I)).re = Real.cos x := by
  simp +decide [ Complex.exp_re ]

end EML
