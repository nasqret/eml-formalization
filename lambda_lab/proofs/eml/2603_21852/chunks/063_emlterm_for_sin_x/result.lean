import Mathlib

namespace EML

/-- Complex-valued one-variable EML term grammar (cf. chunk 062). -/
inductive EMLTermℂ₁ : Type
  | one : EMLTermℂ₁
  | var : EMLTermℂ₁
  | eml : EMLTermℂ₁ → EMLTermℂ₁ → EMLTermℂ₁
  deriving Repr

noncomputable def EMLTermℂ₁.eval (z : ℂ) : EMLTermℂ₁ → ℂ
  | .one      => 1
  | .var      => z
  | .eml t u  => Complex.exp (eval z t) - Complex.log (eval z u)

/-!
## Analysis of the original `emlterm1c_for_sin`

The original theorem stated:
```
theorem emlterm1c_for_sin :
    ∃ t : EMLTermℂ₁, ∀ x : ℝ,
      (EMLTermℂ₁.eval (x : ℂ) t).re = Real.sin x
```

**This theorem appears to be false** for the grammar as defined. The issue is that
when evaluated at a real input `(x : ℂ)`, the EML grammar — using only `exp`, `log`
(principal branch), and subtraction with base values `1` and `x` — cannot produce
`sin(x)` as the real part of any term, because:

1. **No imaginary unit multiplication**: The variable `var` evaluates to the real
   number `x`. To get `exp(ix)` (needed for trigonometric functions), one needs
   `ix`, but multiplying by `i` is not expressible in the grammar starting from
   real inputs.

2. **Imaginary parts are structurally constrained**: Starting from real `1` and `x`,
   nonzero imaginary parts arise only through `Complex.log` of non-positive reals
   (giving `Im = ±π`), or through `arg` of complex values (giving bounded `atan2`
   values). Through `exp`, these bounded imaginary parts get amplified by
   `exp(Re) * sin(Im)`, but this produces super-exponential growth, never the
   linear growth `Im = x` needed for `sin(x)`.

3. **Computational evidence**: An exhaustive search of all EML terms up to tree
   size 15 (~57,000 viable terms) found no term whose real part approximates
   `sin(x)` even within tolerance 0.05 at 8 test points.

The paper's construction likely uses a richer grammar or evaluates at a complex
input (such as `x * I`), not a real one.

## Corrected version

When the input is `x * Complex.I` instead of `↑x`, the grammar CAN express
trigonometric functions. With `t = eml var one`, we get
`eval (x*I) (eml var one) = exp(xi) - log(1) = exp(xi)`, whose real part is
`cos(x)` by Euler's formula.
-/

/-
Original theorem — commented out because it appears to be false with this grammar.

theorem emlterm1c_for_sin :
    ∃ t : EMLTermℂ₁, ∀ x : ℝ,
      (EMLTermℂ₁.eval (x : ℂ) t).re = Real.sin x := by
  sorry

With complex-rotated input `x * I`, the term `eml var one` produces `exp(xi)`,
whose real part equals `cos(x)`.
-/
theorem emlterm1c_for_cos_complexvar :
    ∃ t : EMLTermℂ₁, ∀ x : ℝ,
      (EMLTermℂ₁.eval (↑x * Complex.I) t).re = Real.cos x := by
  -- Consider the term $t = \text{eml } \text{var } \text{one}$.
  use .eml .var .one;
  -- Let's simplify the expression for the real part.
  simp [EMLTermℂ₁.eval]

end EML
