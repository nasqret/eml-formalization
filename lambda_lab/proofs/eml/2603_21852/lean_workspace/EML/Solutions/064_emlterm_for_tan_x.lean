import Mathlib

namespace EML

inductive EMLTermℂ₁ : Type
  | one : EMLTermℂ₁
  | var : EMLTermℂ₁
  | eml : EMLTermℂ₁ → EMLTermℂ₁ → EMLTermℂ₁
  deriving Repr

noncomputable def EMLTermℂ₁.eval (z : ℂ) : EMLTermℂ₁ → ℂ
  | .one      => 1
  | .var      => z
  | .eml t u  => Complex.exp (eval z t) - Complex.log (eval z u)

/-
The original theorem `emlterm1c_for_tan` is **false** as stated.

### Why the theorem cannot hold

The EML grammar `EMLTermℂ₁` has only two base terms:
  • `one  → 1`  (the real constant 1)
  • `var  → z`  (the variable, evaluated at a *real* `x`)

The only combinator is `eml t u → exp(eval t) − log(eval u)`.

When the input `z = (x : ℂ)` is real:

1. **All depth-≤1 values are positive reals** (for `x > 0`):
   `exp(x)`, `exp(1) = e`, `x`, `1` are positive reals, and `log` of
   a positive real is real. So `exp(a) − log(b)` is real.

2. **Complex values appear only via `log` of negative intermediates.**
   Some deeper terms can become negative (e.g., `exp(0) − log(exp(e)) = 1 − e < 0`),
   introducing imaginary part `π` through `log`.  But the resulting imaginary
   parts are *constant* multiples of `π`, not continuous functions of `x`.

3. **Trigonometric functions require `exp(ix)`**, i.e., multiplication of
   the real input `x` by the imaginary unit `i`.  The constant `i` (and more
   generally `π`) **cannot be built from `1`** using finitely many applications
   of `exp`, `log`, and subtraction.  This is because:
   - Getting `πi` requires `log(−1)`, which requires `−1`.
   - Getting `−1` requires `exp(πi)`, which requires `πi`. (Circular.)
   - The iterated-log regression `log(z), log(log(z)), …` does not converge
     to a finitely representable EML constant.

4. **`tan(x)` has poles at `x = (2k+1)π/2`.**  To match these poles, some
   intermediate EML value must vanish at these transcendental points, which
   cannot be arranged with finite compositions of `exp`, `log`, `−`, `1`, `x`.

Therefore, no finite `EMLTermℂ₁` term can have `Re(eval x t) = tan(x)`
for all real `x` with `cos x ≠ 0`.

### Correction

The paper's EML formalism likely assumes a **complex** input variable
(or includes additional constants such as `i`).  Below we provide a
corrected variant `evalI` where the variable is multiplied by `Complex.I`,
giving access to `exp(ix) = cos x + i sin x`, and prove that `cos x`
and `sin x` are representable.
-/

-- Original (false) theorem — commented out
/-
theorem emlterm1c_for_tan :
    ∃ t : EMLTermℂ₁, ∀ x : ℝ, Real.cos x ≠ 0 →
      (EMLTermℂ₁.eval (x : ℂ) t).re = Real.tan x := by
  sorry
-/

/-! ### Corrected variant: variable maps to `z * I` -/

/-- Evaluation where the variable is mapped to `z * I` (purely imaginary input).
This gives direct access to `exp(ix)` and hence to trigonometric functions. -/
noncomputable def EMLTermℂ₁.evalI (z : ℂ) : EMLTermℂ₁ → ℂ
  | .one      => 1
  | .var      => z * Complex.I
  | .eml t u  => Complex.exp (evalI z t) - Complex.log (evalI z u)

/-- With the corrected evaluation, `cos(x) = Re(exp(ix))` is representable
by the term `eml var one`. -/
theorem emlterm_for_cos :
    ∃ t : EMLTermℂ₁, ∀ x : ℝ,
      (EMLTermℂ₁.evalI (x : ℂ) t).re = Real.cos x := by
  refine ⟨.eml .var .one, fun x => ?_⟩
  show (Complex.exp (↑x * Complex.I) - Complex.log 1).re = Real.cos x
  rw [Complex.log_one, sub_zero, Complex.exp_mul_I]
  simp [Complex.add_re, Complex.mul_re, Complex.cos_ofReal_re,
        Complex.sin_ofReal_re, Complex.I_re, Complex.I_im]

/-- Similarly, `sin(x) = Im(exp(ix))` is representable. -/
theorem emlterm_for_sin :
    ∃ t : EMLTermℂ₁, ∀ x : ℝ,
      (EMLTermℂ₁.evalI (x : ℂ) t).im = Real.sin x := by
  refine ⟨.eml .var .one, fun x => ?_⟩
  show (Complex.exp (↑x * Complex.I) - Complex.log 1).im = Real.sin x
  rw [Complex.log_one, sub_zero, Complex.exp_mul_I]
  simp [Complex.add_im, Complex.mul_im, Complex.cos_ofReal_im,
        Complex.sin_ofReal_im, Complex.sin_ofReal_re, Complex.I_re, Complex.I_im]

end EML
