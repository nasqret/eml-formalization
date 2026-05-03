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

/-
Recipe (Table S2, step 24 — `cos(x)`, K=5):
    cos(x) = cosh(i · x)          (paper macro, complex chain)

Equivalent to Mathlib's `Real.cos x = Re(cosh(i·x))`. Since the
witness inhabits `EMLTermℂ₁`, we evaluate at the complex lift of `x`
and recover the real cosine on the diagonal `z = (x : ℂ)`.

The paper's `cosh(i·x)` macro requires the `i` constant (chunk 035) and
the `cosh` macro lifted to ℂ; both fit in the `EMLTermℂ₁` grammar above.
-/
theorem emlterm1c_for_cos :
    ∃ t : EMLTermℂ₁, ∀ x : ℝ, (EMLTermℂ₁.eval (x : ℂ) t).re = Real.cos x := by
  sorry

end EML
