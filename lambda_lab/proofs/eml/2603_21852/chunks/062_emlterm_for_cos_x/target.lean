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
Recipe (Table S2 step 24): cos(x) = Re(exp(I·x)).

Spec tightening: original `∀ x : ℝ` reduced to `0 < x` so that
`Complex.log (x : ℂ) = (Real.log x : ℂ)` (real-valued log on positive reals).

Construction (sealed): build closed `iTerm` (eval = Complex.I) reusing
chunk 035, then `cosTerm := mkEXP (mkEXP (mkADD (mkLOG iTerm) (mkLOG var)))`.
Eval = exp(exp(log I + log x)) = exp(I·x) for x > 0; .re = cos x.
-/
theorem emlterm1c_for_cos :
    ∃ t : EMLTermℂ₁, ∀ x : ℝ, 0 < x →
      (EMLTermℂ₁.eval (x : ℂ) t).re = Real.cos x := by
  sorry

end EML
