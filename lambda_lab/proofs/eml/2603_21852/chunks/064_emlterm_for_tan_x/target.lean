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
Recipe (Table S2, step 26 — `tan(x)`, K=5):
    tan(x) = sin(x) / cos(x)        (chunks 062, 063, 050)

The division requires `cos x ≠ 0`, i.e. `x ≠ (k + 1/2)·π` for k ∈ ℤ.
We state the identity over an open neighbourhood of `0`; the full domain
follows by analytic continuation (Mathlib has `Real.tan` defined on the
appropriate set).
-/
theorem emlterm1c_for_tan :
    ∃ t : EMLTermℂ₁, ∀ x : ℝ, Real.cos x ≠ 0 →
      (EMLTermℂ₁.eval (x : ℂ) t).re = Real.tan x := by
  sorry

end EML
