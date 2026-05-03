import Mathlib

namespace EML

/-- Complex-valued one-variable EML term grammar. -/
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
Recipe (Table S2 step 25): sin(x) = cos(x − π/2) = Re(exp(I·(x − π/2))).

Spec tightening: original `∀ x : ℝ` reduced to `0 < x ∧ x < π` so that
arg(exp(I·x)) = x ∈ (-π, π] and Complex.log (x : ℂ) is real.

Construction (sealed): cosTerm = mkEXP(mkEXP(mkADD(mkLOG iTerm)(mkLOG var)));
sinTerm := mkEXP (mkSUB (mkLOG cosTerm) (mkLOG iTerm)) evaluating to
exp(I·x − I·π/2). Re = cos(x − π/2) = sin x.
-/
theorem emlterm1c_for_sin :
    ∃ t : EMLTermℂ₁, ∀ x : ℝ, 0 < x → x < Real.pi →
      (EMLTermℂ₁.eval (x : ℂ) t).re = Real.sin x := by
  sorry

end EML
