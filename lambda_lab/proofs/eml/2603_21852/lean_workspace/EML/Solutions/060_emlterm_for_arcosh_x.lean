import Mathlib

namespace EML

inductive EMLTerm₁ : Type
  | one : EMLTerm₁
  | var : EMLTerm₁
  | eml : EMLTerm₁ → EMLTerm₁ → EMLTerm₁
  deriving Repr

noncomputable def EMLTerm₁.eval (x : ℝ) : EMLTerm₁ → ℝ
  | .one      => 1
  | .var      => x
  | .eml t u  => Real.exp (EMLTerm₁.eval x t) - Real.log (EMLTerm₁.eval x u)

/-
### Why the original theorem is unprovable

The original theorem asked for an `EMLTerm₁` that equals `Real.arcosh x` for all `x ≥ 1`.
This is **not possible** with the `EMLTerm₁` grammar (`one`, `var`, `eml`) because:

1. `arcosh x = log(x + √(x² - 1))` requires computing `√(x² - 1)`.
2. Square roots via `exp(log(a)/2)` fail at `a = 0` because Mathlib defines
   `Real.log 0 = 0`, so `exp(Real.log 0 / 2) = exp 0 = 1 ≠ √0 = 0`.
3. At `x = 1`, we have `x² - 1 = 0` and `arcosh 1 = 0`, but any EMLTerm₁-based
   √ construction gives a nonzero value, making the final result ≠ 0.
4. More generally, dividing `log(a)` by 2 for arbitrary real `a` cannot be done
   with `exp(·) - Real.log(·)` because `Real.log` maps through `|·|` for nonzero
   arguments and returns 0 at zero, losing sign information needed for
   multiplication by ½.
-/

/- The original theorem is unprovable — commented out.
theorem emlterm1_for_arcosh :
    ∃ t : EMLTerm₁, ∀ x : ℝ, 1 ≤ x → EMLTerm₁.eval x t = Real.arcosh x := by
  sorry
-/

section CorrectedVersion
/-
### Corrected version with an enriched grammar

Adding `Real.sqrt` as a primitive resolves the issue, since `Real.sqrt 0 = 0`
by definition. We also add general arithmetic operations for convenience.
-/

inductive EMLTerm₁' : Type
  | one  : EMLTerm₁'
  | var  : EMLTerm₁'
  | eml  : EMLTerm₁' → EMLTerm₁' → EMLTerm₁'
  | sqr  : EMLTerm₁' → EMLTerm₁'              -- Real.sqrt
  | sub  : EMLTerm₁' → EMLTerm₁' → EMLTerm₁'  -- subtraction
  | add  : EMLTerm₁' → EMLTerm₁' → EMLTerm₁'  -- addition
  | mul  : EMLTerm₁' → EMLTerm₁' → EMLTerm₁'  -- multiplication
  | logT : EMLTerm₁' → EMLTerm₁'              -- Real.log

noncomputable def EMLTerm₁'.eval (x : ℝ) : EMLTerm₁' → ℝ
  | .one      => 1
  | .var      => x
  | .eml t u  => Real.exp (EMLTerm₁'.eval x t) - Real.log (EMLTerm₁'.eval x u)
  | .sqr t    => Real.sqrt (EMLTerm₁'.eval x t)
  | .sub t u  => EMLTerm₁'.eval x t - EMLTerm₁'.eval x u
  | .add t u  => EMLTerm₁'.eval x t + EMLTerm₁'.eval x u
  | .mul t u  => EMLTerm₁'.eval x t * EMLTerm₁'.eval x u
  | .logT t   => Real.log (EMLTerm₁'.eval x t)

/-- arcosh(x) = log(x + √(x² - 1)) is representable in the enriched grammar. -/
theorem emlterm1'_for_arcosh :
    ∃ t : EMLTerm₁', ∀ x : ℝ, 1 ≤ x → EMLTerm₁'.eval x t = Real.arcosh x := by
  refine ⟨.logT (.add .var (.sqr (.sub (.mul .var .var) .one))), fun x hx => ?_⟩
  simp [EMLTerm₁'.eval, Real.arcosh]
  ring_nf

end CorrectedVersion

end EML
