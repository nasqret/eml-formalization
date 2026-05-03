import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace EML

inductive EMLTerm₁ : Type
  | one : EMLTerm₁
  | var : EMLTerm₁
  | eml : EMLTerm₁ → EMLTerm₁ → EMLTerm₁
  deriving Repr

noncomputable def EMLTerm₁.eval (x : ℝ) : EMLTerm₁ → ℝ
  | .one => 1
  | .var => x
  | .eml t u => Real.exp (EMLTerm₁.eval x t) - Real.log (EMLTerm₁.eval x u)

/-
Restricted to `0 < x`.

A genuine universal `∀ x : ℝ` version is not reachable in pure `EMLTerm₁`:
the natural construction `exp(2 · log x)` works only when `x > 0` because
`Real.log` returns its junk value `0` on `x ≤ 0`. A single witness term
cannot branch on the sign of `x`, and the closure of `{1, x, exp, log, –}`
does not contain absolute value or unrestricted multiplication, both of
which would be needed to produce `x²` for negative `x`. Tested at the
existing witness: `sqTerm.eval 0 = 1 ≠ 0` and `sqTerm.eval (-1) ≠ 1`.

Compare chunk 036 (`-x`), which IS universal because `-x` is in the closure
on all of `ℝ` via `(exp x − x) − exp x = −x` (no `log x` involved).
-/
theorem emlterm1_for_sq_x_pos :
    ∃ t : EMLTerm₁, ∀ x : ℝ, 0 < x → EMLTerm₁.eval x t = x ^ 2 := by
  sorry

end EML
