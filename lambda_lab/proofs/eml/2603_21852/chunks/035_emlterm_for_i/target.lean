import Mathlib

namespace EML

/-- Complex-valued EML term grammar (extended from the real-valued version). -/
inductive EMLTermℂ : Type
  | one : EMLTermℂ
  | eml : EMLTermℂ → EMLTermℂ → EMLTermℂ
  deriving Repr

/-- Evaluation over ℂ using `Complex.log` (principal branch) and `Complex.exp`. -/
noncomputable def EMLTermℂ.eval : EMLTermℂ → ℂ
  | .one => 1
  | .eml t u => Complex.exp (eval t) - Complex.log (eval u)

/-- The imaginary unit `i` is reachable as a complex EML term.

The full witness is constructed in `lean_workspace/EML/Solutions/035_emlterm_for_i.lean`
using `i = −exp(Lg(−1)/2)`, with the final negation realised via the
chunk-036 trick `(exp z − z) − exp z = −z`, branch-safe because
`(−i).im = −1 ∈ (−π, π]` strictly. -/
theorem emlterm_for_i : ∃ t : EMLTermℂ, EMLTermℂ.eval t = Complex.I := by
  sorry

end EML
