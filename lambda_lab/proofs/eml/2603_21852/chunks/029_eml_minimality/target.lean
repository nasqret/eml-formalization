import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import EML.Calc

namespace EML

/-- Calc EML restricted to **just the constant `1`** (no `eml` operator,
no variables): every term is the constant `1`. This is a degenerate
configuration that cannot express the function `x ↦ x`. -/
inductive EMLOnlyOne : Type
  | one : EMLOnlyOne
  deriving Repr

/-- Real evaluation of `EMLOnlyOne`. Trivially constant `1`. -/
def EMLOnlyOne.eval : EMLOnlyOne → ℝ
  | .one => 1

/-- **Minimality of the EML calculator** (Table 2 closing remark).

The paper claims: no calculator with strictly fewer than three
primitives suffices for elementary expressiveness.

We formalise one operational corollary: dropping the binary `eml`
from the EML row leaves only the constant `1`, which cannot
represent the identity function `x ↦ x`. (Symmetric arguments rule
out the other 2-element subsets.)

A *complete* minimality proof — quantified over all calculator
configurations of size < 3 — is open in the paper and remains
beyond this formalisation pass. We keep the witness for the
single-constant-only case and leave the universal claim as
`sorry`. -/
theorem eml_only_one_cannot_represent_identity :
    ¬ ∃ t : EMLOnlyOne, ∀ x : ℝ, EMLOnlyOne.eval t = x := by
  intro ⟨t, h⟩
  -- t = .one, so EMLOnlyOne.eval t = 1 for every x; choose x ≠ 1.
  have h0 : (1 : ℝ) = 0 := by
    have := h 0
    cases t
    simpa [EMLOnlyOne.eval] using this
  exact one_ne_zero h0

/-- Universal minimality (open in the paper). -/
theorem eml_minimality_universal : True := by
  sorry

end EML
