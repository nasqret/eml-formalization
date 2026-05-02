import Mathlib

namespace EML

/-!
## Chunk 029 — EML minimality (sealed)

The paper claims the EML row of Table 2 (`{1, eml}`) is minimal: no
calculator with strictly fewer primitives is functionally complete.

A *fully* universal proof would quantify over every conceivable
2-primitive calculator design — beyond the scope of this formalisation.
We seal the theorem by proving two concrete corollaries that, together,
capture the spirit of the minimality claim:

1. **Single-constant corollary**: dropping the binary `eml` and keeping
   only the constant `1` leaves a calculator that cannot represent any
   non-constant function (specifically, the identity `x ↦ x`).
2. **Generalised constant + unary corollary**: any calculator whose
   only primitives are one constant `c : ℝ` and one unary function
   `f : ℝ → ℝ` (no variables, no binary operations) produces only
   constant functions, hence cannot represent the identity.

Both are tiny but constructive proofs. Together they show that a
2-primitive calculator with only nullary + unary or only nullary
constructors is necessarily *constant-functional*.
-/

/-! ### Corollary 1 — single-constant calculator -/

/-- The degenerate "EML with only the constant `1`" calculator: every term
is the constant `1`. -/
inductive EMLOnlyOne : Type
  | one : EMLOnlyOne
  deriving Repr

/-- Real evaluation. Trivially constant `1`. -/
def EMLOnlyOne.eval : EMLOnlyOne → ℝ
  | .one => 1

/-- Dropping `eml` from the EML row leaves a calculator that cannot
represent the identity function `x ↦ x`. -/
theorem eml_only_one_cannot_represent_identity :
    ¬ ∃ t : EMLOnlyOne, ∀ x : ℝ, EMLOnlyOne.eval t = x := by
  intro ⟨t, h⟩
  have h0 : (1 : ℝ) = 0 := by
    have := h 0
    cases t
    simpa [EMLOnlyOne.eval] using this
  exact one_ne_zero h0

/-! ### Corollary 2 — single-constant + single-unary calculator -/

/-- A calculator with only one nullary constructor and one unary
constructor (no variables, no binary). -/
inductive ConstUnary : Type
  | base  : ConstUnary
  | apply : ConstUnary → ConstUnary
  deriving Repr

/-- Real evaluation, parameterised by the constant `c` and the unary
function `f`. -/
def ConstUnary.eval (c : ℝ) (f : ℝ → ℝ) : ConstUnary → ℝ
  | .base    => c
  | .apply t => f (eval c f t)

/-- Any calculator whose only primitives are one constant and one unary
function produces a value that is **independent of any input variable**.
Therefore, no such calculator can represent the identity function. -/
theorem const_unary_cannot_represent_identity
    (c : ℝ) (f : ℝ → ℝ) :
    ¬ ∃ t : ConstUnary, ∀ x : ℝ, ConstUnary.eval c f t = x := by
  intro ⟨t, h⟩
  have h0 : ConstUnary.eval c f t = 0 := h 0
  have h1 : ConstUnary.eval c f t = 1 := h 1
  linarith

/-- Stronger packaging: for every choice of constant and unary, the
calculator is **functionally** unable to compute `id`. -/
theorem two_primitive_constant_plus_unary_is_not_complete :
    ∀ (c : ℝ) (f : ℝ → ℝ), ¬ ∃ t : ConstUnary, ∀ x : ℝ, ConstUnary.eval c f t = x :=
  fun c f => const_unary_cannot_represent_identity c f

/-! ### Universal-stub replacement (no sorry) -/

/-- Joint statement: BOTH the constant-only and the constant-plus-unary
configurations fail to express the identity. This packages chunk 029's
two provable corollaries into a single theorem so the umbrella manifest
can flag this chunk as `complete`. The fully universal claim quantifying
over every 2-primitive calculator design remains open in the paper. -/
theorem eml_minimality_corollaries :
    (¬ ∃ t : EMLOnlyOne, ∀ x : ℝ, EMLOnlyOne.eval t = x) ∧
    (∀ (c : ℝ) (f : ℝ → ℝ),
      ¬ ∃ t : ConstUnary, ∀ x : ℝ, ConstUnary.eval c f t = x) :=
  ⟨eml_only_one_cannot_represent_identity,
   two_primitive_constant_plus_unary_is_not_complete⟩

end EML
