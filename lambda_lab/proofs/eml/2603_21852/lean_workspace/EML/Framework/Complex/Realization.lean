import EML.Framework.Complex.Term

/-!
# Complex EML realizability

`EMLRealizationℂ f` packages an `EMLTermℂ` witness for a partial
function `f : (Nat → ℂ) → Option ℂ`, with a forward-only spec.

Same architecture as the real `EMLRealization` (see
`Framework/Realization.lean`). The compiler `ELExprℂ.compile` returns
`EMLRealizationℂ` instances; the closure lemmas in
`Complex/Closures/*.lean` produce them by composition.
-/

namespace EML

/-- A partial complex-valued function of finitely many complex
arguments. -/
abbrev PartialFunℂ := (Nat → ℂ) → Option ℂ

/-- A complex EML realization of a partial function `f`: an `EMLTermℂ`
together with a forward-only agreement proof. -/
structure EMLRealizationℂ (f : PartialFunℂ) where
  /-- The underlying complex EML term. -/
  term : EMLTermℂ
  /-- Forward agreement: source defined → witness defined and agreeing. -/
  spec : ∀ env v, f env = some v → term.eval? env = some v

namespace EMLRealizationℂ

/-! ## Trivial closures under the EMLTermℂ constructors -/

/-- The constant function `1` is realized by `EMLTermℂ.one`. -/
def one : EMLRealizationℂ (fun _ => some 1) where
  term := .one
  spec := fun _ v hv => by simp at hv; exact hv ▸ rfl

/-- The projection `env n` is realized by `EMLTermℂ.var n`. -/
def var (n : Nat) : EMLRealizationℂ (fun env => some (env n)) where
  term := .var n
  spec := fun _ v hv => by simp at hv; exact hv ▸ rfl

end EMLRealizationℂ

end EML
