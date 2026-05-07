import EML.Framework.EMLPartial

/-!
# EML realizability

`EMLRealization f` packages an EML witness for a partial function
`f : (Nat → ℝ) → Option ℝ` together with the proof that the witness's
partial evaluation matches `f` pointwise.

This is the central data structure of the framework. Closure lemmas
take `EMLRealization`s as input and produce `EMLRealization`s as
output, building larger witnesses from smaller ones. The final
compiler `compile : F36Expr → EMLTerm` is just `(complete e).term`,
where `complete : (e : F36Expr) → EMLRealization (F36.denote e)` is
proved by structural induction.

By packaging the witness as **data** (a `structure`) rather than
hiding it behind `∃`, the compiler stays computable — no
`Classical.choice` needed.

The trivial constructors below (`one`, `var`, `eml`) directly mirror
the EML grammar. Everything else (add, mul, exp, log, sqrt, sin, cos,
…) is built from these by closure lemmas in `Framework/Closure/*.lean`.
-/

namespace EML

/-- A partial real-valued function of finitely many real arguments,
encoded as a function from a variable assignment to `Option ℝ`. -/
abbrev PartialFun := (Nat → ℝ) → Option ℝ

/-- An EML realization of a partial function `f`: an EML term `t`
together with a proof that `t.eval?` agrees with `f` pointwise. -/
structure EMLRealization (f : PartialFun) where
  /-- The underlying EML term. -/
  term : EMLTerm
  /-- Pointwise agreement of partial evaluations. -/
  spec : ∀ env, term.eval? env = f env

namespace EMLRealization

/-! ## Trivial closure under EML constructors -/

/-- The constant function `1` is realized by `EMLTerm.one`. -/
def one : EMLRealization (fun _ => some 1) where
  term := .one
  spec := fun _ => rfl

/-- The projection `env n` is realized by `EMLTerm.var n`. -/
def var (n : Nat) : EMLRealization (fun env => some (env n)) where
  term := .var n
  spec := fun _ => rfl

/-- The combinator: if `f` and `g` are realized, then `eml(f, g)` is
realized. The denoted partial function returns `none` precisely when
either argument is undefined or `g`'s value is non-positive.

This is the unconditional version. For uses where `g > 0` is known,
the convenience corollary `eml_of_pos` below packages the result as
the simpler total form `some (exp f - log g)`. -/
noncomputable def eml {f g : PartialFun}
    (hf : EMLRealization f) (hg : EMLRealization g) :
    EMLRealization (fun env =>
      match f env, g env with
      | some va, some vb =>
          if 0 < vb then some (Real.exp va - Real.log vb) else none
      | _, _ => none) where
  term := .eml hf.term hg.term
  spec := fun env => by
    show (EMLTerm.eml hf.term hg.term).eval? env = _
    unfold EMLTerm.eval?
    rw [hf.spec env, hg.spec env]
    rfl

/-- The convenience eml combinator: when `g`'s realization always
returns a strictly-positive value, the resulting eml realization is
the clean total form `some (exp f - log g)` (no `if-then-else` in
the denoted function). -/
noncomputable def eml_of_pos {f g : PartialFun}
    (hf : EMLRealization f) (hg : EMLRealization g)
    (hpos : ∀ env vg, g env = some vg → 0 < vg) :
    EMLRealization (fun env =>
      match f env, g env with
      | some va, some vb => some (Real.exp va - Real.log vb)
      | _, _ => none) where
  term := .eml hf.term hg.term
  spec := fun env => by
    show (EMLTerm.eml hf.term hg.term).eval? env = _
    unfold EMLTerm.eval?
    rw [hf.spec env, hg.spec env]
    -- Both sides are matches on f env and g env. Case-split on g env;
    -- when it's some vb, hpos gives 0 < vb so the if-then-else collapses.
    cases hge : g env with
    | none => cases hfe : f env <;> rfl
    | some vb =>
      have hvb : 0 < vb := hpos env vb hge
      cases hfe : f env with
      | none => rfl
      | some va => simp [hvb]

/-! ## Worked example: `exp x = eml(x, 1)` -/

/-- Sanity-check realization: `Real.exp (env 0)` is realized by
`eml(var 0, one)`. Direct application of Identity 4. -/
noncomputable example :
    EMLRealization (fun env =>
      match (some (env 0) : Option ℝ), (some 1 : Option ℝ) with
      | some va, some vb => some (Real.exp va - Real.log vb)
      | _, _ => none) :=
  eml_of_pos (var 0) one (fun _ vg h => by
    simp at h; rw [← h]; exact zero_lt_one)

end EMLRealization

end EML

