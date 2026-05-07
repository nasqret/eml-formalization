import EML.Framework.Complex.Partial

/-!
# Complex EML term language

`EMLTermℂ` is the complex-valued analogue of `EMLTerm`. The grammar is
the same — `one`, `var`, `eml` — but evaluation lands in `Option ℂ`
with a partial `eml` rule:

```
eml(a, b).eval? env = if b.eval? env = some vb ≠ 0
                      then some (Complex.exp(a.eval) − Complex.log vb)
                      else none
```

Same forward-only spec convention as the real layer (see
`Framework/EMLPartial.lean`).
-/

namespace EML

/-- Abstract syntax of a complex EML term. -/
inductive EMLTermℂ where
  /-- The constant `1`. -/
  | one : EMLTermℂ
  /-- A variable lookup `env n`. -/
  | var : Nat → EMLTermℂ
  /-- `eml(a, b) = exp(a) − log(b)`, partial when `b = 0`. -/
  | eml : EMLTermℂ → EMLTermℂ → EMLTermℂ
  deriving Repr

/-- Partial-semantics evaluation. Returns `none` if any nested
`eml(_, b)` has `b ≠ 0` violated. -/
noncomputable def EMLTermℂ.eval? (env : Nat → ℂ) : EMLTermℂ → Option ℂ
  | .one     => some 1
  | .var n   => some (env n)
  | .eml a b =>
      match EMLTermℂ.eval? env a, EMLTermℂ.eval? env b with
      | some va, some vb =>
          if vb = 0 then none else some (Complex.exp va - Complex.log vb)
      | _, _ => none

@[simp] lemma EMLTermℂ.eval?_one (env : Nat → ℂ) :
    (EMLTermℂ.one).eval? env = some 1 := rfl

@[simp] lemma EMLTermℂ.eval?_var (env : Nat → ℂ) (n : Nat) :
    (EMLTermℂ.var n).eval? env = some (env n) := rfl

/-- Constructive `eml` rule: when both children evaluate and the
second is non-zero, the partial eval gives the expected value. -/
lemma EMLTermℂ.eval?_eml_of_ne
    {env : Nat → ℂ} {a b : EMLTermℂ} {va vb : ℂ}
    (ha : a.eval? env = some va) (hb : b.eval? env = some vb)
    (hvb : vb ≠ 0) :
    (EMLTermℂ.eml a b).eval? env = some (Complex.exp va - Complex.log vb) := by
  unfold EMLTermℂ.eval?
  rw [ha, hb]
  simp [hvb]

end EML
