import EML.Basic

/-!
# EML term language

A first-class syntactic representation of EML expressions, together with
its size measure and semantic evaluation under a variable environment.
The grammar follows the paper:

```
S -> 1 | var n | eml(S, S)
```

`var` nodes are included so we can speak about parameterized expressions
(e.g. `exp(x) = eml(x, 1)` as a function of `x`) without reaching outside
the `EMLTerm` type.
-/

namespace EML

/-- Abstract syntax of EML expressions. -/
inductive EMLTerm
  | one : EMLTerm
  | var : Nat → EMLTerm
  | eml : EMLTerm → EMLTerm → EMLTerm
  deriving Repr

namespace EMLTerm

/-- Number of nodes in an `EMLTerm`. -/
def size : EMLTerm → Nat
  | one     => 1
  | var _   => 1
  | eml a b => 1 + size a + size b

/-- Evaluate an `EMLTerm` under a variable assignment `env : Nat -> Real`. -/
noncomputable def eval (env : Nat → ℝ) : EMLTerm → ℝ
  | one     => 1
  | var n   => env n
  | eml a b => EML.eml (eval env a) (eval env b)

/-- Every `EMLTerm` has at least one node. -/
lemma size_pos : ∀ t : EMLTerm, 1 ≤ t.size
  | one     => Nat.le_refl 1
  | var _   => Nat.le_refl 1
  | eml a b => by
      show 1 ≤ 1 + a.size + b.size
      omega

end EMLTerm

end EML
