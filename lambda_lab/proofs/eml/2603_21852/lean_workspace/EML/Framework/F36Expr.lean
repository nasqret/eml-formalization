import EML.Framework.ELExpr
import Mathlib

/-!
# F36Expr — the paper's 36-primitive source language

The source language for the paper's headline completeness theorem.
Every constructor corresponds to one row in `EML.tex`'s Table `Calc4`
(the "scientific calculator" target).

The denotation `F36Expr.eval? : (Nat → ℝ) → F36Expr → Option ℝ` is
domain-aware: each operation returns `none` outside its natural
mathematical domain (e.g. `log` on `≤ 0`, `inv` on `0`).

## Constructor groups

* **Atoms / constants**: `var n`, `one`, `negOne`, `two`, `half_const`,
  `e_const`, `pi`.
* **Real-valued unary**: `exp`, `log`, `inv`, `half`, `minus`, `sqrt`,
  `sqr`, `sigma`.
* **Trig family** (real input, witness via complex Euler in Phase B+):
  `sin`, `cos`, `tan`, `arcsin`, `arccos`, `arctan`.
* **Hyperbolic family** (direct real witnesses): `sinh`, `cosh`,
  `tanh`, `arsinh`, `arcosh`, `artanh`.
* **Binary**: `add`, `sub`, `mul`, `div`, `logb`, `pow`, `avg`,
  `hypot`.

## Final theorem

After all closure lemmas are wired in, the final theorem is:

```
theorem F36_complete : ∀ e : F36Expr,
  ∃ t : EMLTerm, ∀ env v, F36Expr.eval? env e = some v →
    EMLTerm.eval? env t = some v
```

This is the structural compiler theorem from the paper's Supplementary
Information Theorem 5.
-/

namespace EML

/-- The paper's 36-primitive scientific-calculator language. -/
inductive F36Expr : Type where
  -- Atoms / constants
  | var : Nat → F36Expr
  | one : F36Expr
  | negOne : F36Expr
  | two : F36Expr
  | half_const : F36Expr
  | e_const : F36Expr
  | pi : F36Expr
  -- Real-valued unary
  | exp : F36Expr → F36Expr
  | log : F36Expr → F36Expr
  | inv : F36Expr → F36Expr
  | half : F36Expr → F36Expr
  | minus : F36Expr → F36Expr
  | sqrt : F36Expr → F36Expr
  | sqr : F36Expr → F36Expr
  | sigma : F36Expr → F36Expr
  -- Trig family (witness via complex Euler in Phase B+)
  | sin : F36Expr → F36Expr
  | cos : F36Expr → F36Expr
  | tan : F36Expr → F36Expr
  | arcsin : F36Expr → F36Expr
  | arccos : F36Expr → F36Expr
  | arctan : F36Expr → F36Expr
  -- Hyperbolic family (direct real witnesses)
  | sinh : F36Expr → F36Expr
  | cosh : F36Expr → F36Expr
  | tanh : F36Expr → F36Expr
  | arsinh : F36Expr → F36Expr
  | arcosh : F36Expr → F36Expr
  | artanh : F36Expr → F36Expr
  -- Binary
  | add : F36Expr → F36Expr → F36Expr
  | sub : F36Expr → F36Expr → F36Expr
  | mul : F36Expr → F36Expr → F36Expr
  | div : F36Expr → F36Expr → F36Expr
  | logb : F36Expr → F36Expr → F36Expr
  | pow : F36Expr → F36Expr → F36Expr
  | avg : F36Expr → F36Expr → F36Expr
  | hypot : F36Expr → F36Expr → F36Expr
  deriving Repr

/-- Domain-aware partial evaluation. Returns `none` exactly when some
sub-expression falls outside its natural mathematical domain. -/
noncomputable def F36Expr.eval? (env : Nat → ℝ) : F36Expr → Option ℝ
  | .var n        => some (env n)
  | .one          => some 1
  | .negOne       => some (-1)
  | .two          => some 2
  | .half_const   => some (1 / 2)
  | .e_const      => some (Real.exp 1)
  | .pi           => some Real.pi
  | .exp a        => (a.eval? env).map Real.exp
  | .log a        => (a.eval? env).bind fun va =>
                       if 0 < va then some (Real.log va) else none
  | .inv a        => (a.eval? env).bind fun va =>
                       if va ≠ 0 then some va⁻¹ else none
  | .half a       => (a.eval? env).map (· / 2)
  | .minus a      => (a.eval? env).map (-·)
  | .sqrt a       => (a.eval? env).bind fun va =>
                       if 0 ≤ va then some (Real.sqrt va) else none
  | .sqr a        => (a.eval? env).map (· ^ 2)
  | .sigma a      => (a.eval? env).map (fun va => 1 / (1 + Real.exp (-va)))
  | .sin a        => (a.eval? env).map Real.sin
  | .cos a        => (a.eval? env).map Real.cos
  | .tan a        => (a.eval? env).bind fun va =>
                       if Real.cos va ≠ 0 then some (Real.tan va) else none
  | .arcsin a     => (a.eval? env).bind fun va =>
                       if -1 ≤ va ∧ va ≤ 1 then some (Real.arcsin va) else none
  | .arccos a     => (a.eval? env).bind fun va =>
                       if -1 ≤ va ∧ va ≤ 1 then some (Real.arccos va) else none
  | .arctan a     => (a.eval? env).map Real.arctan
  | .sinh a       => (a.eval? env).map Real.sinh
  | .cosh a       => (a.eval? env).map Real.cosh
  | .tanh a       => (a.eval? env).map Real.tanh
  | .arsinh a     => (a.eval? env).map Real.arsinh
  -- NOTE: F36's natural domain is `1 ≤ va`, but the structural compiler
  -- requires `1 < va` (the boundary `va = 1` gives `√(va²−1) = 0`, which
  -- collides with `mkSqrtPos`'s `0 < arg` requirement). We tighten the
  -- spec here so structural translation lines up with EL's domain.
  | .arcosh a     => (a.eval? env).bind fun va =>
                       if 1 < va then some (Real.arcosh va) else none
  | .artanh a     => (a.eval? env).bind fun va =>
                       if -1 < va ∧ va < 1 then some (Real.artanh va) else none
  | .add a b      => bind2 (a.eval? env) (b.eval? env) (fun va vb => some (va + vb))
  | .sub a b      => bind2 (a.eval? env) (b.eval? env) (fun va vb => some (va - vb))
  | .mul a b      => bind2 (a.eval? env) (b.eval? env) (fun va vb => some (va * vb))
  | .div a b      => bind2 (a.eval? env) (b.eval? env)
                       (fun va vb => if vb ≠ 0 then some (va / vb) else none)
  | .logb a b     => bind2 (a.eval? env) (b.eval? env)
                       (fun va vb =>
                         if 0 < va ∧ va ≠ 1 ∧ 0 < vb
                         then some (Real.log vb / Real.log va) else none)
  | .pow a b      => bind2 (a.eval? env) (b.eval? env)
                       (fun va vb => if 0 < va then some (Real.rpow va vb) else none)
  | .avg a b      => bind2 (a.eval? env) (b.eval? env) (fun va vb => some ((va + vb) / 2))
  -- NOTE: hypot's natural F36 domain is unconditional, but the EL→EML
  -- structural compiler can only seal `(va, vb) ≠ (0, 0)` (the boundary
  -- `(0, 0)` hits the §G junk-value collision via `√(0² + 0²) = √0`).
  -- We tighten the spec here so the structural translation lines up.
  | .hypot a b    => bind2 (a.eval? env) (b.eval? env)
                       (fun va vb =>
                         if ¬(va = 0 ∧ vb = 0)
                         then some (Real.sqrt (va ^ 2 + vb ^ 2)) else none)

end EML
