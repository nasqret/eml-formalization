import EML.Framework.Realization
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Intermediate exp-log-arithmetic language (real)

`ELExpr` is the compact intermediate language sitting between the
36-primitive source `F36Expr` and the raw `EMLTerm` target. It
contains:

* atoms: `1`, `var n`, named constants
* the EML primitives `exp`, `log`
* arithmetic: `neg`, `add`, `sub`, `mul`, `div`
* derived primitives that have direct paper analogues: `inv`, `sq`,
  `sqrt`, `pow`, `logb`, `half`, `avg`, `hypot`

Trig is **not** in `ELExpr` directly; it lives in a complex `ELExprℂ`
layer (Phase B+) and gets compiled to `EMLTermℂ` via the same
realizability machinery. The `F36ToEL` translator handles the
real-vs-complex dispatch.

`ELExpr.eval?` is total-domain partial: it returns `none` exactly
when an operation falls outside the natural mathematical domain
(e.g. `log` of non-positive, `inv` of zero, `sqrt` of negative,
`pow` of non-positive base). This keeps the compiler honest — no
junk-value accidents are possible by construction.
-/

namespace EML

/-- Real intermediate exp-log-arithmetic language.

Each constructor's denotation is given by `ELExpr.eval?` below.
Constructors with implicit positivity / non-zero domains return
`none` outside that domain. -/
inductive ELExpr : Type where
  /-- The constant `1`. -/
  | one : ELExpr
  /-- A variable lookup `env n`. -/
  | var : Nat → ELExpr
  /-- The constant `0`. -/
  | zero : ELExpr
  /-- The constant `-1`. -/
  | negOne : ELExpr
  /-- The constant `2`. -/
  | two : ELExpr
  /-- The constant `1/2`. -/
  | half_const : ELExpr
  /-- Euler's number `e`. -/
  | e_const : ELExpr
  /-- Negation `-x`. -/
  | neg : ELExpr → ELExpr
  /-- Multiplicative inverse `1/x`. Defined when `x ≠ 0`. -/
  | inv : ELExpr → ELExpr
  /-- Square `x²`. Defined for all real `x`. -/
  | sq : ELExpr → ELExpr
  /-- Square root `√x`. Defined when `x ≥ 0`. -/
  | sqrt : ELExpr → ELExpr
  /-- Natural exponential `exp x`. Defined for all real `x`. -/
  | exp : ELExpr → ELExpr
  /-- Natural logarithm `log x`. Defined when `x > 0`. -/
  | log : ELExpr → ELExpr
  /-- Halving `x/2`. Defined for all real `x`. -/
  | halve : ELExpr → ELExpr
  /-- Addition. -/
  | add : ELExpr → ELExpr → ELExpr
  /-- Subtraction. -/
  | sub : ELExpr → ELExpr → ELExpr
  /-- Multiplication. -/
  | mul : ELExpr → ELExpr → ELExpr
  /-- Division `x/y`. Defined when `y ≠ 0`. -/
  | div : ELExpr → ELExpr → ELExpr
  /-- Real power `x^y`. Defined when `0 < x` (paper's natural domain;
  the exponent `y` may have any sign). -/
  | pow : ELExpr → ELExpr → ELExpr
  /-- Logarithm with arbitrary base `log_x y = log y / log x`. Defined
  when `0 < x`, `x ≠ 1`, `0 < y` (paper's natural domain; permits
  `0 < x < 1` with negative `log x`). -/
  | logb : ELExpr → ELExpr → ELExpr
  /-- Average `(x+y)/2`. Defined for all real `x, y`. -/
  | avg : ELExpr → ELExpr → ELExpr
  /-- Hypotenuse `√(x²+y²)`. Defined for all real `x, y`. -/
  | hypot : ELExpr → ELExpr → ELExpr
  deriving Repr

/-- Helper: bind two `Option`s and apply a binary operation. -/
@[simp] def bind2 {α β γ} (x : Option α) (y : Option β) (f : α → β → Option γ) :
    Option γ :=
  match x, y with
  | some a, some b => f a b
  | _, _ => none

/-- Domain-aware evaluation. Returns `none` exactly when some
sub-expression falls outside the natural math domain. -/
noncomputable def ELExpr.eval? (env : Nat → ℝ) : ELExpr → Option ℝ
  | .one          => some 1
  | .var n        => some (env n)
  | .zero         => some 0
  | .negOne       => some (-1)
  | .two          => some 2
  | .half_const   => some (1 / 2)
  | .e_const      => some (Real.exp 1)
  -- Phase B+ coverage: with unconditional builders now available
  -- (`Builders/Unconditional.lean`), the partial semantics here are
  -- widened to match each operation's natural mathematical domain.
  --
  -- Wide (full domain): `inv` (≠0), `sq`, `halve`, `mul`, `div` (denom ≠0),
  -- `avg`, `hypot` ((va,vb) ≠ (0,0)), `pow` (only base positivity), `logb`
  -- (`0 < va, va ≠ 1, 0 < vb`).
  -- Still narrow (TODO Phase B++): `sqrt` (0 < va; awaiting unconditional
  -- `mkSqrtAll` to lift to `0 ≤ va`).
  -- `log` is genuinely undefined for `va ≤ 0` and stays narrow.
  | .neg a        => (a.eval? env).map (-·)
  | .inv a        => (a.eval? env).bind fun va => if va ≠ 0 then some va⁻¹ else none
  | .sq a         => (a.eval? env).map (fun va => va ^ 2)
  | .sqrt a       => (a.eval? env).bind fun va =>
                       if 0 < va then some (Real.sqrt va) else none
  | .exp a        => (a.eval? env).map Real.exp
  | .log a        => (a.eval? env).bind fun va =>
                       if 0 < va then some (Real.log va) else none
  | .halve a      => (a.eval? env).map (fun va => va / 2)
  | .add a b      => bind2 (a.eval? env) (b.eval? env) (fun va vb => some (va + vb))
  | .sub a b      => bind2 (a.eval? env) (b.eval? env) (fun va vb => some (va - vb))
  | .mul a b      => bind2 (a.eval? env) (b.eval? env)
                       (fun va vb => some (va * vb))
  | .div a b      => bind2 (a.eval? env) (b.eval? env)
                       (fun va vb => if vb ≠ 0 then some (va / vb) else none)
  | .pow a b      => bind2 (a.eval? env) (b.eval? env)
                       (fun va vb => if 0 < va then some (Real.rpow va vb) else none)
  | .logb a b     => bind2 (a.eval? env) (b.eval? env)
                       (fun va vb =>
                         if 0 < va ∧ va ≠ 1 ∧ 0 < vb
                         then some (Real.log vb / Real.log va) else none)
  | .avg a b      => bind2 (a.eval? env) (b.eval? env)
                       (fun va vb => some ((va + vb) / 2))
  | .hypot a b    => bind2 (a.eval? env) (b.eval? env)
                       (fun va vb =>
                         if ¬(va = 0 ∧ vb = 0)
                         then some (Real.sqrt (va ^ 2 + vb ^ 2)) else none)

@[simp] lemma ELExpr.eval?_one (env : Nat → ℝ) :
    ELExpr.one.eval? env = some 1 := rfl

@[simp] lemma ELExpr.eval?_var (env : Nat → ℝ) (n : Nat) :
    (ELExpr.var n).eval? env = some (env n) := rfl

@[simp] lemma ELExpr.eval?_zero (env : Nat → ℝ) :
    ELExpr.zero.eval? env = some 0 := rfl

@[simp] lemma ELExpr.eval?_two (env : Nat → ℝ) :
    ELExpr.two.eval? env = some 2 := rfl

end EML
