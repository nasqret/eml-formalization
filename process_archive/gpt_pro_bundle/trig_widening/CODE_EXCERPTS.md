# Code excerpts — full Lean source for the trig-widening problem

> This file contains the complete (or near-complete) text of every Lean
> definition and lemma referenced in `PROMPT.md`. Pro should be able to
> answer all questions from this file alone.

## 1. The fixed eval rule (Term.lean)

```lean
-- Framework/Complex/Term.lean (full file, 60 lines)

import EML.Framework.Complex.Partial

namespace EML

inductive EMLTermℂ where
  | one : EMLTermℂ
  | var : Nat → EMLTermℂ
  | eml : EMLTermℂ → EMLTermℂ → EMLTermℂ
  deriving Repr

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

lemma EMLTermℂ.eval?_eml_of_ne
    {env : Nat → ℂ} {a b : EMLTermℂ} {va vb : ℂ}
    (ha : a.eval? env = some va) (hb : b.eval? env = some vb)
    (hvb : vb ≠ 0) :
    (EMLTermℂ.eml a b).eval? env = some (Complex.exp va - Complex.log vb) := by
  unfold EMLTermℂ.eval?
  rw [ha, hb]
  simp [hvb]

end EML
```

## 2. The `mkLogℂ` macro and its current closure lemma

```lean
-- Framework/Complex/Closures/Trig.lean

/-- `mkExpℂ T := eml(T, 1)`. Evaluates to `Complex.exp(T.eval)` for
any `T` with a defined eval (since `eml(T, 1) = exp(T.eval) − log 1 =
exp(T.eval)`). No precondition. -/
def mkExpℂ (T : EMLTermℂ) : EMLTermℂ := .eml T .one

lemma eval?_mkExpℂ {env : Nat → ℂ} {T : EMLTermℂ} {v : ℂ}
    (hT : T.eval? env = some v) :
    (mkExpℂ T).eval? env = some (Complex.exp v) := by
  unfold mkExpℂ
  have h := EMLTermℂ.eval?_eml_of_ne hT (EMLTermℂ.eval?_one env) one_ne_zero
  rw [Complex.log_one, sub_zero] at h
  exact h

/-- `mkLogℂ T := eml(1, eml(eml(1, T), 1))`. Evaluates to
`Complex.log(T.eval)` whenever `T.eval ≠ 0` AND `arg(T.eval) < π`. -/
def mkLogℂ (T : EMLTermℂ) : EMLTermℂ := .eml .one (.eml (.eml .one T) .one)

lemma eval?_mkLogℂ {env : Nat → ℂ} {T : EMLTermℂ} {v : ℂ}
    (hT : T.eval? env = some v) (hv : v ≠ 0)
    (harg : Complex.arg v < Real.pi) :
    (mkLogℂ T).eval? env = some (Complex.log v) := by
  unfold mkLogℂ
  -- inner: eml(one, T) = exp 1 - log v
  have h1 : (EMLTermℂ.eml .one T).eval? env =
      some (Complex.exp 1 - Complex.log v) :=
    EMLTermℂ.eval?_eml_of_ne (EMLTermℂ.eval?_one env) hT hv
  -- next: eml(eml(one, T), one) = exp(exp 1 - log v)
  have h2 : (EMLTermℂ.eml (.eml .one T) .one).eval? env =
      some (Complex.exp (Complex.exp 1 - Complex.log v)) := by
    have := EMLTermℂ.eval?_eml_of_ne h1 (EMLTermℂ.eval?_one env) one_ne_zero
    rw [Complex.log_one, sub_zero] at this
    exact this
  -- non-zero: exp _ ≠ 0
  have hexp_ne : Complex.exp (Complex.exp 1 - Complex.log v) ≠ 0 :=
    Complex.exp_ne_zero _
  -- outer: eml(one, ...) = exp 1 - log(exp(exp 1 - log v))
  have h3 := EMLTermℂ.eval?_eml_of_ne (EMLTermℂ.eval?_one env) h2 hexp_ne
  rw [h3]
  congr 1
  -- Compute log(exp w) = w when w.im ∈ (-π, π].
  -- w = exp 1 - log v, w.im = - (log v).im = - arg v.
  have hL_im : (Complex.log v).im = Complex.arg v := Complex.log_im v
  have hexp1_im : (Complex.exp 1).im = 0 := by simp [Complex.exp_im]
  have hw_im : (Complex.exp 1 - Complex.log v).im = -Complex.arg v := by
    rw [Complex.sub_im, hexp1_im, zero_sub, hL_im]
  rw [Complex.log_exp]
  · ring
  · rw [hw_im]; linarith
  · rw [hw_im]; linarith [Complex.neg_pi_lt_arg v]
```

The strict `harg : Complex.arg v < Real.pi` flows from
`Complex.log_exp`'s strict lower bound `-π < z.im`.

## 3. The `mkAddℂ` macro and its closure lemma (the gnarliest)

```lean
-- Framework/Complex/Builders/Trig.lean

/-- Precondition bundle for `mkAddℂ`. -/
structure ADDsafeℂ (a b : ℂ) : Prop where
  ha₁ : -Real.pi < a.im
  ha₂ : a.im ≤ Real.pi
  hema₁ : -Real.pi < (Complex.exp 1 - a).im
  hema₂ : (Complex.exp 1 - a).im ≤ Real.pi
  hexpa_a_ne : Complex.exp a - a ≠ 0
  hb₁ : -Real.pi < b.im
  hb₂ : b.im ≤ Real.pi
  helogexpa₁ :
    -Real.pi < (Complex.exp 1 - Complex.log (Complex.exp a - a)).im
  helogexpa₂ :
    (Complex.exp 1 - Complex.log (Complex.exp a - a)).im ≤ Real.pi
  hexp_a_a_b₁ : -Real.pi < (Complex.exp a - a - b).im
  hexp_a_a_b₂ : (Complex.exp a - a - b).im ≤ Real.pi

/-- The `mkAddℂ` term shape (chunk-062 pattern, lifted into `EMLTermℂ`). -/
def mkAddℂ (A B : EMLTermℂ) : EMLTermℂ :=
  .eml
    (.eml .one (.eml (.eml .one (.eml A .one)) .one))
    (.eml
      (.eml (.eml .one (.eml (.eml .one (.eml A (.eml A .one))) .one))
            (.eml B .one))
      .one)

/-- Closure: under `ADDsafeℂ`, `mkAddℂ A B` evaluates to `va + vb`. -/
lemma eval?_mkAddℂ {env : Nat → ℂ} {A B : EMLTermℂ} {va vb : ℂ}
    (hA : A.eval? env = some va) (hB : B.eval? env = some vb)
    (H : ADDsafeℂ va vb) :
    (mkAddℂ A B).eval? env = some (va + vb)
```

(13-line proof, omitted; mechanically threads the 8 `ADDsafeℂ`
conditions through 6 `eval?_eml_of_ne` applications.)

## 4. Multiplication, subtraction, division

```lean
def mkMulℂ (A B : EMLTermℂ) : EMLTermℂ :=
  mkExpℂ (mkAddℂ (mkLogℂ A) (mkLogℂ B))

lemma eval?_mkMulℂ {env : Nat → ℂ} {A B : EMLTermℂ} {va vb : ℂ}
    (hA : A.eval? env = some va) (hB : B.eval? env = some vb)
    (hva_ne : va ≠ 0) (hvb_ne : vb ≠ 0)
    (h_arg_a : Complex.arg va < Real.pi)
    (h_arg_b : Complex.arg vb < Real.pi)
    (Hadd : ADDsafeℂ (Complex.log va) (Complex.log vb)) :
    (mkMulℂ A B).eval? env = some (va * vb)

def mkSubℂ (A B : EMLTermℂ) : EMLTermℂ := .eml (mkLogℂ A) (mkExpℂ B)
-- mkSubℂ A B = exp(log A) − log(exp B) = A − B under
-- arg(A) < π, A ≠ 0, B.im ∈ (−π, π].

def mkDivℂ (A B : EMLTermℂ) : EMLTermℂ :=
  mkExpℂ (mkSubℂ (mkLogℂ A) (mkLogℂ B))
```

## 5. The trig witnesses

### `cosTermℂ` — currently sealed on `ℝ ∖ {0}` (the only one that works)

```lean
private def cosLhsℂ : EMLTermℂ :=
  .eml .one (.eml (.eml .one (.eml (mkLogℂ iTermℂ) .one)) .one)

private def cosRhsℂ : EMLTermℂ :=
  .eml
    (.eml (.eml .one (.eml (.eml .one (.eml (mkLogℂ iTermℂ) (.eml (mkLogℂ iTermℂ) .one))) .one))
          (.eml (mkLogℂ (.var 0)) .one))
    .one

def cosTermℂ : EMLTermℂ :=
  mkExpℂ (mkExpℂ (.eml cosLhsℂ cosRhsℂ))
-- Evaluates to exp(exp(log i + log x)) = exp(i*x) when env 0 = (x : ℝ), x > 0.
-- The OUTER mkExpℂ is what saves us — any 2πi shift in inner mkLogℂ
-- gets absorbed by Complex.exp_periodic.
```

### `sinTermℂ` — sealed on `(0, π)` (positive side)

```lean
-- Built via the identity sin x = cos(π/2 − x).
-- Outermost is essentially mkLogℂ extracted via .im.
-- Concretely (omitting some helper unfolding):
def sinTermℂ : EMLTermℂ :=
  -- (long term — 1703 nodes)
  -- bridge: sinTermℂ.eval? env_x = some vc, vc.re = Real.sin x
  ...

-- Companion (negative side, x ∈ (−π, 0)):
def sinTermℂ_neg : EMLTermℂ :=
  -- uses log(−i) = −iπ/2 to mirror sinTermℂ across the y-axis
  -- 1439 nodes
  ...
```

The narrowness comes from intermediate `mkMulℂ iTermℂ (.var 0)` calls
that need `arg(var 0) < π`, failing on the negative real ray.

### `arctanTermℂ` — sealed on `(0, π)`

```lean
def arctanTermℂ : EMLTermℂ :=
  mkLogℂ (mkAddℂ .one (mkMulℂ iTermℂ (.var 0)))
-- arctanTermℂ.eval? env_x = some vc, vc.im = Real.arctan x.
-- Outermost is mkLogℂ — exposes .im directly. The inner mkMulℂ blocks
-- on negative-real var 0.
```

### `tanCoreTermℂ` — sealed on `(0, π/2)` (Cayley quotient)

```lean
noncomputable def tanCoreTermℂ : EMLTermℂ :=
  let twoX := mkMulℂ twoPubℂ (.var 0)
  let I2x  := mkMulℂ iTermPubℂ twoX
  let E2   := mkExpℂ I2x
  mkDivℂ (mkSubℂ E2 .one) (mkAddℂ .one E2)
-- (eval).im = tan x for x ∈ (0, π/2).
-- Outermost is mkDivℂ. Same arg(var 0) < π blocker.
```

## 6. The substitution machinery (Plan C foundation, already built)

```lean
-- Framework/Complex/Subst.lean (full file, 95 lines)

namespace EML
namespace EMLTermℂ

def subst0 : EMLTermℂ → EMLTermℂ → EMLTermℂ
  | .one,       _ => .one
  | .var 0,     s => s
  | .var (n+1), _ => .var (n+1)
  | .eml a b,   s => .eml (a.subst0 s) (b.subst0 s)

def envShift0 (s_val : ℂ) (env : Nat → ℂ) : Nat → ℂ :=
  fun n => if n = 0 then s_val else env n

lemma eval?_subst0 {env : Nat → ℂ} {s : EMLTermℂ} {s_val : ℂ}
    (hs : s.eval? env = some s_val)
    (t : EMLTermℂ) :
    (t.subst0 s).eval? env = t.eval? (envShift0 s_val env) := by
  induction t with
  | one => rfl
  | var n =>
    match n with
    | 0 =>
      rw [subst0_var_zero, hs]
      rw [EMLTermℂ.eval?_var, envShift0_zero]
    | n + 1 =>
      rw [subst0_var_succ]
      rw [EMLTermℂ.eval?_var, EMLTermℂ.eval?_var, envShift0_succ]
  | eml a b iha ihb =>
    rw [subst0_eml]
    unfold EMLTermℂ.eval?
    rw [iha, ihb]

end EMLTermℂ
end EML
```

## 7. Real-fragment subtraction (for Path C's shift term construction)

`ELExpr` has subtraction:

```lean
| sub : ELExpr → ELExpr → ELExpr
-- ELExpr.sub a b evaluates to (a.eval - b.eval) under partial eval

-- ELExpr does NOT have `pi` as an atom; pi lives only in F36Expr (paper layer).
```

`piPubℂ : EMLTermℂ` is available (evaluates to `((Real.pi : ℝ) : ℂ)`)
via `EMLRealizationℂ.realizeℂ_pi.term`. K = 233.

For Path C, the shift term `s_k : EMLTermℂ` for `x − 2πk` would be:

```lean
-- ℂ-level: subtract 2πk from var 0
noncomputable def shift2πKℂ (k : ℤ) : EMLTermℂ :=
  -- want: evaluates to ((x - 2π * k : ℝ) : ℂ) when env 0 = ((x : ℝ) : ℂ)
  if k = 0 then .var 0
  else
    -- mkSubℂ (.var 0) (mkMulℂ (intToTerm k) piPubℂ)
    -- but mkMulℂ's arg-π constraint and intToTerm's positivity needs care
    sorry  -- this is the construction we're asking Pro about
```

## 8. Mathlib facts available

- `Complex.log_exp : -π < z.im → z.im ≤ π → Complex.log (Complex.exp z) = z`
- `Complex.arg z ∈ (−π, π]` always; `Complex.arg z = π ↔ z is negative real`
- `Complex.exp_periodic : Function.Periodic Complex.exp (2 * π * I)`
- `Complex.exp_int_mul_two_pi_mul_I : ∀ k : ℤ, Complex.exp (k * (2 * π * I)) = 1`
- `Real.sin_periodic : Function.Periodic Real.sin (2 * π)`
- `Real.cos_periodic : Function.Periodic Real.cos (2 * π)`
- `Real.tan_periodic : Function.Periodic Real.tan π`
- `Real.arctan` has no periodicity but `arctan` extends to `(−π/2, π/2)`
  natively; the question for `arctan` is "all of ℝ" since `arctan` has
  domain ℝ.

## 9. Existing companion technique (precedent for Path C-style solutions)

For each narrow trig primitive, we have a *companion* witness for the
opposite half:

| Primitive | Positive-side witness | Negative-side companion | Identity used |
|---|---|---|---|
| `cos` | `cosTermℂ` (`x > 0`) | `cosTermℂ_neg` (`x < 0`) | `cos(−x) = cos x` |
| `sin` | `sinTermℂ` (`x ∈ (0, π)`) | `sinTermℂ_neg` (`x ∈ (−π, 0)`) | `sin x = cos(π/2 − x)`, `log(−i) = −iπ/2` |
| `tan` | `tanCoreTermℂ` (`x ∈ (0, π/2)`) | `tanCoreTermℂ_neg` (`x ∈ (−π/2, 0)`) | swap-numerator Cayley |
| `arctan` | `arctanTermℂ` (`x > 0`) | `arctanTermℂ_neg` (`x < 0`) | `1 + ix = 1 − i·(−x)` |

The paper-claim uses paired existentials:
```
paper_claim_sin : ∃ t_pos, ∀ x ∈ (0, π), ∃ vc, ...
paper_claim_sin_neg : ∃ t_neg, ∀ x ∈ (−π, 0), ∃ vc, ...
paper_claim_sin_zero : ∀ env, sinTermℂ_at_zero.eval? env = some 0
```

So we already have witness *pairs* per primitive — the companions
mirror Path C's "different witnesses per region", just for two regions.
Path C extends this from 2 regions to ℤ-many regions via periodicity.
The architectural precedent is established.
