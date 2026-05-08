# GPT Pro consult — full-real-domain trig in Lean 4 EML formalization

## What we want from you

We have a Lean 4 + Mathlib v4.28 formalization of arXiv:2603.21852
(Odrzywołek, *"All elementary functions from a single binary operator"*).
36/36 paper primitives are sealed end-to-end, sorry-free; `lake build`
gives 8055 jobs. Three structural boundary points and a trig-narrowing
mismatch with the paper remain.

**The trig narrowing is the bottleneck we want your help with.** The
paper claims (line 328) "EML-compiled expressions work on the real axis,
both positive and negative, except for a few isolated points". Our
artefact narrows trig primitives to symmetric subdomains around 0:
- `cos` on `ℝ ∖ {0}` ✓ (matches paper)
- `sin`, `arctan` on `(−π, π) ∖ {0}` ✗
- `tan` on `(−π/2, π/2) ∖ {0}` ✗
- `arccos`, `arcsin` on full open `(−1, 1)` ✓ (matches paper, natural domain)

Three candidate paths to close the gap are described below. **We want
your independent recommendation** on which path is cleanest in Lean,
plus any path we haven't thought of. Detailed sub-questions at the end.

---

## Project architecture (60 seconds)

```
F36Expr  --- 36-primitive source language (paper's named constructors)
   │
   │  translate?
   ▼
ELExpr  --- exp/log/arithmetic intermediate (real)
   │
   │  compile (structural compiler — Theorem 2)
   ▼
EMLTerm  --- pure single-operator grammar T ::= 1 ∣ xₙ ∣ eml(T, T)
              eml(a, b) := exp(a) − log(b)
   │
   │  ι : EMLTerm → EMLTermℂ (homomorphic embedding)
   ▼
EMLTermℂ  --- complex-coefficient version, same syntax, ℂ semantics
              eml.eval = Complex.exp(a) − Complex.log(b)
```

Each `paper_claim_<f>` is a one-line existential

```
∃ t : EMLTermℂ, ∀ env : ℕ → ℂ, t.eval? env = some (paper_value)
```

with `eval?` partial (`Option ℂ`) and `none` exactly when a nested
`eml(_, b)` would have `b = 0`.

## The fixed eval rule (the hard constraint)

`EMLTermℂ.eval?` is hard-coded to use Mathlib's principal `Complex.log`:

```lean
-- Framework/Complex/Term.lean
noncomputable def EMLTermℂ.eval? (env : Nat → ℂ) : EMLTermℂ → Option ℂ
  | .one     => some 1
  | .var n   => some (env n)
  | .eml a b =>
      match eval? env a, eval? env b with
      | some va, some vb =>
          if vb = 0 then none else some (Complex.exp va - Complex.log vb)
      | _, _ => none
```

There is **no way** to swap in a different log branch from inside the
EML term language. This rules out the "custom log function" reformulation
that the paper's prose suggests (line 333: *"redefine the branch for EML
itself…"* — we read this as paper's compiler swapping witnesses, not
the underlying log).

## The macro layer that all witnesses use

Built in `Framework/Complex/Closures/Trig.lean` and `Framework/Complex/Builders/Trig.lean`:

```lean
def mkExpℂ (T : EMLTermℂ) : EMLTermℂ := .eml T .one
-- evaluates to Complex.exp(T.eval) under T.eval ≠ 0 NOT required (any T)

def mkLogℂ (T : EMLTermℂ) : EMLTermℂ := .eml .one (.eml (.eml .one T) .one)
-- evaluates to Complex.log(T.eval) when T.eval ≠ 0  AND  arg(T.eval) < π

def mkAddℂ (A B : EMLTermℂ) : EMLTermℂ := /- 9-node tree -/
-- evaluates to va + vb under the ADDsafeℂ bundle (8 conditions on imag parts)

def mkMulℂ (A B : EMLTermℂ) : EMLTermℂ := mkExpℂ (mkAddℂ (mkLogℂ A) (mkLogℂ B))
-- evaluates to va * vb when arg va < π, arg vb < π, ADDsafeℂ on logs
```

The `arg < π` constraint on `mkLogℂ` is the strict source of all narrowness.

## Why the constraint is strict

`mkLogℂ T` reduces (via three nested `eml` evaluations) to
`Complex.exp 1 − Complex.log (Complex.exp (Complex.exp 1 − Complex.log v))`
when `T.eval = v ≠ 0`. This equals `Complex.log v` provided the inner
`Complex.log_exp` lemma fires:

```
Complex.log_exp : -π < z.im → z.im ≤ π → Complex.log (Complex.exp z) = z
```

Here `z = Complex.exp 1 − Complex.log v`, so `z.im = − Complex.arg v`.
The constraint `-π < z.im` (strict) becomes `Complex.arg v < π`. **Strict.**

For real-negative `v`, `Complex.arg v = π` exactly, so the closure
lemma doesn't fire — even though `mkLogℂ T` does evaluate (everything is
total in Mathlib).

## Our finding: `mkLogℂ T = Complex.log v − 2πi` at the boundary

When `Complex.arg v = π` (real-negative `v`), `z.im = −π` and
`Complex.log_exp` gives `z + 2πi` (not `z`), because the principal-branch
`log(exp w)` for `w.im = −π` returns `w + 2πi` (jumping to the upper
boundary `arg = π`). Tracking through:

```
mkLogℂ T = exp 1 − log(exp(exp 1 − log v))
         = exp 1 − ((exp 1 − log v) + 2πi)        [at arg v = π]
         = log v − 2πi
```

So at the boundary, **the macro evaluates to `Complex.log v − 2πi`**,
which is the value of log on the next Riemann sheet down.

**Consequence.** Witnesses whose final operation is `mkExpℂ` absorb
this `−2πi` shift via `Complex.exp_periodic`. That's why `cosTermℂ =
mkExpℂ (mkExpℂ (...))` already covers `ℝ ∖ {0}` — the inner `−2πi`
shifts cancel through both outer `exp`s.

`sinTermℂ`, `arctanTermℂ`, `tanCoreTermℂ` do NOT have `mkExpℂ` outermost;
they expose the imaginary part of a final `mkLogℂ` (or `mkDivℂ` for tan).
A `−2πi` shift in their final `mkLogℂ` makes the answer differ from
`Real.sin x` by `−2π` in the imaginary part — observable, wrong.

## Witness shapes (the things we'd extend)

```lean
-- arctan: outer is mkLogℂ, .im = arctan x
def arctanTermℂ : EMLTermℂ :=
  mkLogℂ (mkAddℂ .one (mkMulℂ iTermℂ (.var 0)))
-- works for x ∈ (0, π); narrowness comes from mkMulℂ's arg constraint

-- sin: nested via cos(π/2 − x) identity, outer is mkLogℂ etc.
-- works for x ∈ (0, π); companion sinTermℂ_neg via sin x = cos(π/2 − x) algebra
-- and log(−i) = −iπ/2 covers (−π, 0)

-- tan: Cayley quotient, outer is mkDivℂ
def tanCoreTermℂ : EMLTermℂ :=
  let twoX := mkMulℂ twoPubℂ (.var 0)
  let I2x  := mkMulℂ iTermPubℂ twoX
  let E2   := mkExpℂ I2x
  mkDivℂ (mkSubℂ E2 .one) (mkAddℂ .one E2)
-- Pro's own recommendation; (eval).im = tan x for x ∈ (0, π/2)
```

The narrowness pattern repeats: the inner `mkMulℂ` requires `arg(var 0) < π`
(strict), which fails on the negative real ray.

---

## Three candidate paths

### Path A — Boundary lemmas + `2πi` shift tracking

Prove a parallel set of "at-boundary" eval lemmas:

```lean
lemma eval?_mkLogℂ_at_pi (hT : T.eval? env = some v) (hv : v ≠ 0)
    (harg : Complex.arg v = Real.pi) :
    (mkLogℂ T).eval? env = some (Complex.log v - 2 * Real.pi * Complex.I)
```

Then for each composite (`mkMulℂ`, `mkAddℂ`, `mkSubℂ`, `mkDivℂ`), prove
"at-boundary" variants that track `2πi` shifts symbolically. Re-prove
each trig witness's eval lemma in the boundary case, propagating the
shift, and show that for `sinTermℂ`, `arctanTermℂ`, `tanCoreTermℂ` the
shift either cancels or contributes a known offset.

**Pros.** Stays in the existing single-witness-per-primitive framing.
Follows the paper's "manual i-sign correction" narrative literally.
**Cons.** ~50–80 new lemmas. The boundary cases multiply combinatorially:
arg = π on `va` xor `vb` for binary builders, all four corners for
`mkMulℂ`/`mkDivℂ`, etc.

### Path B — Witness reshaping via Euler-form identities

For each narrow primitive, find an alternative algebraic form whose
witness has `mkExpℂ` outermost (the only operation that absorbs `2πi`
shifts).

For `tan`: already have Cayley quotient — outer is `mkDivℂ`, doesn't help.
For `sin`: `sin x = (e^{ix} − e^{−ix}) / (2i)` — outer would be `mkDivℂ`,
also doesn't help. `sin x = Im(e^{ix})` reduces to `cos`'s shape but
`Im` isn't an EML operation.

Maybe: rewrite `sinTermℂ = mkExpℂ (something)` such that the
"something" computes `log sin x + iπ/2` modulo `2πi`? That seems to
require `arcsin` machinery (which we'd then have to widen recursively —
chicken-and-egg).

**Question for you: is there a clean Euler-form witness for any of these
that has `mkExpℂ` outermost?** This would close the gap with no boundary
arithmetic.

### Path C — Multi-witness periodicity (foundation already built)

Witness becomes a *family* indexed by `k : ℤ`:

```lean
theorem sin_witness_family : ∀ x : ℝ, x ≠ 0 → x ≠ 2 * Real.pi → ... →
  ∃ t : EMLTermℂ, ∃ vc : ℂ,
    t.eval? (fun n => if n = 0 then ((x : ℝ) : ℂ) else 0) = some vc ∧
    vc.re = Real.sin x
```

Construction: pick `k = round(x / 2π)`, build a "shift-by-2πk" term
`s_k : EMLTermℂ` evaluating to `((x − 2πk : ℝ) : ℂ)`, then
`t := sinTermℂ.subst0 s_k`. Existing `sinTermℂ` covers `(−π, π) ∖ {0}`
which is exactly where `x − 2πk` lives.

Foundation already in place: `EML/Framework/Complex/Subst.lean` (~95
lines) defines `EMLTermℂ.subst0` and proves `eval?_subst0`:

```lean
lemma eval?_subst0 {env} {s : EMLTermℂ} {s_val : ℂ}
    (hs : s.eval? env = some s_val) (t : EMLTermℂ) :
    (t.subst0 s).eval? env = t.eval? (envShift0 s_val env)
```

Remaining work: construct `s_k` (real-fragment EL: `var 0 - 2π·k`,
lifted via `EMLTerm.toComplex`), apply Mathlib's `Real.sin_periodic`,
spec out `k = round(x/2π)`. Estimated 2–3 days of mechanical proof work.

**Pros.** Zero new architectural primitives; uses Mathlib periodicity
lemmas directly; fully constructive in Lean.
**Cons.** Witness depends on `x` (`∀x∃t` rather than `∃t∀x`). Slightly
less faithful to the paper's "one witness per primitive" framing.

---

## Specific sub-questions

1. **Which path do you recommend** for the cleanest Lean artefact:
   A (boundary lemmas), B (Euler-form reshaping if it exists), or C
   (multi-witness periodicity)? Why?

2. **Path B feasibility check.** Is there a known Euler-form identity
   for `sin x`, `arctan x`, or `tan x` whose witness can be expressed
   with `mkExpℂ` outermost in our grammar (`one`, `var`, `eml(a,b) =
   exp(a) − log(b)`)? Specifically:
   - Can we write `sin x = exp(F(x))` for some EML-expressible `F`
     that handles the `arg = π` boundary cleanly?
   - Same question for `tan x`. The Cayley quotient is `i·tan x =
     (e^{2ix} − 1)/(1 + e^{2ix})` — is there a single-`exp` form?
   - For `arctan x`: it's `(1/2i) · log((1+ix)/(1−ix))` — is there a
     non-log form expressible?

3. **Path A combinatorics.** If we go with A, what's the right
   abstraction for "log on the boundary"? Should we introduce a
   `LogResult` type with a `2πi`-shift count parameter, or is direct
   case analysis cleaner?

4. **Path C edge cases.** For C, the witness depends on `k`. For the
   "isolated points" `x = 2πk` (where `sin x = 0`) and `x = π/2 + πk`
   (where `tan x` is undefined), we'd state `paper_claim_sin_full :
   ∀ x ≠ kπ, ∃ t, ...`. Is there a cleaner formulation?

5. **Anything we missed.** Is there a fourth path we haven't considered?
   E.g., is there a Mathlib lemma family that handles
   "log on different branches via shift" cleanly for compositions like
   `Complex.log (exp z₁ * exp z₂) = z₁ + z₂ + 2πi · k(z₁, z₂)` that
   would give us composable boundary arithmetic for free?

6. **Paper-faithfulness.** The paper's compiler reportedly produces a
   *single* witness per primitive (compiles to one expression tree).
   Path C produces a witness *family*. Is this discrepancy
   philosophically meaningful, or are they observably equivalent
   (e.g., the paper's "single witness" actually inlines a `case` on
   `floor(x / 2π)` at run-time)?

## What we want as output

A markdown reply (≤ 3 pages) with:

1. **Headline recommendation** in one sentence.
2. **Why** that path beats the others, in 1–3 paragraphs.
3. **Concrete proof sketches** for the 2–3 hardest lemmas of the
   recommended path. Lean syntax preferred but pseudocode OK.
4. **What to skip** — if you think one of A/B/C is a dead end, say so
   plainly so we don't waste time.
5. **Open questions back to us** if any of our framings are wrong.

We trust your read on the architecture more than ours. Don't soft-pedal.
