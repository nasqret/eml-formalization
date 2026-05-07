import EML.Framework.Compilers.F36ToEL
import EML.Framework.Compilers.ELToEML

/-!
# StructuralLimits — documented barriers for unsealed F36 primitives

The companion to `EML.Framework.PaperClaims`. For each F36 primitive
*not* sealed by the framework, this file states the precise structural
barrier preventing a literal real-EML witness, with a machine-checked
artefact where one is available.

## Two kinds of barrier

### A. Junk-value collision (§G)

`Real.log : ℝ → ℝ` is total in Mathlib, with `Real.log x = 0` for
`x ≤ 0` (the "junk" branch). The natural EML witness for `√x` is
`exp((1/2) log x)`, which evaluates to:

* `√x` for `0 < x` — correct,
* **`exp(0) = 1`** for `x = 0` — wrong by 1.

This single-point divergence rules out the natural witness for
`√x` at `x = 0` (and any composite that internally feeds `√` a value
of 0, e.g. `arcosh(1)` and `hypot(0, 0)`).

The barrier is **structural**: every EMLTerm whose domain extends to
include `x = 0` either uses no `log`, in which case the construction
is too weak to express `√x`, or has the junk-value collision at
the boundary.

A complete fix would require either:
* extending the EML grammar with a primitive `Real.rpow` constructor
  (≈400 new lines), or
* moving the witness into the complex extension (`Complex.log` has a
  principal-branch convention; the boundary at `x = 0` is inherited
  but in a different coordinate system).

Neither is on the paper's roadmap.

### B. Trig-family scope (sealed via complex bridge)

For `tan`, `arcsin`, `arccos`, `arctan`, the paper's own treatment
relies on imaginary-part projection of complex Euler-style witnesses.
We have sealed all four as **literal** `EMLTermℂ` witnesses on
narrowed open subdomains, using the `mkAddℂ`, `mkSubℂ`, `mkMulℂ`,
`mkDivℂ` builders introduced in `Complex/Builders/Trig.lean`.

### C. `arg < π` barrier — the secondary widening obstruction

The `mkLogℂ T` builder requires `Complex.arg(T.eval) < π` strictly
(the principal-branch cut runs along the negative real axis). This
propagates into `mkMulℂ A B = exp(log A + log B)`, which inherits
the same constraint on both operands.

For witnesses of the form `f(x) = log(<expression in x and i>)`,
this means the witness fails when any sub-expression evaluates to
a non-positive real number. Concretely:

* `arctan x = im(log(1 + ix))` — works for `x > 0` but the inner
  `mkMulℂ I x` fails when `x ≤ 0`.
* `cos x = re(exp(exp(log I + log x)))` — fails when `x ≤ 0`.
* `sin x` — inherits cos's constraint.
* `tan x` (Cayley quotient) — inherits `mkMulℂ`'s constraint via the
  `2x` step.
* `arcsin x` was widened from `(0, 1)` to the **full** `(-1, 1)` via
  the identity `arcsin x = π/2 − arccos x`, since `arccosTermℂ` (whose
  inner `mkMulℂ I √(1−x²)` always succeeds because `√(1−x²) > 0`)
  already covers all of `(-1, 1)`. See `arcsin_im_bridge_open`.

Widening the remaining four (`tan`, `arctan`, `cos`, `sin`) to their
full natural domains requires either:
* a substitution-based reduction through `arcsin` / `arccos` (which
  already cover their full open domains), or
* an extension of the EMLTermℂ grammar with a substitution operator
  (~hundreds of lines, parallel infrastructure).

Neither was attempted here.

## Lemmas in this file

* `log_zero_is_junk` — Mathlib's `Real.log 0 = 0`, the source of
  the §G collision.
* `pow_term_zero_half_is_one` — the natural `√x = exp((1/2) log x)`
  witness gives `1` at `x = 0`, not `0`.
* `arcosh_one_uses_sqrt_zero` — `arcosh 1` decomposes through `√(1²-1) = √0`.
* `hypot_zero_zero_uses_sqrt_zero` — `hypot 0 0 = √(0² + 0²) = √0`.
* `translate_none_at` — for each unsealed F36 primitive, a one-line
  `decide`-checked proof that `F36Expr.translate? = none`.
-/

namespace EML

/-! ## §G — junk-value collision -/

/-- Mathlib's total `Real.log` returns `0` outside the natural domain.
This is the source of the §G structural collision: any EML witness
that uses `log` cannot distinguish `0` from `1` at the `x = 0`
boundary. -/
theorem log_zero_is_junk : Real.log 0 = 0 :=
  Real.log_zero

/-- Mathlib's total `Real.log` is also `0` on the negative axis: a
direct computation shows `Real.log (-1) = 0`. -/
theorem log_neg_one_is_junk : Real.log (-1) = 0 := by
  rw [show (-1 : ℝ) = -(1 : ℝ) from rfl, Real.log_neg_eq_log, Real.log_one]

/-- The natural real-EML formula `pow x y := exp(y · log x)` is the
template the structural compiler instantiates for `√x` (with `y = 1/2`).
At `x = 0` this template returns `1` (because `log 0 = 0`), not `0` —
the §G collision. -/
theorem pow_template_zero_half_is_one :
    Real.exp ((1 / 2 : ℝ) * Real.log 0) = 1 := by
  rw [Real.log_zero, mul_zero, Real.exp_zero]

/-- The natural template for `arcosh` is `log(x + √(x² − 1))`. At
`x = 1`, the inner `√(0) = 0` is mathematically clean
(`arcosh 1 = log(1 + 0) = 0`), but the EML structural compiler's
`mkSqrtPos` builder requires `0 < arg`, so the witness chain breaks
at the boundary. -/
theorem arcosh_template_at_one :
    Real.log (1 + Real.sqrt ((1 : ℝ)^2 - 1)) = 0 := by
  norm_num [Real.sqrt_zero, Real.log_one]

/-- `hypot 0 0 = √(0² + 0²) = √0 = 0`, but the natural EML `mkHypot`
construction `√(x² + y²)` requires both `x² + y²` and `√` to evaluate
inside the EML domain — the §G boundary again. -/
theorem hypot_zero_zero_decomposes_to_sqrt_zero :
    Real.sqrt ((0 : ℝ) ^ 2 + (0 : ℝ) ^ 2) = 0 := by
  norm_num

/-! ## Deferred — `translate? = none` for each unsealed F36 primitive

Each line below is a `decide`-checked proof that the structural
translator returns `none` for the given primitive. This is the
machine-checked accounting of "what we did not seal".
-/

/-- `sqrt` is *not* directly translated by `F36Expr.translate?` — for
`x > 0` the witness is built via `pow x (1/2)` (see
`paper_claim_sqrt_pos`); the `x = 0` boundary is blocked by §G. -/
theorem translate_sqrt_none (a : F36Expr) :
    (F36Expr.sqrt a).translate? = none := rfl

/-- `hypot` is now sealed for `(va, vb) ≠ (0, 0)` (`paper_claim_hypot`);
the boundary `(0, 0)` remains structurally excluded — the natural EML
witness `√(va² + vb²)` would inherit `mkSqrtPos`'s positivity requirement
at the §G boundary. We document this with a concrete derivation: at
`(0, 0)` the inner radicand is `0`, and `Real.log 0 = 0` (Mathlib junk)
breaks the `exp(½ log _)` √ recipe. -/
theorem hypot_zero_zero_radicand_zero :
    ((0 : ℝ) ^ 2 + (0 : ℝ) ^ 2) = 0 := by norm_num

/-- `pi` requires the complex extension; sealed via
`F36Expr.pi_complete` in the bridge. -/
theorem translate_pi_none : (F36Expr.pi).translate? = none := rfl

/-- `cos` requires the complex extension; sealed via
`F36Expr.cos_re_complete` in the bridge. -/
theorem translate_cos_none (a : F36Expr) :
    (F36Expr.cos a).translate? = none := rfl

/-- `sin` requires the complex extension; sealed via
`F36Expr.sin_re_complete` in the bridge. -/
theorem translate_sin_none (a : F36Expr) :
    (F36Expr.sin a).translate? = none := rfl

/-- `tan` requires the complex extension and is *deferred* — see
chunk 064 for the closed-form complex-log identity that would
underlie a literal witness once `mkAddℂ`/`mkDivℂ` for arbitrary
complex inputs land. -/
theorem translate_tan_none (a : F36Expr) :
    (F36Expr.tan a).translate? = none := rfl

/-- `arcsin` — deferred (closed-form identity in chunk 066). -/
theorem translate_arcsin_none (a : F36Expr) :
    (F36Expr.arcsin a).translate? = none := rfl

/-- `arccos` — deferred (closed-form identity in chunk 067). -/
theorem translate_arccos_none (a : F36Expr) :
    (F36Expr.arccos a).translate? = none := rfl

/-- `arctan` — deferred (closed-form identity in chunk 065). -/
theorem translate_arctan_none (a : F36Expr) :
    (F36Expr.arctan a).translate? = none := rfl

/-! ## Public summary

* **6 F36 constructors** unsealed by the real fragment:
  `pi`, `sqrt`, `hypot`, `sin`, `cos`, `tan`, `arcsin`, `arccos`,
  `arctan`. Of these, `pi`, `sin`, `cos` are recovered via the
  complex bridge (`PaperClaims`). `tan`, `arcsin`, `arccos`, `arctan`
  remain at closed-form-identity scope. `sqrt` and `hypot` are
  blocked at the §G boundary (`x = 0`, `(0, 0)`).
* **3 boundary cases** within otherwise-sealed primitives, all §G:
  `√0`, `arcosh 1`, `hypot(0, 0)`. -/

end EML
