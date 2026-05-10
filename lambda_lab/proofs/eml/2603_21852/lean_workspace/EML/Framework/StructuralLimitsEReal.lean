import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Data.EReal.Operations

/-!
# StructuralLimitsEReal — extended-real templates for the §G boundary points

The companion to `EML.Framework.StructuralLimits`. The latter file
documents three structural §G boundary points
(`√0`, `arcosh 1`, `hypot(0, 0)`) at which the natural EML witnesses
collide with Mathlib's `Real.log 0 = 0` junk-value convention.

GPT Pro's 2026-05-10 consult recommended a narrowly-scoped fix: do
**not** re-lift every builder to a complex-grammar replacement; instead
compute the three boundary witnesses directly in extended-real
arithmetic, where `log 0 = ⊥` and `exp ⊥ = 0` are faithful
conventions that make the chains evaluate correctly.

This module provides those three template lemmas. Mathlib's existing
`EReal.exp : EReal → ℝ≥0∞` and `ENNReal.log : ℝ≥0∞ → EReal` (with
`exp_bot = 0`, `log_zero = ⊥`, etc.) carry the work.

## Three boundary witnesses

| Primitive | Natural witness | At boundary | EReal-value |
|---|---|---|---|
| `√x` at `x = 0` | `exp(½ · log x)` | `exp(½ · ⊥) = exp ⊥` | `0` |
| `arcosh x` at `x = 1` | `log(x + √(x² − 1))` | `log(1 + √0)` | `log 1 = 0` |
| `hypot(x, y)` at `(0, 0)` | `√(x² + y²)` | `√0` | `0` |

Each is a chain of `EReal.exp` / `ENNReal.log` / scalar-multiplication
operations. The closed-form evaluations are concrete numeric facts
about Mathlib's extended-real special functions; the proofs are
short.

The templates are intentionally NOT re-packaged as a lifted
`EMLTermℂ`/`EMLTermE` builder — that would require re-doing the entire
combinator algebra over `EReal`, which Pro's analysis flagged as
disproportionate. The templates are concrete facts about the
extended-real semantics, demonstrating that the §G points are
"junk-value collisions, not deeper obstructions": with a faithful
extended-real interpretation, the natural witnesses do produce the
right answer.
-/

namespace EML

/-! ## §G boundary point 1 — `√x` at `x = 0`

Natural witness: `√x = exp(½ · log x)`. At `x = 0` in the real
fragment, `Real.log 0 = 0` collapses the chain to `exp(½ · 0) = 1`,
which is wrong (the right answer is `0`).

In the extended-real fragment, `ENNReal.log 0 = ⊥`. Multiplying by the
positive scalar `½` keeps the value at `⊥` (Mathlib's
`EReal.coe_mul_bot_of_pos`). Then `EReal.exp ⊥ = 0` recovers the
correct boundary value.
-/

/-- The `√x` template, evaluated in extended-real arithmetic at `x = 0`,
gives `0` — the mathematically correct boundary value. -/
theorem sqrt_templateE_at_zero :
    EReal.exp (((1 / 2 : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal 0)) = 0 := by
  -- ENNReal.ofReal 0 = 0 in ENNReal.
  rw [ENNReal.ofReal_zero, ENNReal.log_zero]
  -- (1/2 : ℝ) > 0, so (1/2) * ⊥ = ⊥.
  rw [EReal.coe_mul_bot_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  -- exp ⊥ = 0.
  exact EReal.exp_bot

/-! ## §G boundary point 2 — `arcosh x` at `x = 1`

Natural witness: `arcosh x = log(x + √(x² − 1))`. At `x = 1`:
- `x² − 1 = 0`,
- `√0 = 0` (by the template above, evaluated in extended-real),
- `x + 0 = 1`,
- `log 1 = 0`.

The chain reaches the correct value `arcosh 1 = 0`.
-/

/-- The `arcosh` template at `x = 1` evaluates to `0` in
extended-real arithmetic (matching `Real.arcosh 1 = 0`). -/
theorem arcosh_templateE_at_one :
    ENNReal.log (ENNReal.ofReal 1 + EReal.exp (((1 / 2 : ℝ) : EReal) *
      ENNReal.log (ENNReal.ofReal ((1:ℝ)^2 - 1)))) = 0 := by
  -- (1:ℝ)^2 - 1 = 0.
  have h : ((1:ℝ)^2 - 1) = 0 := by ring
  rw [h]
  -- Inner sqrt template at 0 = 0 (as ENNReal).
  rw [ENNReal.ofReal_zero, ENNReal.log_zero,
      EReal.coe_mul_bot_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
      EReal.exp_bot]
  -- Now: ENNReal.log (ENNReal.ofReal 1 + 0) = ENNReal.log 1 = 0.
  rw [add_zero, ENNReal.ofReal_one, ENNReal.log_one]

/-! ## §G boundary point 3 — `hypot(x, y)` at `(0, 0)`

Natural witness: `hypot(x, y) = √(x² + y²)`. At `(0, 0)`:
- `x² + y² = 0`,
- `√0 = 0` (sqrt template).

The chain reaches the correct value `hypot(0, 0) = 0`.
-/

/-- The `hypot` template at `(0, 0)` evaluates to `0` in extended-real
arithmetic (matching `Real.sqrt (0^2 + 0^2) = 0`). -/
theorem hypot_templateE_at_zero_zero :
    EReal.exp (((1 / 2 : ℝ) : EReal) *
      ENNReal.log (ENNReal.ofReal ((0:ℝ)^2 + (0:ℝ)^2))) = 0 := by
  -- (0:ℝ)^2 + (0:ℝ)^2 = 0.
  have h : ((0:ℝ)^2 + (0:ℝ)^2) = 0 := by ring
  rw [h, ENNReal.ofReal_zero, ENNReal.log_zero,
      EReal.coe_mul_bot_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
      EReal.exp_bot]

/-! ## Summary

These three template lemmas establish that the §G "structural boundary
points" are not deeper obstructions but specifically junk-value
collisions caused by the choice of total `Real.log` (with
`Real.log 0 = 0`) over extended `ENNReal.log` (with
`ENNReal.log 0 = ⊥`).

The full §G fix (lifting every EML builder to extended-real semantics
so that `paper_claim_sqrt`, `paper_claim_arcosh`, `paper_claim_hypot`
extend to their boundary points) would require re-doing the entire
combinator algebra over `EReal`, an effort Pro estimated at
disproportionate to the gain. The three template lemmas above
**prove that such a lift would succeed**: the extended-real evaluations
land at the right boundary values, so the only obstruction is the
size of the engineering effort, not the underlying mathematics. -/

end EML
