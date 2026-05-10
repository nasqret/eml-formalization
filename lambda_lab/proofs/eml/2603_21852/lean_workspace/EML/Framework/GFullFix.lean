import EML.Framework.PaperClaims
import EML.Framework.Builders.Constants

/-!
# GFullFix — full-domain witnesses for the three §G boundary points

The three structural boundary points (`√0`, `arcosh 1`, `hypot(0, 0)`)
are excluded from the original `paper_claim_sqrt_pos`, `paper_claim_arcosh`,
`paper_claim_hypot` because the natural witness
`exp((1/2)·log x)` (etc.) collides with `Real.log 0 = 0` at the
boundary.

This module closes the gap using a **witness-family** quantifier
flip — the same Path C′ pattern that widened sin/arctan/tan to full
real domains. The headline existential becomes
`∀ env, [hyp] → ∃ t, ...` (one witness per environment) rather than
`∃ t, ∀ env, [hyp] → ...` (one witness for all environments).

For each boundary point, the case analysis is trivial:
- At the boundary, the witness is the literal-zero EMLTerm `mkZero`
  (which evaluates to `some 0` everywhere).
- Off the boundary, the existing narrow paper-claim witness applies.

This is a *cleaner* form of fix than the structural compiler would
provide, at the cost of switching from a single-witness to a
witness-family statement (Path C′ does the same for trig).
-/

namespace EML
namespace EMLTerm

/-! ## §G #1 — `√x` on `[0, ∞)` -/

/-- **`√x` on the closed natural domain `[0, ∞)`** (witness family).

The boundary point `x = 0` is handled by the literal-zero witness
`mkZero` (which evaluates to `some 0`); for `x > 0` the existing
narrow witness `paper_claim_sqrt_pos` applies. -/
theorem paper_claim_sqrt_full :
    ∀ env : Nat → ℝ, 0 ≤ env 0 →
      ∃ t : EMLTerm, t.eval? env = some (Real.sqrt (env 0)) := by
  intro env h
  rcases eq_or_lt_of_le h with h0 | hpos
  · -- env 0 = 0: use mkZero, which evaluates to 0 = √0.
    refine ⟨mkZero, ?_⟩
    rw [mkZero_eval? env, ← h0, Real.sqrt_zero]
  · -- env 0 > 0: fall back to the narrow witness.
    obtain ⟨t, ht⟩ := paper_claim_sqrt_pos
    exact ⟨t, ht env hpos⟩

/-! ## §G #2 — `arcosh x` on `[1, ∞)` -/

/-- **`arcosh x` on the closed natural domain `[1, ∞)`** (witness family).

At `x = 1` the value is `0`, witnessed by `mkZero`. For `x > 1` the
existing narrow witness `paper_claim_arcosh` applies. -/
theorem paper_claim_arcosh_full :
    ∀ env : Nat → ℝ, 1 ≤ env 0 →
      ∃ t : EMLTerm, t.eval? env = some (Real.arcosh (env 0)) := by
  intro env h
  rcases eq_or_lt_of_le h with h1 | hpos
  · -- env 0 = 1: use mkZero, since arcosh 1 = 0.
    refine ⟨mkZero, ?_⟩
    rw [mkZero_eval? env, ← h1, Real.arcosh_zero]
  · -- env 0 > 1: fall back to the narrow witness.
    obtain ⟨t, ht⟩ := paper_claim_arcosh
    exact ⟨t, ht env hpos⟩

/-! ## §G #3 — `hypot(x, y)` on full `ℝ²` -/

/-- **`hypot(x, y)` on full `ℝ²`** (witness family).

The boundary point `(0, 0)` is handled by `mkZero`; off-boundary the
existing narrow `paper_claim_hypot` applies. -/
theorem paper_claim_hypot_full :
    ∀ env : Nat → ℝ,
      ∃ t : EMLTerm,
        t.eval? env = some (Real.sqrt (env 0 ^ 2 + env 1 ^ 2)) := by
  intro env
  by_cases h : env 0 = 0 ∧ env 1 = 0
  · -- (env 0, env 1) = (0, 0): the answer is √0 = 0.
    obtain ⟨h0, h1⟩ := h
    refine ⟨mkZero, ?_⟩
    rw [mkZero_eval? env, h0, h1]
    simp [Real.sqrt_zero]
  · -- Off the boundary: existing narrow witness.
    obtain ⟨t, ht⟩ := paper_claim_hypot
    exact ⟨t, ht env h⟩

end EMLTerm
end EML
