import Mathlib

/-!
# §G full fix — extend boundary point witnesses to closed natural domains

The three §G structural boundary points (`√0`, `arcosh 1`, `hypot(0,0)`)
have ALREADY been shown correct in extended-real arithmetic:
`StructuralLimitsEReal.lean` proves the three template values match.

This chunk asks Aristotle to do the FULL fix: produce three new public
theorems

```
paper_claim_sqrt_full :
    ∃ t : EMLTerm, ∀ env : Nat → ℝ, 0 ≤ env 0 →
      t.eval? env = some (Real.sqrt (env 0))

paper_claim_arcosh_full :
    ∃ t : EMLTerm, ∀ env : Nat → ℝ, 1 ≤ env 0 →
      t.eval? env = some (Real.arccosh (env 0))

paper_claim_hypot_full :
    ∃ t : EMLTerm, ∀ env : Nat → ℝ,
      t.eval? env = some (Real.sqrt (env 0 ^ 2 + env 1 ^ 2))
```

These extend the existing narrow versions to include the boundary
points (env 0 = 0, env 0 = 1, (env 0, env 1) = (0, 0) respectively).

The fix requires either:
(a) A new builder layer `mkSqrtAll`, `mkArcoshAll`, `mkHypotAll` that
    handles the boundary case via a piecewise construction (e.g.,
    `sqrt(x²) = |x|` works for x = 0 too via `mkSqAll`); OR
(b) A multi-witness version where the witness depends on whether
    the env is at the boundary or not.

Approach (a) is preferred where it can be made to work without
inflating the K-count. For sqrt: `sqrt(x) = sqrt(x²)/sqrt(x²)·x`...
no that doesn't work. Try: `sqrt(x) = exp((1/2)·log x)` requires
x > 0; can we use `sqrt(x²) = |x|` instead and then... hmm.

The cleanest may be to use the EReal templates we already have
(`sqrt_templateE_at_zero` etc.) as the witness "value" via a
homomorphism from EReal back to ℝ when the value is finite.

Aristotle is asked to find the right construction for each of the
three primitives.
-/

example : True := trivial
