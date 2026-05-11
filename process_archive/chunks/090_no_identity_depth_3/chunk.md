# Chunk 090 — No identity term at depth 3

## Target

Prove that no `EMLTerm` of depth exactly 3 evaluates to the identity function on every real environment. This continues the SI §1.5 #5 closure work (depth 1 and depth 2 already sealed in `EML/Framework/TransplantDepths.lean`).

## Statement

```lean
theorem no_identity_at_depth_three :
    ¬ ∃ t : EMLTerm, t.depth = 3 ∧
      ∀ env : Nat → ℝ, t.eval? env = some (env 0)
```

## Proof strategy

Same all-ones-environment trick as for depths 1 and 2. A depth-3 term is `eml a b` with `max(a.depth, b.depth) = 2`. Six subcases:

| `(a.depth, b.depth)` | Subterm-eval on env=ones |
|---|---|
| `(0, 2)` | `1, β` where `β ∈ {e-1, exp(e), exp(e)-1}` |
| `(1, 2)` | `e, β` where `β ∈ {e-1, exp(e), exp(e)-1}` |
| `(2, 0)` | `α, 1` where `α ∈ {e-1, exp(e), exp(e)-1}` |
| `(2, 1)` | `α, e` where `α ∈ {e-1, exp(e), exp(e)-1}` |
| `(2, 2)` | both at depth 2 |

The depth-2 children's eval on env=ones are tracked by the existing `eval_one_of_depth_two` helper (to be added if not already present, or defined locally here as a Finset).

Each combination produces a specific real value of the form `exp(α) - log(β)`. We need to show none equals 1. Sufficient bounds:

- `Real.exp 1 > 2` (from `Real.add_one_lt_exp one_ne_zero`)
- `Real.exp (Real.exp 1) > Real.exp 1 + 1 > 3`
- `Real.log (Real.exp x - 1) < x` for `x > 0` (since `exp x - 1 < exp x` and `log` monotone)
- Each candidate value of the form `exp(α) - log(β)` with α, β positive and ≥ 1 is ≠ 1: case analysis discharged by `linarith` / `nlinarith` after the right inequality lemmas.

## Pre-existing API

`EML.EMLTerm.eval_one_of_depth_zero` (helper, returns `some 1`)
`EML.EMLTerm.eval_one_of_depth_one` (helper, returns `some (Real.exp 1)`)

A new helper `eval_one_of_depth_two` would package the three depth-2 values into a disjunction. Aristotle is invited to either:
1. Prove it directly with the disjunction case-split, or
2. Add a finer per-shape helper that tracks the exact tree shape.

Either route closes the depth-3 case.

## Status

Chunk created 2026-05-10. Submitted to Aristotle.
