# Algebraic simplification of inv(suc(inv x)) — 018_inv_successor_inv_inverse_simple

**Paper section**: §3 Results (sub-step of successor identity)
**Difficulty**: 1/5
**Status**: pending

## Source quote
> 1/(1/x + 1) = x / (1 + x)

## Informal (PL)
Pomocniczy lemat algebraiczny: 1/(1/x + 1) = x/(1+x), dla x ≠ 0 i 1+x ≠ 0. Wykorzystywany jako krok pośredni w 017 i 019.

## Informal (EN)
Auxiliary algebraic lemma: 1/(1/x + 1) = x/(1+x) for x ≠ 0 and 1+x ≠ 0. Used as an intermediate step in 017 and 019.

## Formal target

```lean
theorem inv_successor_inv (x : ℝ) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) : 1 / (1 / x + 1) = x / (1 + x) := by sorry
```

## Dependencies
(none)

## Aristotle status
pending (project_id: null)
