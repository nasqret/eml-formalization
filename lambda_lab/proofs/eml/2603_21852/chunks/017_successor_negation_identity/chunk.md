# Successor / negation identity — 017_successor_negation_identity

**Paper section**: §3 Results (passing remark)
**Difficulty**: 2/5
**Status**: pending

## Source quote
> suc(inv(pre(inv(suc(inv(x)))))) = 1/(1/(1/x + 1) − 1) + 1 = −x

## Informal (PL)
Tożsamość: 1/(1/(1/x + 1) − 1) + 1 = −x. Pojedynczy `field_simp; ring` powinien zamknąć cel; konieczne hipotezy x ≠ 0, 1/x + 1 ≠ 0, 1/(1/x + 1) − 1 ≠ 0 (czyli x ≠ 0, x ≠ −1).

## Informal (EN)
Identity: 1/(1/(1/x + 1) − 1) + 1 = −x. A single `field_simp; ring` should close it; the side conditions are x ≠ 0 and x ≠ −1 to keep all denominators alive.

## Formal target

```lean
theorem successor_negation_identity (x : ℝ) (hx : x ≠ 0) (hx1 : x ≠ -1) : 1 / (1 / (1 / x + 1) - 1) + 1 = -x := by sorry
```

## Dependencies
(none)

## Aristotle status
pending (project_id: null)
