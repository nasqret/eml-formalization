# Negation realised in the Calc-3 set — 019_negation_in_calc3

**Paper section**: §3 Results, Table 2 row 'Calc 3'
**Difficulty**: 3/5
**Status**: pending

## Source quote
> −x is realised in Calc 3 (operators {+, exp, ln, −x, 1/x}) using only +, 1/x and the standalone −x primitive — but the bootstrap formula in Identity (suc/inv) shows the operation is derivable from + and 1/x alone.

## Informal (PL)
Pokazujemy, że negacja −x jest osiągalna używając tylko dodawania i odwrotności (zestaw Calc 3 minus sama −x): −x = 1/(1/(1/x+1)−1) + 1, dla x ≠ 0, x ≠ −1. Pozwala to wykluczyć −x z minimalnego zestawu (krok ku Calc 2/Calc 1).

## Informal (EN)
We show that negation −x is reachable using only addition and inversion (the Calc-3 operator set minus the standalone −x primitive): −x = 1/(1/(1/x+1)−1) + 1 for x ≠ 0, x ≠ −1. This is the step that removes −x as a primitive on the way to Calc 2/Calc 1.

## Formal target

```lean
theorem neg_via_calc3 (x : ℝ) (hx : x ≠ 0) (hx1 : x ≠ -1) : -x = 1 / (1 / (1 / x + 1) - 1) + 1 := by sorry
```

## Dependencies
017_successor_negation_identity

## Aristotle status
pending (project_id: null)
