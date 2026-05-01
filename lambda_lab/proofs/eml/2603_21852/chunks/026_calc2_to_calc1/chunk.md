# Calc 2 → Calc 1 reduction — 026_calc2_to_calc1

**Paper section**: §3 Results, Table 2 (rows 'Calc 2' and 'Calc 1')
**Difficulty**: 3/5
**Status**: pending

## Source quote
> From Calc 2 {exp, ln, −} we move to Calc 1 {e or π} ∪ {x^y, log_x(y)}.

## Informal (PL)
Krok przejścia od pary unarnych exp/ln + binarnego − do pary binarnych potęgowania i logarytmu_x razem ze stałą e (lub π). Wymaga tożsamości exp(x) = e^x i ln(x) = log_e(x).

## Informal (EN)
Move from a unary {exp, ln} + binary {−} to two binary primitives {x^y, log_x(y)} together with a constant e (or π). Uses exp(x) = e^x and ln(x) = log_e(x).

## Formal target

```lean
theorem calc2_subset_calc1 : True := by sorry
```

## Dependencies
(none)

## Aristotle status
pending (project_id: null)
