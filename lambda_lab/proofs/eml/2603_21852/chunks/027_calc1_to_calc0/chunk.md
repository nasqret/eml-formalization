# Calc 1 → Calc 0 reduction — 027_calc1_to_calc0

**Paper section**: §3 Results, Table 2 (rows 'Calc 1' and 'Calc 0')
**Difficulty**: 3/5
**Status**: pending

## Source quote
> From Calc 1 {e, x^y, log_x(y)} we drop the constant and replace x^y with exp(x), reaching Calc 0 {exp, log_x(y)} (3 symbols).

## Informal (PL)
Pomocniczy krok: zastępujemy x^y przez exp(y · ln x), używając exp jako jedynej operacji unarnej, i odzyskujemy stałą e jako exp(1). Wymaga binarnego log_x(y) i unarnego exp.

## Informal (EN)
Substitute x^y by exp(y · ln x), keeping exp as the only unary, and recover e as exp(1). Requires the binary log_x(y) and the unary exp.

## Formal target

```lean
theorem calc1_subset_calc0 : True := by sorry
```

## Dependencies
(none)

## Aristotle status
pending (project_id: null)
