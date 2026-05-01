# Subtraction expressed via EML — 013_sub_via_eml

**Paper section**: §3 Results, Calculator-equivalence chain
**Difficulty**: 2/5
**Status**: pending

## Source quote
> x − y = exp(ln x) − exp(ln y) (when x, y > 0); equivalently exp(ln x) − ln(exp y).

## Informal (PL)
Odejmowanie x − y można wyrazić przez EML poprzez eml(ln x, exp y) = exp(ln x) − ln(exp y) = x − y, dla x > 0 (bo wtedy ln(exp y)=y wymaga jedynie y rzeczywistego, a exp(ln x)=x wymaga x > 0).

## Informal (EN)
The subtraction x − y can be written as eml(ln x, exp y) = exp(ln x) − ln(exp y) = x − y when x > 0 (the ln(exp y) = y simplification needs no positivity, but exp(ln x) = x needs x > 0).

## Formal target

```lean
theorem sub_via_eml (x y : ℝ) (hx : 0 < x) : x - y = eml (Real.log x) (Real.exp y) := by sorry
```

## Dependencies
001_def_eml

## Aristotle status
pending (project_id: null)
