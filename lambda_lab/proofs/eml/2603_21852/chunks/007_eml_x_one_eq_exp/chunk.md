# eml(x,1) = exp(x) — 007_eml_x_one_eq_exp

**Paper section**: §3 Results, EML expression catalog
**Difficulty**: 1/5
**Status**: pending

## Source quote
> exp(x) = eml(x, 1)

## Informal (PL)
Drugi argument równy 1 sprowadza ln(1) do zera, więc eml(x,1) = exp(x) dla każdej liczby rzeczywistej x. To pokazuje, że funkcja wykładnicza jest natychmiast osiągalna w EML.

## Informal (EN)
Setting the second argument to 1 collapses ln(1) to zero, so eml(x,1) = exp(x) for every real x. This shows that the exponential is immediately reachable in EML.

## Formal target

```lean
theorem eml_x_one (x : ℝ) : eml x 1 = Real.exp x := by sorry
```

## Dependencies
001_def_eml

## Aristotle status
pending (project_id: null)
