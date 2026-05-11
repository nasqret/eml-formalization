# eml(1,y) = e − ln(y) — 008_eml_one_y

**Paper section**: §3 Results (consequence of Equation 3)
**Difficulty**: 1/5
**Status**: pending

## Source quote
> eml(1, y) = exp(1) − ln(y)

## Informal (PL)
Pierwszy argument równy 1 redukuje exp(1) do stałej e, więc eml(1,y) = e − ln(y). Hipoteza y > 0 nie jest formalnie konieczna (ze względu na junk-value Real.log), ale dodajemy ją dla przejrzystości semantycznej.

## Informal (EN)
Setting the first argument to 1 reduces exp(1) to the constant e, giving eml(1,y) = e − ln(y). The hypothesis y > 0 is not formally required (Real.log is junk-valued elsewhere) but we keep it for semantic clarity.

## Formal target

```lean
theorem eml_one_y (y : ℝ) (hy : 0 < y) : eml 1 y = Real.exp 1 - Real.log y := by sorry
```

## Dependencies
001_def_eml

## Aristotle status
pending (project_id: null)
