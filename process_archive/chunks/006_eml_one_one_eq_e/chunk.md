# eml(1,1) = e — 006_eml_one_one_eq_e

**Paper section**: §3 Results, EML expression catalog
**Difficulty**: 1/5
**Status**: pending

## Source quote
> e = eml(1, 1)

## Informal (PL)
Wartość operatora EML dla obu argumentów równych 1 daje liczbę e: eml(1,1) = exp(1) − ln(1) = e − 0 = e. Najprostszy z fundamentalnych przykładów.

## Informal (EN)
Applying the EML operator to two unit arguments yields Euler's number: eml(1,1) = exp(1) − ln(1) = e − 0 = e. The simplest of the fundamental examples.

## Formal target

```lean
theorem eml_one_one : eml 1 1 = Real.exp 1 := by sorry
```

## Dependencies
001_def_eml

## Aristotle status
pending (project_id: null)
