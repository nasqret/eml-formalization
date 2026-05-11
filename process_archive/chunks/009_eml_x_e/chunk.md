# eml(x, e) = exp(x) − 1 — 009_eml_x_e

**Paper section**: §3 Results (consequence of Equation 3)
**Difficulty**: 1/5
**Status**: pending

## Source quote
> eml(x, e) = exp(x) − ln(e) = exp(x) − 1

## Informal (PL)
Podstawienie y = e daje ln(e) = 1, więc eml(x,e) = exp(x) − 1. Wartość 'exp(x) − 1' pojawia się w wielu rozwinięciach (np. szereg Taylora), więc warto mieć ją jako wyodrębniony lemat.

## Informal (EN)
Substituting y = e yields ln(e) = 1, so eml(x,e) = exp(x) − 1. The value exp(x) − 1 appears throughout analysis (Taylor expansions, etc.) so it is worth isolating.

## Formal target

```lean
theorem eml_x_e (x : ℝ) : eml x (Real.exp 1) = Real.exp x - 1 := by sorry
```

## Dependencies
001_def_eml

## Aristotle status
pending (project_id: null)
