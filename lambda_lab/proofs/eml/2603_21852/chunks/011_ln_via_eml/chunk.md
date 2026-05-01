# Natural logarithm via EML — 011_ln_via_eml

**Paper section**: §3 Results, Identity 5
**Difficulty**: 3/5
**Status**: pending

## Source quote
> ln(z) = eml(1, eml(eml(1, z), 1))

## Informal (PL)
Logarytm naturalny daje się wyrazić zagnieżdżeniem trzech operatorów EML: ln(z) = eml(1, eml(eml(1, z), 1)). Dowód polega na rozwijaniu definicji EML i użyciu Real.log_one, Real.log_exp oraz arytmetyki rzeczywistej. Dla z > 0 wszystkie wewnętrzne argumenty Real.log są dodatnie.

## Informal (EN)
The natural log expands as a triple-nested EML application: ln(z) = eml(1, eml(eml(1, z), 1)). The proof unfolds eml repeatedly and uses Real.log_one, Real.log_exp plus arithmetic. For z > 0 all the inner Real.log arguments are positive.

## Formal target

```lean
theorem ln_via_eml (z : ℝ) (hz : 0 < z) : Real.log z = eml 1 (eml (eml 1 z) 1) := by sorry
```

## Dependencies
001_def_eml

## Aristotle status
pending (project_id: null)
