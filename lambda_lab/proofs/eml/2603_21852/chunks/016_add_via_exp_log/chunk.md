# Additive consequence: x + y via exp and ln (specialized) — 016_add_via_exp_log

**Paper section**: §3 Results, Identity 1 (specialised consequence)
**Difficulty**: 2/5
**Status**: pending

## Source quote
> x + y = ln(exp(x) · exp(y))

## Informal (PL)
Wariant chunka 014 z bezpośrednim odwołaniem do dwukrotnego użycia exp/ln; rozłączenie z 014 ma sens, jeśli Aristotle proponuje różne ścieżki dowodowe (np. log_mul + log_exp_self vs Real.log_exp_mul_exp).

## Informal (EN)
A re-statement of chunk 014 split out so that Aristotle can use either (log_mul + log_exp) or a direct combined lemma. Useful for the calculator-equivalence chain in Group 6.

## Formal target

```lean
theorem add_eq_log_mul_exp (x y : ℝ) : x + y = Real.log (Real.exp x) + Real.log (Real.exp y) := by sorry
```

## Dependencies
(none)

## Aristotle status
pending (project_id: null)
