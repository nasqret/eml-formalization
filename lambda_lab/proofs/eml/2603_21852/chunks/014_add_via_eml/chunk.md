# Addition via Identity 1 (Exp-Log reduction) — 014_add_via_eml

**Paper section**: §3 Results, Identity 1
**Difficulty**: 2/5
**Status**: pending

## Source quote
> x + y = ln(exp(x) × exp(y))

## Informal (PL)
Dodawanie wynika z mnożenia funkcji exp przez homomorfizm ln: x + y = ln(exp x · exp y). Kanoniczna tożsamość transcendentalna; w Mathlib jest to Real.log_exp_mul_exp lub kombinacja Real.log_mul + Real.log_exp.

## Informal (EN)
Addition arises from the exp homomorphism: x + y = ln(exp x · exp y). A canonical transcendental identity; in Mathlib it follows from Real.log_mul plus Real.log_exp.

## Formal target

```lean
theorem add_via_exp_log (x y : ℝ) : x + y = Real.log (Real.exp x * Real.exp y) := by sorry
```

## Dependencies
(none)

## Aristotle status
pending (project_id: null)
