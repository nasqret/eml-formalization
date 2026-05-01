# Multiplication via Identity 1 (Exp-Log reduction) — 015_mul_via_exp_log

**Paper section**: §3 Results, Identity 1
**Difficulty**: 2/5
**Status**: pending

## Source quote
> x × y = exp(ln x + ln y)

## Informal (PL)
Mnożenie liczb dodatnich daje się odzyskać z dodawania ich logarytmów: x · y = exp(ln x + ln y) dla x, y > 0. To multiplikatywna połowa Identity 1.

## Informal (EN)
The product of positive reals is recovered by exponentiating the sum of logs: x · y = exp(ln x + ln y) for x, y > 0. The multiplicative half of Identity 1.

## Formal target

```lean
theorem mul_via_exp_log (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : x * y = Real.exp (Real.log x + Real.log y) := by sorry
```

## Dependencies
(none)

## Aristotle status
pending (project_id: null)
