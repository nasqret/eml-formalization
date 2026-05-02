# Calc 1 → Calc 0 reduction — 027_calc1_to_calc0

**Paper section**: §3 Results, Table 2 (rows 'Calc 1' and 'Calc 0')
**Difficulty**: 3/5
**Status**: pending

## Source quote
> From Calc 1 {e, x^y, log_x(y)} we drop the constant and replace x^y with exp(x), reaching Calc 0 {exp, log_x(y)} (3 symbols).

## Informal (PL)
Tłumaczenie: `eConst` → `exp_ (logb varX varX)` (jako `e^1`), `logb a b` → `logb a b`, `pow a b` → `exp_ (logb (exp_ (inv b)) a)` gdzie `inv b := logb (exp_ b) (exp_ 1)` daje `ln(e)/ln(e^b) = 1/b`. Wówczas `logb (exp_ (1/b)) a = b · ln a`, a `exp_ (b · ln a) = a^b`. Stwierdzenie istnieniowe w naturalnej domenie dodatniości.

## Informal (EN)
Translation: `eConst` ↦ `exp_ (logb varX varX)` (yielding `e^1`); `logb a b` ↦ `logb a b`; `pow a b` ↦ `exp_ (logb (exp_ (inv b)) a)` with `inv b := logb (exp_ b) (exp_ 1)` evaluating to `ln(e)/ln(e^b) = 1/b`. Then `logb (exp_ (1/b)) a = b · ln a` and `exp_ (b · ln a) = a^b`. Existential statement, valid on the natural positivity domain.

## Formal target

```lean
theorem calc1_to_calc0 :
    ∀ e : Calc1, ∃ e' : Calc0,
      ∀ x y : ℝ, Calc0.eval x y e' = Calc1.eval x y e := by sorry
```

## Dependencies
(none — builds on `EML/Calc.lean`)

## Aristotle status
pending (project_id: null) — submitted in this round.
