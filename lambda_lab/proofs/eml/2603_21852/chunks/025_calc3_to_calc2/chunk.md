# Calc 3 → Calc 2 reduction — 025_calc3_to_calc2

**Paper section**: §3 Results, Table 2 (rows 'Calc 3' and 'Calc 2')
**Difficulty**: 3/5
**Status**: pending

## Source quote
> From Calc 3 {exp, ln, −x, 1/x, +} we drop −x, 1/x and replace + with − to obtain Calc 2 {exp, ln, −} (4 symbols).

## Informal (PL)
Krok kanoniczny: `−x` zastępujemy przez `0 − x` (a `0 := varX − varX`); `+` przez `a + b = a − (0 − b)`; `1/x` przez `exp(0 − ln x)` (poprawnie dla `x > 0`; poza tym domeną zgadza się dzięki konwencji Mathliba). `exp` i `ln` przekładają się tożsamościowo. Stwierdzenie: dla każdego `e : Calc3` istnieje `e' : Calc2` taki, że `Calc2.eval x y e' = Calc3.eval x y e` dla wszystkich `x y`.

## Informal (EN)
Canonical step: `−x` becomes `0 − x` (with `0 := varX − varX`); `+` becomes `a + b = a − (0 − b)`; `1/x` becomes `exp(0 − ln x)` (correct for `x > 0`; on the rest of the domain the equality is preserved by Mathlib's `Real.log 0 = 0` convention). `exp` and `ln` translate identically. Statement: for every `e : Calc3` there exists `e' : Calc2` with `Calc2.eval x y e' = Calc3.eval x y e` for all `x y`.

## Formal target

```lean
theorem calc3_to_calc2 :
    ∀ e : Calc3, ∃ e' : Calc2,
      ∀ x y : ℝ, Calc2.eval x y e' = Calc3.eval x y e := by sorry
```

## Dependencies
019_negation_in_calc3 (informally — provides the −x = 0 − x identity at the level of Calc3 evaluation)

## Aristotle status
pending (project_id: null) — submitted to Aristotle in this round.
