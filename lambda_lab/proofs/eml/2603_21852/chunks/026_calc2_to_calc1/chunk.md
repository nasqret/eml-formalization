# Calc 2 → Calc 1 reduction — 026_calc2_to_calc1

**Paper section**: §3 Results, Table 2 (rows 'Calc 2' and 'Calc 1')
**Difficulty**: 3/5
**Status**: pending

## Source quote
> From Calc 2 {exp, ln, −} we move to Calc 1 {e or π} ∪ {x^y, log_x(y)}.

## Informal (PL)
Przejście od pary unarnych `exp/ln` z binarnym `−` do dwóch binarnych `pow/logb` ze stałą `e`. `exp a` to `pow eConst a`; `ln a` to `logb eConst a`. Trudność leży w `sub`: aby wyrazić `a − b` używając tylko `pow`, `logb` i `eConst`, trzeba albo skonstruować mnożenie i `−1`, albo posłużyć się tożsamościami logarytmicznymi, korzystając z konwencji "junk values" Mathliba (`Real.log 0 = 0`). Stwierdzenie istnieniowe.

## Informal (EN)
Move from the unary {exp, ln} + binary {−} to the binary pair {pow, logb} with the constant `e`. `exp a ↦ pow eConst a`, `ln a ↦ logb eConst a`. The hard step is `sub`: expressing `a − b` from `pow`, `logb`, `eConst` alone requires either constructing multiplication and `−1`, or relying on logarithm identities that exploit Mathlib's junk-value conventions (`Real.log 0 = 0`). Existential statement.

## Formal target

```lean
theorem calc2_to_calc1 :
    ∀ e : Calc2, ∃ e' : Calc1,
      ∀ x y : ℝ, Calc1.eval x y e' = Calc2.eval x y e := by sorry
```

## Dependencies
(none — builds on `EML/Calc.lean`)

## Aristotle status
pending (project_id: null) — submitted in this round.
