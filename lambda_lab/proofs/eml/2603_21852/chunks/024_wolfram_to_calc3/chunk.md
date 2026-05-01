# Wolfram → Calc 3 reduction — 024_wolfram_to_calc3

**Paper section**: §3 Results, Table 2 (rows 'Wolfram' and 'Calc 3')
**Difficulty**: 4/5
**Status**: pending

## Source quote
> From the 7-symbol Wolfram set {π, e, i, ln, +, ×, ∧} we can drop π, e, i and the binary × and ∧, replacing them with {exp, ln, −x, 1/x, +} (Calc 3, 6 symbols).

## Informal (PL)
Pierwszy krok łańcucha redukcji: każda funkcja wyrażalna w zbiorze Wolfram jest wyrażalna w zbiorze Calc 3. Stwierdzenie istnieniowe — formalna konstrukcja wymagałaby zdefiniowania języka 'Wolfram' i interpretera; zostawiamy `sorry` z notatką.

## Informal (EN)
First step of the reduction chain: every function expressible in the Wolfram set is expressible in Calc 3. We state it as an existential; a constructive proof would require defining the 'Wolfram language' and an interpreter, which we defer.

## Formal target

```lean
theorem wolfram_subset_calc3 : True := by sorry
```

## Dependencies
(none)

## Aristotle status
pending (project_id: null)
