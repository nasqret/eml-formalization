# Calc 3 → Calc 2 reduction — 025_calc3_to_calc2

**Paper section**: §3 Results, Table 2 (rows 'Calc 3' and 'Calc 2')
**Difficulty**: 3/5
**Status**: pending

## Source quote
> From Calc 3 {exp, ln, −x, 1/x, +} we drop −x, 1/x and replace + with − to obtain Calc 2 {exp, ln, −} (4 symbols).

## Informal (PL)
Krok kanoniczny: −x usuwamy przez successor identity (chunk 019); 1/x przez tożsamości algebraiczne; + zostaje zastąpione − bo a + b = a − (−b) i −b mamy z 019. Stwierdzenie istnieniowe.

## Informal (EN)
Canonical step: −x is removed via the successor identity (chunk 019); 1/x via algebraic identities; + is replaced by − because a + b = a − (−b) and −b is now available. Stated as a placeholder existential.

## Formal target

```lean
theorem calc3_subset_calc2 : True := by sorry
```

## Dependencies
019_negation_in_calc3

## Aristotle status
pending (project_id: null)
