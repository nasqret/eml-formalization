# Calc 0 → EML reduction — 028_calc0_to_eml

**Paper section**: §3 Results, Table 2 (rows 'Calc 0' and 'EML')
**Difficulty**: 4/5
**Status**: pending

## Source quote
> From Calc 0 {exp, log_x(y)} we collapse to EML {1, eml(·,·)} — exp(x) = eml(x, 1) and log_x(y) is built from the natural log via Identity 5.

## Informal (PL)
Najsilniejszy krok łańcucha: redukcja do trójki {1, eml}. Wymaga zarówno exp(x) = eml(x,1) (chunk 007) jak i ln(z) = eml(1, eml(eml(1,z),1)) (chunk 011). Stwierdzenie istnieniowe; pełna konstrukcja wymaga interpretera.

## Informal (EN)
The strongest step of the chain: reduction to {1, eml}. Uses both exp(x) = eml(x,1) (chunk 007) and ln(z) = eml(1, eml(eml(1,z),1)) (chunk 011). Stated as an existential; a constructive proof would need an interpreter.

## Formal target

```lean
theorem calc0_subset_eml : True := by sorry
```

## Dependencies
007_eml_x_one_eq_exp, 011_ln_via_eml

## Aristotle status
pending (project_id: null)
