# Calc 0 → EML reduction — 028_calc0_to_eml

**Paper section**: §3 Results, Table 2 (rows 'Calc 0' and 'EML')
**Difficulty**: 4/5
**Status**: pending

## Source quote
> From Calc 0 {exp, log_x(y)} we collapse to EML {1, eml(·,·)} — exp(x) = eml(x, 1) and log_x(y) is built from the natural log via Identity 5.

## Informal (PL)
Najsilniejszy krok łańcucha: redukcja do trójki {1, varX/varY, eml}. Korzysta z `exp(x) = eml(x, 1)` (chunk 007), `ln(z) = eml(1, eml(eml(1, z), 1))` (chunk 011) i tożsamości polowej `c/d = exp(ln c − ln d)`. `logb a b = ln b / ln a` realizuje się jako głęboko zagnieżdżona kompozycja eml. Stwierdzenie istnieniowe.

## Informal (EN)
The strongest step of the chain: reduction to {1, varX/varY, eml}. Uses `exp(x) = eml(x, 1)` (chunk 007), `ln(z) = eml(1, eml(eml(1, z), 1))` (chunk 011) and the field identity `c/d = exp(ln c − ln d)`. `logb a b = ln b / ln a` is realised as a deeply nested eml composition. Existential statement.

## Formal target

```lean
theorem calc0_to_eml :
    ∀ e : Calc0, ∃ e' : EMLTerm₂,
      ∀ x y : ℝ, EMLTerm₂.eval x y e' = Calc0.eval x y e := by sorry
```

## Dependencies
007_eml_x_one_eq_exp, 011_ln_via_eml

## Aristotle status
pending (project_id: null) — submitted in this round.
