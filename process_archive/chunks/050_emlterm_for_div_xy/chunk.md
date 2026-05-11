# EMLTerm₂ realising x / y — 050_emlterm_for_div_xy

**Paper section**: §Sup. Table S2 step 12 (`x/y`, K=4)
**Difficulty**: 4/5
**Status**: pending

## Source quote
> 12  x/y    K=4    x × inv(y)

## Informal (PL)
Istnieje 2-zmienny term EML ewaluujący do `x / y` dla `x, y > 0`. Świadek
budowany jako kompozycja chunków 041 (`x · y`) oraz 037 (`1/y`), zgodnie
z przepisem Tabeli S2 (krok 12): `x / y := x · (1/y)`.

## Informal (EN)
There exists a two-variable EML term evaluating to `x / y` for `x, y > 0`.
The witness composes chunk 041 (`x · y`) with chunk 037 (`1/y`), per
Table S2 step 12: `x / y := x · (1/y)`.

## Formal target

```lean
theorem emlterm2_for_div :
    ∃ t : EMLTerm₂, ∀ x y : ℝ, 0 < x → 0 < y →
      EMLTerm₂.eval x y t = x / y := by sorry
```

## Dependencies
037_emlterm_for_inv_x, 041_emlterm_for_mul_xy

## Aristotle status
pending (project_id: null)
