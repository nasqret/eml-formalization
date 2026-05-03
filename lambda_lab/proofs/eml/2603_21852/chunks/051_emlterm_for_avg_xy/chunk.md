# EMLTerm₂ realising avg(x, y) — 051_emlterm_for_avg_xy

**Paper section**: §Sup. Table S2 step 14 (`avg(x,y)`, K=5)
**Difficulty**: 4/5
**Status**: pending

## Source quote
> 14  avg(x,y)    K=5    half(x + y)

## Informal (PL)
Średnia arytmetyczna `(x+y)/2`. Świadek (Tabela S2, krok 14) to złożenie
chunków 040 (`x + y`) i 052 (`half`). Pełna identyczność `avg(x,y) =
(x+y)/2` zachodzi bez warunków na znak.

## Informal (EN)
Arithmetic mean `(x+y)/2`. The witness (Table S2 step 14) composes chunk
040 (`x + y`) with chunk 052 (`half`). The full identity `avg(x,y) =
(x+y)/2` holds without sign hypotheses.

## Formal target

```lean
theorem emlterm2_for_avg :
    ∃ t : EMLTerm₂, ∀ x y : ℝ, EMLTerm₂.eval x y t = (x + y) / 2 := by sorry
```

## Dependencies
040_emlterm_for_add_xy, 052_emlterm_for_half_x

## Aristotle status
pending (project_id: null)
