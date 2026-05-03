# EMLTerm₂ realising hypot(x, y) — 054_emlterm_for_hypot_xy

**Paper section**: §Sup. Table S2 step 19 (`hypot(x,y)`, K=6)
**Difficulty**: 4/5
**Status**: pending

## Source quote
> 19  hypot(x,y)    K=6    √(x² + y²)

## Informal (PL)
Funkcja euklidesowej długości boku `hypot(x,y) = √(x² + y²)`. Świadek
korzysta z chunków 038 (`x²`), 040 (`+`) i 039 (`√x`). Wszystkie podtermy
wymagają dodatnich wejść, stąd `x, y > 0`.

## Informal (EN)
Euclidean leg-length `hypot(x,y) = √(x² + y²)`. Witness composes chunks
038 (`x²`), 040 (`+`) and 039 (`√x`). All sub-terms need positive inputs,
hence `x, y > 0`.

## Formal target

```lean
theorem emlterm2_for_hypot :
    ∃ t : EMLTerm₂, ∀ x y : ℝ, 0 < x → 0 < y →
      EMLTerm₂.eval x y t = Real.sqrt (x ^ 2 + y ^ 2) := by sorry
```

## Dependencies
038_emlterm_for_sq_x, 039_emlterm_for_sqrt_x, 040_emlterm_for_add_xy

## Aristotle status
pending (project_id: null)
