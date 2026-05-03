# EMLTerm₁ realising x / 2 — 052_emlterm_for_half_x

**Paper section**: §Sup. Table S2 step 13 (`x/2`, K=2)
**Difficulty**: 4/5
**Status**: pending

## Source quote
> 13  x/2    K=2    x × (1/2)

## Informal (PL)
Funkcja `half : x ↦ x/2`. Tabela S2 podaje przepis `x/2 := x · (1/2)`,
gdzie stała `1/2` pochodzi z chunku 033, a mnożenie z chunku 041. Świadek
jest 1-zmiennym termem; wymaga `x > 0` z powodu założeń chunku 041.

## Informal (EN)
Function `half : x ↦ x/2`. Table S2 gives the recipe `x/2 := x · (1/2)`
with the `1/2` constant from chunk 033 and multiplication from chunk 041.
Witness is a one-variable term; `x > 0` is required by chunk 041's mul
positivity assumption.

## Formal target

```lean
theorem emlterm1_for_half :
    ∃ t : EMLTerm₁, ∀ x : ℝ, 0 < x → EMLTerm₁.eval x t = x / 2 := by sorry
```

## Dependencies
033_emlterm_for_half, 041_emlterm_for_mul_xy

## Aristotle status
pending (project_id: null)
