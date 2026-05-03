# EMLTermℂ₁ realising arccos(x) — 067_emlterm_for_arccos_x

**Paper section**: §Sup. Table S2 step 29 (`arccos(x)`, K=4)
**Difficulty**: 5/5
**Status**: pending

## Source quote
> 29  arccos(x)    K=4    arcosh(cos(arcosh(x)))

## Informal (PL)
arccos jako `π/2 − arcsin x`. Paperowa recepta `arcosh∘cos∘arcosh` jest
równoważna ale wymaga arcosh poza `[1,∞)`; my korzystamy z klasycznej
komplementarności (chunk 066).

## Informal (EN)
arccos as `π/2 − arcsin x`. The paper's `arcosh∘cos∘arcosh` recipe is
equivalent but extends arcosh outside `[1,∞)`; we use the classical
complementarity (chunk 066).

## Formal target

```lean
theorem emlterm1c_for_arccos :
    ∃ t : EMLTermℂ₁, ∀ x : ℝ, -1 < x → x < 1 →
      (EMLTermℂ₁.eval (x : ℂ) t).re = Real.arccos x := by sorry
```

## Dependencies
034_emlterm_for_pi, 040_emlterm_for_add_xy, 052_emlterm_for_half_x,
066_emlterm_for_arcsin_x

## Aristotle status
pending (project_id: null)
