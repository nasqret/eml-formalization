# EMLTermℂ₁ realising sin(x) — 063_emlterm_for_sin_x

**Paper section**: §Sup. Table S2 step 25 (`sin(x)`, K=5)
**Difficulty**: 5/5
**Status**: pending

## Source quote
> 25  sin(x)    K=5    cos(x - π/2)

## Informal (PL)
Sinus przesunięty: `sin x = cos(x − π/2)`. Świadek to chunk 062 z
podstawieniem zmiennej. Wymaga stałej `π` (chunk 034) i `1/2` (chunk
033 / 052) do zbudowania `π/2`.

## Informal (EN)
Shifted cosine: `sin x = cos(x − π/2)`. Witness is chunk 062 with a
variable shift. Requires constant `π` (chunk 034) and `1/2` (chunk 033
/ 052) to build `π/2`.

## Formal target

```lean
theorem emlterm1c_for_sin :
    ∃ t : EMLTermℂ₁, ∀ x : ℝ,
      (EMLTermℂ₁.eval (x : ℂ) t).re = Real.sin x := by sorry
```

## Dependencies
034_emlterm_for_pi, 052_emlterm_for_half_x, 062_emlterm_for_cos_x

## Aristotle status
pending (project_id: null)
