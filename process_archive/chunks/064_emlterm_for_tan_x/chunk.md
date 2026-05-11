# EMLTermℂ₁ realising tan(x) — 064_emlterm_for_tan_x

**Paper section**: §Sup. Table S2 step 26 (`tan(x)`, K=5)
**Difficulty**: 5/5
**Status**: pending

## Source quote
> 26  tan(x)    K=5    sin x / cos x

## Informal (PL)
Tangens jako iloraz sin/cos; warunek nieosobliwości `cos x ≠ 0`.
Świadek korzysta z chunków 062, 063 (cos, sin) i 050 (dzielenie).

## Informal (EN)
Tangent as ratio sin/cos; non-singularity hypothesis `cos x ≠ 0`.
Witness uses chunks 062, 063 (cos, sin) and 050 (division).

## Formal target

```lean
theorem emlterm1c_for_tan :
    ∃ t : EMLTermℂ₁, ∀ x : ℝ, Real.cos x ≠ 0 →
      (EMLTermℂ₁.eval (x : ℂ) t).re = Real.tan x := by sorry
```

## Dependencies
050_emlterm_for_div_xy, 062_emlterm_for_cos_x, 063_emlterm_for_sin_x

## Aristotle status
pending (project_id: null)
