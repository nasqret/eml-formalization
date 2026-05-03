# EMLTermℂ₁ realising arctan(x) — 065_emlterm_for_arctan_x

**Paper section**: §Sup. Table S2 step 32 (`arctan(x)`, K=4)
**Difficulty**: 5/5
**Status**: pending

## Source quote
> 32  arctan(x)    K=4    arcsin(tanh(arsinh(x)))

## Informal (PL)
arctan przez tożsamość zespoloną `(1/(2i)) · ln((1+ix)/(1−ix))`.
Świadek wymaga stałej `i` (chunk 035), podstawowej arytmetyki i `ln`.
Identyczność globalna w `x : ℝ`.

## Informal (EN)
arctan via the complex identity `(1/(2i)) · ln((1+ix)/(1−ix))`. Witness
needs constant `i` (chunk 035), basic arithmetic and `ln`. Identity is
global on `x : ℝ`.

## Formal target

```lean
theorem emlterm1c_for_arctan :
    ∃ t : EMLTermℂ₁, ∀ x : ℝ,
      (EMLTermℂ₁.eval (x : ℂ) t).re = Real.arctan x := by sorry
```

## Dependencies
035_emlterm_for_i, 036_emlterm_for_neg_x, 040_emlterm_for_add_xy,
050_emlterm_for_div_xy, 052_emlterm_for_half_x, 053_emlterm_for_log_xy

## Aristotle status
pending (project_id: null)
