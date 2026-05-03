# EMLTerm₂ realising log_x y — 053_emlterm_for_log_xy

**Paper section**: §Sup. Table S2 step 17 (`log_x y`, K=5)
**Difficulty**: 4/5
**Status**: pending

## Source quote
> 17  log_x y    K=5    ln y / ln x

## Informal (PL)
Logarytm o dowolnej podstawie `log_x y = ln y / ln x`. Świadek wymaga
`x > 1` (aby `ln x > 0`) oraz `y > 0`. Korzysta z chunku 011 (`ln`)
i chunku 050 (dzielenie).

## Informal (EN)
Logarithm with arbitrary base `log_x y = ln y / ln x`. Witness requires
`x > 1` (so `ln x > 0`) and `y > 0`. Reuses chunk 011 (`ln`) and chunk 050
(division).

## Formal target

```lean
theorem emlterm2_for_log :
    ∃ t : EMLTerm₂, ∀ x y : ℝ, 1 < x → 0 < y →
      EMLTerm₂.eval x y t = Real.log y / Real.log x := by sorry
```

## Dependencies
011_ln_via_eml, 050_emlterm_for_div_xy

## Aristotle status
pending (project_id: null)
