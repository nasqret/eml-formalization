# EMLTerm₁ realising tanh(x) — 058_emlterm_for_tanh_x

**Paper section**: §Sup. Table S2 step 23 (`tanh(x)`, K=5)
**Difficulty**: 4/5
**Status**: pending

## Source quote
> 23  tanh(x)    K=5    sinh x / cosh x

## Informal (PL)
Tangens hiperboliczny `tanh x = sinh x / cosh x`. Świadek korzysta z chunków
056, 057 oraz 050. Dzielenie jest bezpieczne, bo `cosh x > 0` dla każdego `x`.

## Informal (EN)
Hyperbolic tangent `tanh x = sinh x / cosh x`. Witness uses chunks 056,
057 and 050. Division is safe because `cosh x > 0` for every `x`.

## Formal target

```lean
theorem emlterm1_for_tanh :
    ∃ t : EMLTerm₁, ∀ x : ℝ, EMLTerm₁.eval x t = Real.tanh x := by sorry
```

## Dependencies
050_emlterm_for_div_xy, 056_emlterm_for_cosh_x, 057_emlterm_for_sinh_x

## Aristotle status
pending (project_id: null)
