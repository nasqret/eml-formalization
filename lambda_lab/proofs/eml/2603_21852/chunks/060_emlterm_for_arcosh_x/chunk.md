# EMLTerm₁ realising arcosh(x) — 060_emlterm_for_arcosh_x

**Paper section**: §Sup. Table S2 step 28 (`arcosh(x)`, K=5)
**Difficulty**: 4/5
**Status**: pending

## Source quote
> 28  arcosh(x)    K=5    arsinh(hypot(x, √(-1)))

## Informal (PL)
Funkcja odwrotna do cosh, dziedzina `x ≥ 1`. Standardowa forma:
`arcosh x = ln(x + √(x² − 1))`. Paper zapisuje to przez kompozycję
arsinh ∘ hypot z urojonym argumentem (`√(−1) = i`), co przy ścisłym
trzymaniu się ℝ wymaga lokalnej eliminacji warunku `x² − 1 ≥ 0`. Tu
formalizujemy bezpośrednio rzeczywistą formę.

## Informal (EN)
Inverse of cosh, domain `x ≥ 1`. Standard form: `arcosh x = ln(x +
√(x² − 1))`. The paper writes this as `arsinh ∘ hypot` with the second
argument the imaginary `√(−1)`; staying purely in ℝ we instead use the
textbook real form directly under the hypothesis `x² − 1 ≥ 0`.

## Formal target

```lean
theorem emlterm1_for_arcosh :
    ∃ t : EMLTerm₁, ∀ x : ℝ, 1 ≤ x → EMLTerm₁.eval x t = Real.arcosh x := by sorry
```

## Dependencies
011_ln_via_eml, 040_emlterm_for_add_xy, 054_emlterm_for_hypot_xy, 059_emlterm_for_arsinh_x

## Aristotle status
pending (project_id: null)
