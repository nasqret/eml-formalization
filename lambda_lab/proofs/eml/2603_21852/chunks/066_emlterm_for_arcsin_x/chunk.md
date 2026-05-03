# EMLTermℂ₁ realising arcsin(x) — 066_emlterm_for_arcsin_x

**Paper section**: §Sup. Table S2 step 31 (`arcsin(x)`, K=5)
**Difficulty**: 5/5
**Status**: pending

## Source quote
> 31  arcsin(x)    K=5    π/2 − arccos(x)

## Informal (PL)
arcsin via arctan i hypot: `arcsin x = arctan(x / √(1 − x²))` na otwartym
przedziale `(−1, 1)`. Decyzja: nie używamy paperowego `π/2 − arccos`, bo
arccos jest budowany dalej w łańcuchu (chunk 067) — uniknięcie cykliczności.

## Informal (EN)
arcsin via arctan and hypot: `arcsin x = arctan(x / √(1 − x²))` on the
open interval `(−1, 1)`. Decision: we do NOT use the paper's
`π/2 − arccos` recipe because arccos is built later in our chain
(chunk 067) — avoiding circularity.

## Formal target

```lean
theorem emlterm1c_for_arcsin :
    ∃ t : EMLTermℂ₁, ∀ x : ℝ, -1 < x → x < 1 →
      (EMLTermℂ₁.eval (x : ℂ) t).re = Real.arcsin x := by sorry
```

## Dependencies
038_emlterm_for_sq_x, 039_emlterm_for_sqrt_x, 050_emlterm_for_div_xy,
065_emlterm_for_arctan_x

## Aristotle status
pending (project_id: null)
