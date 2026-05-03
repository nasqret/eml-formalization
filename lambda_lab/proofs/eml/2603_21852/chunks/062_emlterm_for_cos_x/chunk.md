# EMLTermℂ₁ realising cos(x) — 062_emlterm_for_cos_x

**Paper section**: §Sup. Table S2 step 24 (`cos(x)`, K=5)
**Difficulty**: 5/5
**Status**: pending

## Source quote
> 24  cos(x)    K=5    cosh(√(-x²)) = cosh(i·x)

## Informal (PL)
Cosinus rzeczywisty `cos x = Re(cosh(i·x))`. Wymagamy rozszerzenia
gramatyki termów do wariantu `EMLTermℂ₁` (zespolona ewaluacja, jedna
zmienna), wzorowanego na chunkach 034/035. Świadek korzysta ze stałej
`i` (chunk 035) i makra `cosh` (chunk 056 podniesionego do ℂ).

## Informal (EN)
Real cosine `cos x = Re(cosh(i·x))`. Requires extending the term grammar
to `EMLTermℂ₁` (complex evaluation, one variable), modelled on chunks
034/035. Witness uses constant `i` (chunk 035) and the `cosh` macro
(chunk 056 lifted to ℂ).

## Formal target

```lean
theorem emlterm1c_for_cos :
    ∃ t : EMLTermℂ₁, ∀ x : ℝ,
      (EMLTermℂ₁.eval (x : ℂ) t).re = Real.cos x := by sorry
```

## Dependencies
035_emlterm_for_i, 056_emlterm_for_cosh_x

## Aristotle status
pending (project_id: null)
