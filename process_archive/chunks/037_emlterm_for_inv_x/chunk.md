# EMLTerm₁ realising the function 1/x — 037_emlterm_for_inv_x

**Paper section**: §3 Results, EML expression catalog (1/x, K=65)
**Difficulty**: 5/5
**Status**: pending

## Source quote
> 1/x: K = 65 (compiler) / K = 15 (direct search).

## Informal (PL)
Istnieje parametryzowany term EML rozmiaru 65 (lub 15 direct-search) ewaluujący do 1/x dla każdego niezerowego x. Stwierdzenie istnieniowe; ze względu na junk-value w 0 ograniczenie x ≠ 0 jest semantyczne, nie formalne.

## Informal (EN)
There exists a parameterised EML term of size 65 (or 15 direct-search) whose evaluation equals 1/x for every nonzero x. Existential; the x ≠ 0 constraint is semantic — Real has junk values at 0.

## Formal target

```lean
theorem emlterm1_for_inv_x : ∃ t : EMLTerm₁, ∀ x : ℝ, x ≠ 0 → EMLTerm₁.eval x t = 1 / x := by sorry
```

## Dependencies
023_emlterm_exp_x_witness

## Aristotle status
pending (project_id: null)
