# EMLTerm₁ realising the function −x — 036_emlterm_for_neg_x

**Paper section**: §3 Results, EML expression catalog (−x, K=57)
**Difficulty**: 5/5
**Status**: pending

## Source quote
> −x: K = 57 (compiler) / K = 15 (direct search).

## Informal (PL)
Istnieje parametryzowany term EML rozmiaru 57 (lub 15 w wariancie direct-search), który dla każdego x ewaluuje do −x. Stwierdzenie istnieniowe; ścisły dowód wymaga successor identity 017 w wersji termowej.

## Informal (EN)
There exists a parameterised EML term of size 57 (or 15 in the direct-search variant) whose evaluation at every x equals −x. Existential; the formal proof would lift the successor identity (017) to the term level.

## Formal target

```lean
theorem emlterm1_for_neg_x : ∃ t : EMLTerm₁, ∀ x : ℝ, EMLTerm₁.eval x t = -x := by sorry
```

## Dependencies
023_emlterm_exp_x_witness

## Aristotle status
pending (project_id: null)
