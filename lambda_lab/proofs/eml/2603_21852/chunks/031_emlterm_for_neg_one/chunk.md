# EMLTerm whose eval is −1 — 031_emlterm_for_neg_one

**Paper section**: §3 Results, EML expression catalog (−1, K=17)
**Difficulty**: 4/5
**Status**: pending

## Source quote
> −1: K = 17 (literal tree in Supplementary).

## Informal (PL)
Istnieje term EML rozmiaru 17 ewaluujący do −1. Stwierdzenie istnieniowe; konstrukcja w Supplementary.

## Informal (EN)
There exists an EML term of size 17 evaluating to −1. Existential; the literal tree is in the Supplementary.

## Formal target

```lean
theorem emlterm_for_neg_one : ∃ t : EMLTerm, EMLTerm.eval t = -1 := by sorry
```

## Dependencies
002_def_eml_term, 003_def_eml_eval

## Aristotle status
pending (project_id: null)
