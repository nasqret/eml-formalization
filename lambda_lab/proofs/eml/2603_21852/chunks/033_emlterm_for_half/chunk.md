# EMLTerm whose eval is 1/2 — 033_emlterm_for_half

**Paper section**: §3 Results, EML expression catalog (1/2, K=91)
**Difficulty**: 4/5
**Status**: pending

## Source quote
> 1/2: K = 91 (literal tree in Supplementary).

## Informal (PL)
Istnieje term EML rozmiaru 91 ewaluujący do 1/2. Stwierdzenie istnieniowe; konstrukcja w Supplementary. Direct-search wariant ma K=29.

## Informal (EN)
There exists an EML term of size 91 evaluating to 1/2. Existential; the direct-search variant has K=29.

## Formal target

```lean
theorem emlterm_for_half : ∃ t : EMLTerm, EMLTerm.eval t = 1/2 := by sorry
```

## Dependencies
002_def_eml_term, 003_def_eml_eval

## Aristotle status
pending (project_id: null)
