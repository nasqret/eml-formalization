# EMLTerm whose eval is 2 — 032_emlterm_for_two

**Paper section**: §3 Results, EML expression catalog (2, K=27)
**Difficulty**: 4/5
**Status**: pending

## Source quote
> 2: K = 27 (literal tree in Supplementary).

## Informal (PL)
Istnieje term EML rozmiaru 27 ewaluujący do 2. Stwierdzenie istnieniowe; konstrukcja w Supplementary. Direct-search wariant ma K=19.

## Informal (EN)
There exists an EML term of size 27 evaluating to 2. Existential; the direct-search variant has K=19.

## Formal target

```lean
theorem emlterm_for_two : ∃ t : EMLTerm, EMLTerm.eval t = 2 := by sorry
```

## Dependencies
002_def_eml_term, 003_def_eml_eval

## Aristotle status
pending (project_id: null)
