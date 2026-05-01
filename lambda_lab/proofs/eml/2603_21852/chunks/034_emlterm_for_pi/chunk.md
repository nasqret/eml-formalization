# EMLTerm whose eval is π — 034_emlterm_for_pi

**Paper section**: §3 Results, EML expression catalog (π, K=193)
**Difficulty**: 5/5
**Status**: pending

## Source quote
> π: K = 193 (literal tree in Supplementary).

## Informal (PL)
Istnieje term EML rozmiaru 193 ewaluujący do π. PROBABLE PERMANENT SORRY: drzewo o 193 węzłach z Supplementary jest poza budżetem ręcznej transkrypcji w bieżącym przebiegu.

## Informal (EN)
There exists an EML term of size 193 evaluating to π. PROBABLE PERMANENT SORRY: transcribing a 193-node tree from the Supplementary by hand is beyond the budget of this auto-formalization pass.

## Formal target

```lean
theorem emlterm_for_pi : ∃ t : EMLTerm, EMLTerm.eval t = Real.pi := by sorry
```

## Dependencies
002_def_eml_term, 003_def_eml_eval

## Aristotle status
pending (project_id: null)
