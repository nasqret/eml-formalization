# EMLTerm whose eval is 0 — 030_emlterm_for_zero

**Paper section**: §3 Results, EML expression catalog (0, K=7)
**Difficulty**: 4/5
**Status**: pending

## Source quote
> 0: K = 7 (literal tree in Supplementary).

## Informal (PL)
Istnieje term EML rozmiaru 7, który ewaluuje się do 0. Liczbę kroków K=7 paper podaje, ale pełnego drzewa nie umieszcza w głównym tekście — formalne stwierdzenie istnieniowe; konstruktywny term wymaga przepisania z Supplementary.

## Informal (EN)
There exists an EML term of size 7 evaluating to 0. The paper reports K=7 but defers the literal tree to the Supplementary; we state existence and leave the witness as `sorry` until the literal tree is transcribed.

## Formal target

```lean
theorem emlterm_for_zero : ∃ t : EMLTerm, EMLTerm.eval t = 0 := by sorry
```

## Dependencies
002_def_eml_term, 003_def_eml_eval

## Aristotle status
pending (project_id: null)
