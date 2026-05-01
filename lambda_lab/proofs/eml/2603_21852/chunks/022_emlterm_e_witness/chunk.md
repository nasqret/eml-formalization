# An EML term whose eval is e — 022_emlterm_e_witness

**Paper section**: §3 Results, EML expression catalog (e, K=3)
**Difficulty**: 2/5
**Status**: pending

## Source quote
> e: eml(1, 1) — K = 3.

## Informal (PL)
Term EML eml(.one, .one) ewaluuje do exp(1) − ln(1) = e. Konstruktywne świadectwo, że stała e leży w obrazie eval. Rozmiar termu wynosi 3 (jeden węzeł + dwa liście), zgodnie z kolumną K paperu.

## Informal (EN)
The EML term eml(.one, .one) evaluates to exp(1) − ln(1) = e. A constructive witness that e lies in the image of eval. The term's size is 3 (one node + two leaves), matching the K column in the paper's catalogue.

## Formal target

```lean
theorem emlterm_e_witness : EMLTerm.eval (.eml .one .one) = Real.exp 1 := by sorry
```

## Dependencies
002_def_eml_term, 003_def_eml_eval

## Aristotle status
pending (project_id: null)
