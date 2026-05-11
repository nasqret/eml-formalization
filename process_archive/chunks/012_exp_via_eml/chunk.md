# exp(x) as eml — corollary phrasing of 007 — 012_exp_via_eml

**Paper section**: §3 Results, EML expression catalog
**Difficulty**: 2/5
**Status**: pending

## Source quote
> exp(x) = eml(x, 1)

## Informal (PL)
Reformulacja chunka 007 w postaci 'definitorycznej': exp(x) jest dokładnie eml(x,1). Dowód zwykle dziedziczy się przez `(eml_x_one x).symm`.

## Informal (EN)
A re-statement of chunk 007 in 'definitional' direction: exp(x) is exactly eml(x,1). The proof typically just inherits via `(eml_x_one x).symm`.

## Formal target

```lean
theorem exp_via_eml (x : ℝ) : Real.exp x = eml x 1 := by sorry
```

## Dependencies
001_def_eml, 007_eml_x_one_eq_exp

## Aristotle status
pending (project_id: null)
