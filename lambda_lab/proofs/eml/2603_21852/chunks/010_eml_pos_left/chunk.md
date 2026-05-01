# Positivity of the left exponential of eml — 010_eml_pos_left

**Paper section**: §3 Results (implicit; pre-condition lemma)
**Difficulty**: 1/5
**Status**: pending

## Source quote
> exp(x) > 0 for every real x, hence the leading exp term in eml(x,y) is always positive.

## Informal (PL)
Lewa część operatora EML, exp(x), jest zawsze ściśle dodatnia. Ten elementarny lemat podpiera dalsze argumenty pozytywności (np. dla pochodnych logarytmu w 011).

## Informal (EN)
The left summand of EML, exp(x), is always strictly positive. This trivial lemma underpins later positivity arguments (e.g. for the log argument in chunk 011).

## Formal target

```lean
theorem eml_left_pos (x y : ℝ) : 0 < Real.exp x := by sorry
```

## Dependencies
001_def_eml

## Aristotle status
pending (project_id: null)
