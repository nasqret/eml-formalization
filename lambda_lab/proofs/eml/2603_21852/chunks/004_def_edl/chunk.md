# EDL variant (Exp Divided by Log) — 004_def_edl

**Paper section**: §3 Results, Identity 4b
**Difficulty**: 1/5
**Status**: pending

## Source quote
> edl(x, y) = exp(x) / ln(y),  constant: e

## Informal (PL)
Wariant EDL operatora EML korzysta z dzielenia zamiast odejmowania: edl(x,y) = exp(x)/ln(y) i wymaga stałej e zamiast 1. Ma podobne własności uniwersalne, ale z odmiennym 'punktem startowym'.

## Informal (EN)
The EDL variant uses division instead of subtraction: edl(x,y) = exp(x)/ln(y), with the constant e replacing 1. It has analogous universality properties but a different 'starting point'.

## Formal target

```lean
def edl (x y : ℝ) : ℝ := Real.exp x / Real.log y
```

## Dependencies
(none)

## Aristotle status
pending (project_id: null)
