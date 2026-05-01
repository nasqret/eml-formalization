# Negated-EML variant — 005_def_neg_eml

**Paper section**: §3 Results, Identity 4c
**Difficulty**: 1/5
**Status**: pending

## Source quote
> −eml(y, x) = ln(x) − exp(y),  constant: −∞

## Informal (PL)
Trzeci wariant operatora to negacja EML z zamianą argumentów: -eml(y,x) = ln(x) - exp(y). W paperze 'stała' jest oznaczona jako -∞, co odzwierciedla różnicę topologiczną przy próbie wyrażenia stałej 1.

## Informal (EN)
The third variant negates EML and swaps the arguments: -eml(y,x) = ln(x) - exp(y). The paper labels its required constant as −∞, reflecting a topological difference when trying to express 1.

## Formal target

```lean
def negEml (x y : ℝ) : ℝ := Real.log x - Real.exp y
```

## Dependencies
(none)

## Aristotle status
pending (project_id: null)
