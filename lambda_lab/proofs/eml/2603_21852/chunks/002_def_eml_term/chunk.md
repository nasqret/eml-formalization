# Inductive type of EML terms — 002_def_eml_term

**Paper section**: §4.2 Elementary functions as binary trees
**Difficulty**: 1/5
**Status**: pending

## Source quote
> S → 1 | eml(S, S)

## Informal (PL)
Termy EML to pełne drzewa binarne: każdy liść jest stałą 1, a każdy węzeł wewnętrzny jest aplikacją operatora eml na dwóch poddrzewach. Język ten jest izomorficzny ze strukturami katalańskimi.

## Informal (EN)
EML terms are full binary trees: every leaf is the constant 1, and every internal node is an application of the eml operator to two subtrees. The language is isomorphic to the Catalan structures.

## Formal target

```lean
inductive EMLTerm : Type
  | one : EMLTerm
  | eml : EMLTerm → EMLTerm → EMLTerm
```

## Dependencies
(none)

## Aristotle status
pending (project_id: null)
