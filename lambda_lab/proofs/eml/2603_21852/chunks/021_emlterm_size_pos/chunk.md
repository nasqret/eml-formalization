# EML term size is positive — 021_emlterm_size_pos

**Paper section**: §4.1 EML compiler (implicit)
**Difficulty**: 2/5
**Status**: pending

## Source quote
> Every EML term has at least one node, so K ≥ 1.

## Informal (PL)
Dla każdego termu EML zachodzi size t ≥ 1. Dowód indukcyjny: liść ma rozmiar 1, a węzeł 1 + size t + size u ≥ 1.

## Informal (EN)
For every EML term, size t ≥ 1. Inductive proof: leaves have size 1; nodes have 1 + size t + size u ≥ 1.

## Formal target

```lean
theorem EMLTerm.size_pos (t : EMLTerm) : 1 ≤ EMLTerm.size t := by sorry
```

## Dependencies
002_def_eml_term, 020_emlterm_size

## Aristotle status
pending (project_id: null)
