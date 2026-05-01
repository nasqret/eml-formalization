# Size function on EML terms — 020_emlterm_size

**Paper section**: §4.1 EML compiler ('K denotes the size of the RPN code')
**Difficulty**: 2/5
**Status**: pending

## Source quote
> K denotes the size of the RPN code (number of EML/leaf nodes in the binary tree).

## Informal (PL)
Definiujemy size termu EML jako liczbę węzłów: liść .one ma rozmiar 1, węzeł .eml t u ma rozmiar 1 + size t + size u. Odpowiada to długości RPN-kodu z paperu (kolumna 'EML compiler K').

## Informal (EN)
We define the size of an EML term as the number of nodes: .one has size 1, and .eml t u has size 1 + size t + size u. This matches the K column ('EML compiler K') in the paper's catalogue.

## Formal target

```lean
def EMLTerm.size : EMLTerm → ℕ
  | .one => 1
  | .eml t u => 1 + EMLTerm.size t + EMLTerm.size u
```

## Dependencies
002_def_eml_term

## Aristotle status
pending (project_id: null)
