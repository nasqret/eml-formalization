# Count of EMLTerms equals the Catalan number — 044_emlterm_count_catalan

**Paper section**: §4.2 Elementary functions as binary trees ('Catalan structures')
**Difficulty**: 4/5
**Status**: pending

## Source quote
> Context-free language; isomorphic to full binary trees / Catalan structures.

## Informal (PL)
Liczba pełnych drzew binarnych z n liśćmi (= n+1 wewnętrznych krawędzi) to liczba Catalana C_n. Indukcyjnie: liczba EMLTerm-ów rozmiaru 2k+1 wynosi C_k. Mathlib zawiera Nat.catalan.

## Informal (EN)
The number of full binary trees with n leaves is the Catalan number C_{n−1}. By induction, the count of EMLTerms of size 2k+1 is C_k. Mathlib has `Nat.catalan`.

## Formal target

```lean
theorem emlterm_count_catalan (k : ℕ) :
    ∃ (S : Finset EMLTerm), … ∧ S.card = Nat.catalan k := by sorry
```

## Dependencies
002_def_eml_term, 020_emlterm_size

## Aristotle status
pending (project_id: null)
