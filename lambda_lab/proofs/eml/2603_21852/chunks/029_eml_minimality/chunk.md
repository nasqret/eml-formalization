# Minimality: three primitives is the minimum — 029_eml_minimality

**Paper section**: §3 Results (concluding remark on Table 2)
**Difficulty**: 5/5
**Status**: pending

## Source quote
> Three primitives is the minimum: any further reduction would either drop the constant (leaving an unsatisfiable arity equation) or merge eml with another operation in a way that loses expressiveness.

## Informal (PL)
Twierdzenie negatywne: nie istnieje konfiguracja kalkulatora z mniej niż trzema prymitywami zachowująca pełną elementarną wyrażalność. Pełny dowód uniwersalny pozostaje otwartym problemem w pracy. Formalizujemy jeden operacyjny korelat: usunięcie operatora `eml` z wiersza EML pozostawia tylko stałą `1`, która nie reprezentuje funkcji `x ↦ x`. Symetryczne argumenty wykluczają inne podzbiory dwuelementowe.

## Informal (EN)
Negative claim: no calculator with fewer than three primitives retains full elementary expressiveness. The fully universal proof remains open in the paper. We formalise one operational corollary: dropping the `eml` operator from the EML row leaves only the constant `1`, which cannot represent the identity function `x ↦ x`. Symmetric arguments rule out the other 2-element subsets.

## Formal targets

```lean
-- Provable: dropping `eml` leaves only the constant 1, which cannot express x ↦ x.
theorem eml_only_one_cannot_represent_identity :
    ¬ ∃ t : EMLOnlyOne, ∀ x : ℝ, EMLOnlyOne.eval t = x := …

-- Open / universal claim — kept as sorry.
theorem eml_minimality_universal : True := by sorry
```

## Dependencies
(none)

## Aristotle status
pending (project_id: null) — **not** submitted; the universal minimality remains a permanent `sorry` stub by design (open problem in the paper).
