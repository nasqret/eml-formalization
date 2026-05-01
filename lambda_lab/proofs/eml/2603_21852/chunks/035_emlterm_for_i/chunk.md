# EMLTerm whose eval is i (imaginary unit) — 035_emlterm_for_i

**Paper section**: §3 Results, EML expression catalog (i, K=131)
**Difficulty**: 5/5
**Status**: pending

## Source quote
> i: K = 131 (literal tree in Supplementary).

## Informal (PL)
Istnieje term EML (po przeniesieniu na ℂ) rozmiaru 131 ewaluujący do jednostki urojonej i. PROBABLE PERMANENT SORRY: wymaga zarówno wersji zespolonej EMLTerm jak i transkrypcji 131-węzłowego drzewa.

## Informal (EN)
There exists an EML term (after lifting to ℂ) of size 131 evaluating to i. PROBABLE PERMANENT SORRY: requires both a complex variant of EMLTerm and transcription of the 131-node tree.

## Formal target

```lean
theorem emlterm_for_i : ∃ t : EMLTermℂ, EMLTermℂ.eval t = Complex.I := by sorry
```

## Dependencies
(none)

## Aristotle status
pending (project_id: null)
