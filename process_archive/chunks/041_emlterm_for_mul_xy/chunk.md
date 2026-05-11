# EMLTerm₂ realising x · y — 041_emlterm_for_mul_xy

**Paper section**: §3 Results, EML expression catalog (x × y, K=41)
**Difficulty**: 5/5
**Status**: pending

## Source quote
> x × y: K = 41 (compiler) / K = 17 (direct search).

## Informal (PL)
Istnieje 2-zmienny term EML rozmiaru 41 ewaluujący do x · y dla x, y > 0 (Identity 1). Stwierdzenie istnieniowe.

## Informal (EN)
There exists a two-variable EML term of size 41 whose evaluation equals x · y for x, y > 0 (Identity 1). Existential.

## Formal target

```lean
theorem emlterm2_for_mul : ∃ t : EMLTerm₂, ∀ x y : ℝ, 0 < x → 0 < y → EMLTerm₂.eval x y t = x * y := by sorry
```

## Dependencies
015_mul_via_exp_log

## Aristotle status
pending (project_id: null)
