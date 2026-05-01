# EMLTerm₂ realising x^y — 042_emlterm_for_pow_xy

**Paper section**: §3 Results, EML expression catalog (x^y, K=49)
**Difficulty**: 5/5
**Status**: pending

## Source quote
> x^y: K = 49 (compiler) / K = 25 (direct search).

## Informal (PL)
Istnieje 2-zmienny term EML rozmiaru 49 (lub 25 direct-search) ewaluujący do x^y = exp(y · ln x) dla x > 0. Stwierdzenie istnieniowe.

## Informal (EN)
There exists a two-variable EML term of size 49 (or 25 direct-search) whose evaluation equals x^y = exp(y · ln x) for x > 0. Existential.

## Formal target

```lean
theorem emlterm2_for_pow : ∃ t : EMLTerm₂, ∀ x y : ℝ, 0 < x → EMLTerm₂.eval x y t = x ^ y := by sorry
```

## Dependencies
015_mul_via_exp_log

## Aristotle status
pending (project_id: null)
