# EMLTerm₁ realising sinh(x) — 057_emlterm_for_sinh_x

**Paper section**: §Sup. Table S2 step 22 (`sinh(x)`, K=5)
**Difficulty**: 4/5
**Status**: pending

## Source quote
> 22  sinh(x)    K=5    eml(x, exp(cosh x))

## Informal (PL)
Sinus hiperboliczny. Paperowy makro: `sinh x = eml(x, e^{cosh x}) =
exp(x) - cosh(x)` (równoważne `(e^x - e^{-x})/2`). Świadek korzysta
z chunku 056 (cosh) i chunku 023 (exp x). Identyczność dla każdego `x`.

## Informal (EN)
Hyperbolic sine. Paper macro: `sinh x = eml(x, e^{cosh x}) = exp(x) -
cosh(x)` (equivalently `(e^x - e^{-x})/2`). Witness uses chunk 056
(cosh) and chunk 023 (exp x). Identity for every `x`.

## Formal target

```lean
theorem emlterm1_for_sinh :
    ∃ t : EMLTerm₁, ∀ x : ℝ, EMLTerm₁.eval x t = Real.sinh x := by sorry
```

## Dependencies
023_emlterm_exp_x_witness, 056_emlterm_for_cosh_x

## Aristotle status
pending (project_id: null)
