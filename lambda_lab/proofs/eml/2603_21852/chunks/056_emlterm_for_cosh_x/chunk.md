# EMLTerm₁ realising cosh(x) — 056_emlterm_for_cosh_x

**Paper section**: §Sup. Table S2 step 21 (`cosh(x)`, K=6)
**Difficulty**: 4/5
**Status**: pending

## Source quote
> 21  cosh(x)    K=6    avg(exp x, exp(-x))

## Informal (PL)
Cosinus hiperboliczny `cosh(x) = (e^x + e^{-x})/2`. Świadek to złożenie
chunków 023 (`exp x`), 036 (`-x`) i 051 (`avg`). Identyczność zachodzi
bezwarunkowo dla każdego `x : ℝ`.

## Informal (EN)
Hyperbolic cosine `cosh(x) = (e^x + e^{-x})/2`. Witness composes chunks
023 (`exp x`), 036 (`-x`) and 051 (`avg`). Identity holds unconditionally
for every `x : ℝ`.

## Formal target

```lean
theorem emlterm1_for_cosh :
    ∃ t : EMLTerm₁, ∀ x : ℝ, EMLTerm₁.eval x t = Real.cosh x := by sorry
```

## Dependencies
023_emlterm_exp_x_witness, 036_emlterm_for_neg_x, 051_emlterm_for_avg_xy

## Aristotle status
pending (project_id: null)
