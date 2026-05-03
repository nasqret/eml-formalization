# EMLTerm₁ realising σ(x) — 055_emlterm_for_sigmoid_x

**Paper section**: §Sup. Table S2 step 20 (`σ(x)`, K=6)
**Difficulty**: 4/5
**Status**: pending

## Source quote
> 20  σ(x)    K=6    1 / eml(-x, exp(-1))

## Informal (PL)
Funkcja sigmoidalna logistyczna `σ(x) = 1/(1 + e^{-x})`. Świadek używa
identyczności EML: `eml(-x, exp(-1)) = e^{-x} - log(e^{-1}) = e^{-x} + 1`,
po czym bierze odwrotność (chunk 037). Identyczność zachodzi dla każdego
`x : ℝ`.

## Informal (EN)
Logistic sigmoid `σ(x) = 1/(1 + e^{-x})`. The witness uses the EML
identity `eml(-x, exp(-1)) = e^{-x} - log(e^{-1}) = e^{-x} + 1`, then
inverts (chunk 037). Identity holds for every `x : ℝ`.

## Formal target

```lean
theorem emlterm1_for_sigmoid :
    ∃ t : EMLTerm₁, ∀ x : ℝ,
      EMLTerm₁.eval x t = 1 / (1 + Real.exp (-x)) := by sorry
```

## Dependencies
022_emlterm_e_witness, 036_emlterm_for_neg_x, 037_emlterm_for_inv_x

## Aristotle status
pending (project_id: null)
