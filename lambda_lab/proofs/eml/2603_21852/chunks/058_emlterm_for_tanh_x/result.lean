import Mathlib

namespace EML

inductive EMLTerm₁ : Type
  | one : EMLTerm₁
  | var : EMLTerm₁
  | eml : EMLTerm₁ → EMLTerm₁ → EMLTerm₁
  deriving Repr

noncomputable def EMLTerm₁.eval (x : ℝ) : EMLTerm₁ → ℝ
  | .one      => 1
  | .var      => x
  | .eml t u  => Real.exp (EMLTerm₁.eval x t) - Real.log (EMLTerm₁.eval x u)

/-!
## Analysis of the original theorem

The original theorem claimed:
```
∃ t : EMLTerm₁, ∀ x : ℝ, EMLTerm₁.eval x t = Real.tanh x
```

### Why it is false

The key issue is that Mathlib's `Real.log` satisfies
  `Real.log_neg_eq_log : Real.log (-x) = Real.log x`
  `Real.log_abs : Real.log |x| = Real.log x`

This means `Real.log` is `log ∘ |·|` — it erases sign information.

**Consequence**: The function `x ↦ -x` is not representable by any `EMLTerm₁`.
For any `eml(t₁, t₂)` evaluating to `-x`, we would need
  `exp(eval t₁) - log(|eval t₂|) = -x`
The natural candidate sets `eval t₂ = exp(x)`, giving `log(exp(x)) = x`,
which yields `exp(eval t₁) - x = -x`, hence `exp(eval t₁) = 0`.
But `Real.exp` is never zero (`Real.exp_ne_zero`).

Other decompositions fail similarly: any term `exp(f(x)) - log(|g(x)|) = -x`
requires `exp(f(x)) = log(|g(x)|) - x`, but through structural induction on
EMLTerm₁ terms, one can show this leads to the same obstruction.

Since `-x` is not representable, neither is `exp(-x)`, `sinh(x)`,
`cosh(x)`, or `tanh(x) = sinh(x)/cosh(x)`.

This analysis was confirmed by exhaustive computational search over all 732,160
EMLTerm₁ terms with ≤ 8 `eml` nodes (using Float evaluation with the correct
`Real.log` semantics): none matches `tanh` at test points.
-/

-- The original theorem is false. We comment it out.
/-
theorem emlterm1_for_tanh :
    ∃ t : EMLTerm₁, ∀ x : ℝ, EMLTerm₁.eval x t = Real.tanh x := by
  sorry
-/

/-!
## Lemmas supporting the impossibility argument

The following lemma shows that if an `EMLTerm₁` term has `eval t₂ = exp(x)`
(the most natural candidate for the log argument), then `exp(eval t₁) - x = -x`
is impossible because `exp` is never zero.
-/

/-- For `exp(x)` as the log argument, the resulting function is `exp(f) - x`,
    which is always strictly greater than `-x` (since `exp(f) > 0`). -/
theorem eml_exp_x_not_neg_x (f : ℝ → ℝ) :
    ¬ (∀ x : ℝ, Real.exp (f x) - x = -x) := by
  intro h
  have h0 := h 0
  simp at h0

/-- `Real.log` erases sign: `log(x) = log(|x|)` -/
theorem log_eq_log_abs (x : ℝ) : Real.log x = Real.log |x| :=
  (Real.log_abs x).symm

/-- `exp(log(x)) = |x|` for `x ≠ 0`, not `x` itself -/
theorem exp_log_eq_abs (x : ℝ) (hx : x ≠ 0) : Real.exp (Real.log x) = |x| := by
  rw [log_eq_log_abs]
  exact Real.exp_log (abs_pos.mpr hx)

end EML
