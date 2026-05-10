import Mathlib
import EML.Framework.Sheffer

/-!
# Plan E broadening — new NegEMLTermE / NegEMLTerm witnesses

## New witnesses found

Beyond the existing 5 sealed primitives, we produce the following
additional witnesses in the EReal-grammar and ℝ-grammar:

### EReal-grammar witnesses (`NegEMLTermE`)

6. **Zero** (`0 : EReal`): `app one_E minusInf` ≡ log(1) − exp(−∞) = 0 − 0 = 0
7. **log(x)** as EReal: `app var_E minusInf` ≡ log(x) − exp(−∞) = log(x)
8. **−exp(x)**: `app one_E var_E` ≡ log(1) − exp(x) = −exp(x)
9. **−e** (= −Real.exp 1): `app one_E one_E` ≡ log(1) − exp(1) = −e
10. **log(x) − e**: `app var_E one_E` ≡ log(x) − exp(1)
11. **log(x) − exp(x)**: `app var_E var_E` ≡ log(x) − exp(x)
12. **−1** (depth 2): `app one_E (app one_E minusInf)` ≡ 0 − exp(0) = −1
13. **−exp(−e)** (depth 2): `app one_E (app one_E one_E)` ≡ 0 − exp(−e)
14. **log(log(x))** (depth 2): `app (app var_E minusInf) minusInf`
15. **log(log(x)) − e** (depth 2): `app (app var_E minusInf) one_E`
16. **−exp(log(x))** = **−x** (for x > 0, depth 2): `app one_E (app var_E minusInf)`

### ℝ-grammar witnesses (`NegEMLTerm`)

17. **−e**: `app one one` ≡ log(1) − exp(1) = −e

## Structural obstructions

### Positive constants (e, π, 2, …) are unreachable

The grammar has a fundamental *sign barrier*: `negEml(a, b) = log(a) − exp(b)`.
Since `exp(b) ≥ 0` for all finite `b`, every application of `negEml` yields a value
`≤ log(a)`. Starting from atoms `{1, x, −∞}`:

* `log(1) = 0`, so `negEml(1, ·) ≤ 0`.
* `log(x)` can be positive (when `x > 1`), but it grows slowly.
* To get a *specific* positive constant `c > 0`, we'd need `log(a) ≥ c`,
  i.e., `a ≥ eᶜ`, which in turn requires `log(a') ≥ eᶜ`, etc.
  This creates an infinite regress of exponentially growing requirements
  that cannot be bootstrapped from finitely many applications of negEml
  starting from `{1, x, −∞}`.

Concretely, to express `e` as a *constant* (independent of `x`):
  `e = negEml(a, −∞) = log(a)` requires `a = eᵉ ≈ 15.15`.
  `eᵉ = negEml(a', −∞) = log(a')` requires `a' = exp(eᵉ) ≈ 3.8 × 10⁶`.
  This chain never terminates — the grammar cannot produce its own
  double-exponential tower.

**This obstruction also blocks `exp(x)` as a *grammar-definable function*.**
Getting `exp(x)` would require a term `t` with `eval t x = exp(x)` for all `x`.
By structural induction, `eval (app s u) x = log(eval s x) − exp(eval u x)`.
For this to equal `exp(x)`, we'd need `eval s x = exp(exp(x) + exp(eval u x))`,
which requires a double-exponential term — the same infinite regress.

### Addition and multiplication

The grammar provides only subtraction (via log − exp). There is no way to
form `a + b` or `a * b` in general:
* `a + b` would require `log(f) − exp(g) = a + b`, coupling both operands
  inside a single log or exp — impossible for independent `a, b`.
* `a * b` faces the same issue: `log` converts products to sums, but the
  subtracted `exp(g)` term prevents clean recovery.

### ⊤ (+∞) is unreachable

`logE(⊤) = ⊤` and `expE(⊤) = ⊤`, but `⊤` is not an atom and cannot be
produced: `negEmlE(x, y) = logE(x) − expE(y)`. Since `expE(y) ≥ 0`,
the result is `≤ logE(x)`. And `logE(x) = ⊤` only when `x = ⊤`,
which is itself unreachable. We prove this formally below.
-/

namespace EML

open EReal Real

/-! ## New EReal-grammar witnesses -/

/-- **Witness 6**: Zero in the EReal-grammar.
    `negEmlE(1, −∞) = log(1) − exp(−∞) = 0 − 0 = 0`. -/
theorem negEml_paper_claim_zero_E :
    NegEMLTermE.eval (.app .one_E .minusInf) = fun _ => (0 : EReal) := by
  ext x
  simp only [NegEMLTermE.eval, negEmlE, logE_coe, expE_bot]
  simp [Real.log_one]

/-- **Witness 7**: `log(x)` in the EReal-grammar.
    `negEmlE(x, −∞) = log(x) − exp(−∞) = log(x) − 0 = log(x)`. -/
theorem negEml_paper_claim_logx_E :
    NegEMLTermE.eval (.app .var_E .minusInf) =
      fun x => ((Real.log x : ℝ) : EReal) := by
  ext x
  simp only [NegEMLTermE.eval, negEmlE, logE_coe, expE_bot]
  simp

/-- **Witness 8**: `−exp(x)` in the EReal-grammar.
    `negEmlE(1, x) = log(1) − exp(x) = 0 − exp(x) = −exp(x)`. -/
theorem negEml_paper_claim_neg_exp_E :
    NegEMLTermE.eval (.app .one_E .var_E) =
      fun x => ((-(Real.exp x) : ℝ) : EReal) := by
  ext x
  simp only [NegEMLTermE.eval, negEmlE, logE_coe, expE_coe]
  simp [Real.log_one]

/-- **Witness 9**: `−e` (= −exp(1)) in the EReal-grammar.
    `negEmlE(1, 1) = log(1) − exp(1) = 0 − e = −e`. -/
theorem negEml_paper_claim_neg_e_E :
    NegEMLTermE.eval (.app .one_E .one_E) = fun _ => ((-(Real.exp 1) : ℝ) : EReal) := by
  ext x
  simp only [NegEMLTermE.eval, negEmlE, logE_coe, expE_coe]
  simp [Real.log_one]

/-- **Witness 10**: `log(x) − e` in the EReal-grammar.
    `negEmlE(x, 1) = log(x) − exp(1)`. -/
theorem negEml_paper_claim_logx_minus_e_E :
    NegEMLTermE.eval (.app .var_E .one_E) =
      fun x => ((Real.log x - Real.exp 1 : ℝ) : EReal) := by
  ext x
  simp only [NegEMLTermE.eval, negEmlE, logE_coe, expE_coe]
  rw [← EReal.coe_sub]

/-- **Witness 11**: `log(x) − exp(x)` in the EReal-grammar.
    `negEmlE(x, x) = log(x) − exp(x)`. -/
theorem negEml_paper_claim_logx_minus_expx_E :
    NegEMLTermE.eval (.app .var_E .var_E) =
      fun x => ((Real.log x - Real.exp x : ℝ) : EReal) := by
  ext x
  simp only [NegEMLTermE.eval, negEmlE, logE_coe, expE_coe]
  rw [← EReal.coe_sub]

/-- **Witness 12**: `−1` in the EReal-grammar (depth 2).
    `negEmlE(1, negEmlE(1, −∞)) = log(1) − exp(0) = 0 − 1 = −1`. -/
theorem negEml_paper_claim_neg_one_E :
    NegEMLTermE.eval (.app .one_E (.app .one_E .minusInf)) =
      fun _ => ((-1 : ℝ) : EReal) := by
  ext x
  simp only [NegEMLTermE.eval, negEmlE, logE_coe, expE_bot]
  simp [expE_zero_ereal]

/-- **Witness 13**: `−exp(−e)` in the EReal-grammar (depth 2).
    `negEmlE(1, negEmlE(1, 1)) = log(1) − exp(−e) = −exp(−e)`. -/
theorem negEml_paper_claim_neg_exp_neg_e_E :
    NegEMLTermE.eval (.app .one_E (.app .one_E .one_E)) =
      fun _ => ((-(Real.exp (-(Real.exp 1))) : ℝ) : EReal) := by
  ext x
  simp only [NegEMLTermE.eval, negEmlE, logE_coe, expE_coe]
  rw [Real.log_one, ← EReal.coe_sub, expE_coe, ← EReal.coe_sub]
  norm_num

/-- **Witness 14**: `log(log(x))` in the EReal-grammar (depth 2).
    `negEmlE(negEmlE(x, −∞), −∞) = log(log(x)) − exp(−∞) = log(log(x))`. -/
theorem negEml_paper_claim_log_log_x_E :
    NegEMLTermE.eval (.app (.app .var_E .minusInf) .minusInf) =
      fun x => ((Real.log (Real.log x) : ℝ) : EReal) := by
  ext x
  simp only [NegEMLTermE.eval, negEmlE, logE_coe, expE_bot]
  simp

/-- **Witness 15**: `log(log(x)) − e` in the EReal-grammar (depth 2).
    `negEmlE(negEmlE(x, −∞), 1) = log(log(x)) − exp(1)`. -/
theorem negEml_paper_claim_log_log_x_minus_e_E :
    NegEMLTermE.eval (.app (.app .var_E .minusInf) .one_E) =
      fun x => ((Real.log (Real.log x) - Real.exp 1 : ℝ) : EReal) := by
  ext x
  simp only [NegEMLTermE.eval, negEmlE, logE_coe, expE_bot, expE_coe]
  simp [← EReal.coe_sub]

/-
**Witness 16**: `−x` (depth 2, valid for all x via Mathlib's `Real.log` convention).
    `negEmlE(1, negEmlE(x, −∞)) = log(1) − exp(log(x)) = 0 − exp(log(x))`.
    When `x > 0`, `exp(log(x)) = x`, giving `−x`.
    When `x ≤ 0`, `Real.log x = 0`, so `exp(log(x)) = 1`, giving `−1`.
    We state the clean form for `x > 0`.
-/
theorem negEml_paper_claim_neg_x_E (x : ℝ) (hx : 0 < x) :
    NegEMLTermE.eval (.app .one_E (.app .var_E .minusInf)) x = ((-x : ℝ) : EReal) := by
  -- Unfold the definitions of `NegEMLTermE.eval` and `negEmlE`.
  simp [NegEMLTermE.eval, negEmlE];
  exact Real.exp_log hx

/-! ## ℝ-grammar additional witness -/

/-- **Witness 17**: `−e` in the ℝ-grammar.
    `negEml(1, 1) = log(1) − exp(1) = 0 − e = −e`. -/
theorem negEml_paper_claim_neg_e :
    NegEMLTerm.eval (.app .one .one) = fun _ => -(Real.exp 1) := by
  ext x
  simp [NegEMLTerm.eval, negEml, Real.log_one]

/-! ## Obstruction: ⊤ is unreachable from NegEMLTermE

Every `NegEMLTermE` term, when evaluated at a finite real `x`, produces
either `⊥` or a finite value — never `⊤`. -/

/-
Every NegEMLTermE term evaluates to a value `≠ ⊤` at any finite input.
-/
theorem negEmlTermE_eval_ne_top (t : NegEMLTermE) (x : ℝ) :
    t.eval x ≠ ⊤ := by
  induction' t with s t ih generalizing x;
  · exact EReal.coe_ne_top _;
  · exact Ne.symm (not_eq_of_beq_eq_false rfl);
  · exact bot_ne_top;
  · -- By definition of `eval`, we have `eval (app s t) x = logE (s.eval x) - expE (t.eval x)`.
    have h_eval : (s.app t).eval x = logE (s.eval x) - expE (t.eval x) := by
      rfl;
    cases h : s.eval x <;> cases h' : t.eval x <;> simp_all +decide;
    exact ne_of_lt ( EReal.coe_lt_top _ )

end EML