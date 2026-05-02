import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import EML.Calc

namespace EML

/-- **Calc 3 → Calc 2** (Table 2, row 2 → row 3).

For every `Calc3` term `e` there exists a `Calc2` term `e'` whose
real-valued evaluation agrees with `e`'s.

**Translation strategy** (informal):
* `add a b ↦ a − (−b) = a − (0 − b)` — addition becomes subtraction.
* `neg a  ↦ 0 − a` — unary negation becomes subtraction.
* `inv a  ↦ exp (0 − ln a)`  — reciprocal becomes `exp(−ln a)`,
  valid for `a > 0`. Outside that domain Calc3's `inv` is the
  Mathlib convention `(0)⁻¹ = 0`, which the Calc2 image does not
  match; the translation is therefore equal on the natural domain
  of the operation. We state the lemma in the unrestricted
  existential form and let Aristotle either find a clever
  encoding (using `Real.log 0 = 0`) or expose the side condition.
* `exp_`, `ln_` translate as themselves.
* The constant `0` available everywhere via `varX − varX`.

Mathlib provides the identities `Real.log_inv`, `Real.exp_neg`, and
`Real.exp_log` (under positivity) needed for the proof.
-/
theorem calc3_to_calc2 :
    ∀ e : Calc3, ∃ e' : Calc2,
      ∀ x y : ℝ, Calc2.eval x y e' = Calc3.eval x y e := by
  sorry

end EML
