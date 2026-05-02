import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import EML.Calc

namespace EML

/-- **Calc 1 → Calc 0** (Table 2, row 4 → row 5).

For every `Calc1` term `e` there exists a `Calc0` term `e'` whose
real-valued evaluation agrees with `e`'s.

**Translation strategy** (informal):
* `varX` ↦ `varX`, `varY` ↦ `varY`.
* `eConst` ↦ `exp_ (logb varX varX)` since `logb x x = 1` for the
  Mathlib convention (and `exp 1 = e`). Note: `logb varX varX`
  evaluates to `Real.log x / Real.log x`, which is `1` whenever
  `Real.log x ≠ 0` (i.e. `x ≠ 0` and `x ≠ 1`); on the exceptional
  set Mathlib's junk values give `0/0 = 0`, so the equality
  `Calc0.eval x y (exp_ (logb varX varX)) = Real.exp 1` only holds
  on the natural domain. A more robust encoding would pick a
  closed term independent of `varX`; we leave the strategy choice
  to the prover.
* `logb a b` ↦ `logb a b` directly.
* `pow a b` ↦ `exp_ (logb (exp_ (inv b)) a)` where `inv b` is itself
  a Calc0 term evaluating to `1/b` via `logb (exp_ b) (exp_ 1)`,
  i.e. `ln(e^1) / ln(e^b) = 1/b`. Then
  `logb (exp_ (1/b)) a = ln a / (1/b) = b · ln a`, and
  `exp_ (b · ln a) = a^b`.

The translation is correct on the natural positivity domain of
the operations involved. -/
theorem calc1_to_calc0 :
    ∀ e : Calc1, ∃ e' : Calc0,
      ∀ x y : ℝ, Calc0.eval x y e' = Calc1.eval x y e := by
  sorry

end EML
