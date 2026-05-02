import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import EML.Calc

namespace EML

/-- **Calc 2 → Calc 1** (Table 2, row 3 → row 4).

For every `Calc2` term `e` there exists a `Calc1` term `e'` whose
real-valued evaluation agrees with `e`'s.

**Translation strategy** (informal):
* `exp_ a ↦ pow eConst a`        — `exp(a) = e^a`.
* `ln_  a ↦ logb eConst a`       — `ln(a) = log_e(a)`.
* `sub a b` is the substantive step. Using `ln (e^a / e^b) = a − b`
  and Calc1's `logb` (which divides logarithms), one route is:
  `sub a b = logb (pow eConst b) (pow eConst a)` evaluates to
  `ln(e^a) / ln(e^b) = a / b`, i.e. division — not subtraction.
  A genuine subtraction route uses logarithm identities of the form
  `a − b = log_e ((e^a)^1 · (e^b)^{−1})`, which requires
  multiplication and a `−1` constant. Both are constructible in
  Calc1 only via repeated tower applications of `pow` and `logb`,
  exploiting Mathlib's junk-value conventions (`Real.log 0 = 0`,
  `(0 : ℝ)⁻¹ = 0`). The proof is delicate — we leave a `sorry`
  and submit to Aristotle for a constructive translation. -/
theorem calc2_to_calc1 :
    ∀ e : Calc2, ∃ e' : Calc1,
      ∀ x y : ℝ, Calc1.eval x y e' = Calc2.eval x y e := by
  sorry

end EML
