import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Partial real-function semantics

The paper's `eml(x, y) = exp(x) − ln(y)` operator is, on `ℝ`, a *partial*
function: it is only defined when `y > 0`. Mathlib's `Real.log` is a
*total* function returning the junk value `0` for `x ≤ 0`. To prevent
proofs that accidentally exploit `Real.log 0 = 0`, this module wraps
each partial primitive in `Option ℝ`, returning `none` exactly when
the operation is undefined under the paper's intended semantics.

The `?` suffix is the convention here: `Real.log?` is the partial
version of `Real.log`.

The total-eval bridge `eval?_eq_eval` (proved in `EMLPartial.lean`)
lets us reuse existing chunks (which use the total eval) as evidence
for the partial framework, without re-proving everything from scratch.
-/

namespace EML

/-- Partial natural exp: total, just lifted into `Option`.
`Real.exp x` is defined for every real `x`, so this never returns `none`. -/
@[simp] noncomputable def Real.exp? (x : ℝ) : Option ℝ :=
  some (_root_.Real.exp x)

/-- Partial natural log: defined only on the strictly positive reals.
Returns `none` for `x ≤ 0` instead of Mathlib's junk value `0`. -/
noncomputable def Real.log? (x : ℝ) : Option ℝ :=
  if 0 < x then some (_root_.Real.log x) else none

/-- `Real.log? x = some v` iff `x > 0` and `v = Real.log x`. -/
@[simp] lemma Real.log?_eq_some (x v : ℝ) :
    Real.log? x = some v ↔ 0 < x ∧ v = _root_.Real.log x := by
  unfold Real.log?
  by_cases h : 0 < x
  · simp [h]; exact ⟨fun e => e.symm, fun e => e.symm⟩
  · simp [h]

/-- `Real.log?` returns `some` exactly on the strictly positive reals. -/
lemma Real.log?_isSome_iff_pos (x : ℝ) :
    (Real.log? x).isSome ↔ 0 < x := by
  unfold Real.log?
  by_cases h : 0 < x <;> simp [h]

/-- On the positive reals, `Real.log?` equals the total `Real.log`. -/
lemma Real.log?_of_pos {x : ℝ} (hx : 0 < x) :
    Real.log? x = some (_root_.Real.log x) := by
  unfold Real.log?; simp [hx]

/-- Off the positive reals, `Real.log?` is undefined. -/
lemma Real.log?_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    Real.log? x = none := by
  unfold Real.log?; simp [not_lt.mpr hx]

end EML
