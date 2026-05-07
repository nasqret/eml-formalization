import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Partial complex-function semantics

The complex EML operator `eml(z, w) = exp(z) − Complex.log(w)` is
*partial*: `Complex.log w` is defined as `log |w| + i · arg w` for
`w ≠ 0` and as the junk value `0` for `w = 0`. To prevent proofs that
accidentally exploit `Complex.log 0 = 0`, this module wraps each
partial primitive in `Option ℂ`.

Two crucial domain facts beyond non-zero:

* `Complex.log_exp z = z` only when `z.im ∈ (-π, π]`. This is the
  principal-branch invariant.
* `Complex.exp_log w = w` for any `w ≠ 0` (no branch restriction).

Builders that compose `log` with a witness whose `.im` could fall
outside `(-π, π]` need to bookkeep this — typically by proving the
witness's imaginary part stays in that range.
-/

namespace EML

/-- Partial complex exp: total, lifted into `Option`. -/
@[simp] noncomputable def Complex.exp? (z : ℂ) : Option ℂ :=
  some (_root_.Complex.exp z)

/-- Partial complex log: defined for `z ≠ 0`, returning Mathlib's
principal-branch `Complex.log`. Returns `none` at `z = 0` instead of
the junk value. -/
noncomputable def Complex.log? (z : ℂ) : Option ℂ :=
  if z = 0 then none else some (_root_.Complex.log z)

/-- `Complex.log? z = some v` iff `z ≠ 0` and `v = Complex.log z`. -/
@[simp] lemma Complex.log?_eq_some (z v : ℂ) :
    Complex.log? z = some v ↔ z ≠ 0 ∧ v = _root_.Complex.log z := by
  unfold Complex.log?
  by_cases h : z = 0
  · simp [h]
  · simp [h]; exact ⟨fun e => e.symm, fun e => e.symm⟩

/-- `Complex.log?` returns `some` exactly on the non-zero complex numbers. -/
lemma Complex.log?_isSome_iff_ne (z : ℂ) :
    (Complex.log? z).isSome ↔ z ≠ 0 := by
  unfold Complex.log?
  by_cases h : z = 0 <;> simp [h]

/-- On the non-zeros, `Complex.log?` equals the total `Complex.log`. -/
lemma Complex.log?_of_ne {z : ℂ} (hz : z ≠ 0) :
    Complex.log? z = some (_root_.Complex.log z) := by
  unfold Complex.log?; simp [hz]

/-- At `z = 0`, `Complex.log?` is undefined. -/
lemma Complex.log?_of_zero : Complex.log? (0 : ℂ) = none := by
  unfold Complex.log?; simp

end EML
