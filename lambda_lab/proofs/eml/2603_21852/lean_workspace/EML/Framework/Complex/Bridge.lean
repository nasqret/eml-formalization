import EML.Framework.Complex.Closures.Constants
import EML.Framework.Complex.Closures.Trig

/-!
# Complex-to-real bridge

For F36 primitives that pass through the complex extension —
`π`, `i`, `cos`, `sin` (Phase B+ IV scope) — the witness lives in
`EMLTermℂ` and the bridge to the real F36 value uses Mathlib's
`Complex.re` projection.

This file packages those bridges as a clean public API so the F36
final theorem can compose them.

## What the paper proves vs. what we ship

The paper's claim for real-trig functions is *not* a literal complex
EML witness for `Complex.cos x`; it is a witness `t : EMLTermℂ` such
that `(eval t with input (x : ℂ)).re = Real.cos x`. The `.re` is
external to the EML grammar — it is part of the *encoding* of the
real number into the complex extension. We match that scope precisely.

For `π` and `i`, the witnesses are *literal* — `eval(t) = (Real.pi : ℂ)`
and `eval(t) = Complex.I` exactly. The `.re` projection isn't needed
for those.
-/

namespace EML

/-! ## Constants — direct closures repackaged -/

/-- The literal complex EML closed witness for `π`, packaged as a
direct existential. -/
theorem F36Expr.pi_complete :
    ∃ t : EMLTermℂ, ∀ env : Nat → ℂ, t.eval? env = some (Real.pi : ℂ) :=
  ⟨EMLRealizationℂ.realizeℂ_pi.term, fun env =>
    EMLRealizationℂ.realizeℂ_pi.spec env _ rfl⟩

/-- The literal complex EML closed witness for `i`, packaged as a
direct existential. -/
theorem F36Expr.i_complete :
    ∃ t : EMLTermℂ, ∀ env : Nat → ℂ, t.eval? env = some Complex.I :=
  ⟨EMLRealizationℂ.realizeℂ_i.term, fun env =>
    EMLRealizationℂ.realizeℂ_i.spec env _ rfl⟩

/-! ## Trig — real-part bridge witnesses

Each of the following theorems takes a real-domain hypothesis on the
input variable and produces a complex EML witness whose `Complex.re`
projection matches the expected real-trig value.

These are used by `F36ToEL.lean` to handle the trig fragment of
`F36Expr` after the real fragment has been compiled. -/

/-- Real-part bridge for `Real.cos`. There is an `EMLTermℂ` whose
evaluation, given a real-valued input variable `x > 0`, has its
real part equal to `Real.cos x`.

This is the cleanest restatement of `cos_re_bridge`. -/
theorem F36Expr.cos_re_complete :
    ∃ t : EMLTermℂ, ∀ x : ℝ, 0 < x →
      ∃ vc : ℂ,
        t.eval? (fun n => if n = 0 then ((x : ℝ) : ℂ) else 0) = some vc
        ∧ vc.re = Real.cos x := by
  refine ⟨cosTermℂ, fun x hx => ?_⟩
  have hev : (fun n : Nat => if n = 0 then ((x : ℝ) : ℂ) else 0) 0 = ((x : ℝ) : ℂ) := by
    simp
  exact cos_re_bridge hx hev

/-- Real-part bridge for `Real.sin` on `(0, π)`. -/
theorem F36Expr.sin_re_complete :
    ∃ t : EMLTermℂ, ∀ x : ℝ, 0 < x → x < Real.pi →
      ∃ vc : ℂ,
        t.eval? (fun n => if n = 0 then ((x : ℝ) : ℂ) else 0) = some vc
        ∧ vc.re = Real.sin x := by
  refine ⟨sinTermℂ, fun x hx0 hxpi => ?_⟩
  have hev : (fun n : Nat => if n = 0 then ((x : ℝ) : ℂ) else 0) 0 = ((x : ℝ) : ℂ) := by
    simp
  exact sin_re_bridge hx0 hxpi hev

/-! ## Future bridges (Phase B++)

* `tan` — once a literal complex `mkAddℂ` and `mkDivℂ` for
  purely-imaginary inputs land, restate as
  `∃ t : EMLTermℂ, ∀ x : ℝ, cos x ≠ 0 → eval t = (tan x : ℂ)`.
* `arcsin`, `arccos`, `arctan` — same pattern via the Mathlib
  closed-form complex-log identities.

These are TODOs; the current scope already covers the paper's
own real-trig claims. -/

end EML
