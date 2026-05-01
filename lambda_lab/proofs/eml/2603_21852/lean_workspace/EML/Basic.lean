import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# EML core operator

This module defines the EML (Exp-Minus-Log) binary operator from
Odrzywolek (arXiv:2603.21852), together with the EDL and negated-EML
variants. Everything is over the real numbers; complex-valued versions
are deferred. The trivial unfolding lemmas live alongside the
definitions and are intended as building blocks for the auto-formalized
chunks under `EML.Solutions`.
-/

namespace EML

/-- The EML operator: `eml(x, y) = exp(x) - log(y)`. -/
noncomputable def eml (x y : ℝ) : ℝ := Real.exp x - Real.log y

/-- The EDL variant: `edl(x, y) = exp(x) / log(y)`. -/
noncomputable def edl (x y : ℝ) : ℝ := Real.exp x / Real.log y

/-- The negated-EML variant: `negEml(x, y) = log(x) - exp(y) = -eml(y, x)`. -/
noncomputable def negEml (x y : ℝ) : ℝ := Real.log x - Real.exp y

variable (x y : ℝ)

/-- Definitional unfolding of `eml`. -/
lemma eml_def : eml x y = Real.exp x - Real.log y := rfl

/-- Setting the second argument to 1 collapses `eml` to `exp`. -/
lemma eml_x_one : eml x 1 = Real.exp x := by simp [eml]

end EML
