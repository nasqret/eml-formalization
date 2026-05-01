import EML.Basic

/-!
# Transcendental functions in EML form

Headline identity from Odrzywolek (arXiv:2603.21852), Section 3,
Identity 5: the natural logarithm expressed purely via `eml` and `1`.
-/

namespace EML

-- chunk 011 log_via_eml (Identity 5, the headline identity from section 3)
/-- Identity 5: `log z = eml(1, eml(eml(1, z), 1))` for `z > 0`. -/
theorem log_via_eml (z : ℝ) (hz : 0 < z) :
    Real.log z = EML.eml 1 (EML.eml (EML.eml 1 z) 1) := by sorry

end EML
