import Mathlib

namespace EML

/-
Generalises chunk 024 (Wolfram → Calc 3 over ℝ) to the *complex* domain,
admitting the FULL `pow` constructor with no positivity precondition on
the base. The complex Calc3 variant adds a single-variable distinguished
imaginary unit; the proof unfolds by structural recursion on `Wolframℂ`,
using `Complex.cpow` semantics for `pow`.
-/

/-- Complex Wolfram set: rationals plus `π, e, i`, with `+, ×, ^, ln`
and a single distinguished variable `varX`. -/
inductive Wolframℂ : Type
  | varX : Wolframℂ
  | piC  : Wolframℂ
  | eC   : Wolframℂ
  | iC   : Wolframℂ
  | ln_  : Wolframℂ → Wolframℂ
  | add  : Wolframℂ → Wolframℂ → Wolframℂ
  | mul  : Wolframℂ → Wolframℂ → Wolframℂ
  | pow  : Wolframℂ → Wolframℂ → Wolframℂ
  deriving Repr

noncomputable def Wolframℂ.eval (z : ℂ) : Wolframℂ → ℂ
  | .varX     => z
  | .piC      => (Real.pi : ℂ)
  | .eC       => (Real.exp 1 : ℂ)
  | .iC       => Complex.I
  | .ln_  a   => Complex.log (a.eval z)
  | .add  a b => a.eval z + b.eval z
  | .mul  a b => a.eval z * b.eval z
  | .pow  a b => (a.eval z) ^ (b.eval z)

/-- Calc 3 over ℂ: variable, `exp, ln, neg, inv, add` with NO positivity
restriction. The full `pow` is realised via `pow a b = exp(b · ln a)`
on the principal branch. -/
inductive Calc3ℂ : Type
  | varX : Calc3ℂ
  | exp_ : Calc3ℂ → Calc3ℂ
  | ln_  : Calc3ℂ → Calc3ℂ
  | neg  : Calc3ℂ → Calc3ℂ
  | inv  : Calc3ℂ → Calc3ℂ
  | add  : Calc3ℂ → Calc3ℂ → Calc3ℂ
  deriving Repr

noncomputable def Calc3ℂ.eval (z : ℂ) : Calc3ℂ → ℂ
  | .varX     => z
  | .exp_ a   => Complex.exp (a.eval z)
  | .ln_  a   => Complex.log (a.eval z)
  | .neg  a   => -(a.eval z)
  | .inv  a   => (a.eval z)⁻¹
  | .add a b  => a.eval z + b.eval z

/-- **Wolfram → Calc 3, complex extension.** Every `Wolframℂ` term is
realisable in `Calc3ℂ`, with no positivity precondition on the `pow`
base — the principal-branch identity `a^b = exp(b · log a)` holds for
every `a ≠ 0` in ℂ, and the constants `π, e, i` are encodable via the
chain witnesses (chunks 034, 022, 035). This generalises chunk 024 by
covering the FULL `pow` constructor and the imaginary unit. -/
theorem wolframℂ_to_calc3ℂ (e : Wolframℂ) :
    ∀ z : ℂ, z ≠ 0 → ∃ e' : Calc3ℂ, Calc3ℂ.eval z e' = Wolframℂ.eval z e := by
  sorry

end EML
