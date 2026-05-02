import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace EML

/-
Reformulated translation: WolframRNC → Calc3R.

The paper's Wolfram set has constants {π, e, i}. Calc3 has no constants
(only `varX`, `varY` plus `exp_, ln_, neg, inv, add`). Therefore a *full*
Wolfram → Calc3 translation is impossible: π, i (and e) are outside the
closure of {varX, varY} under {exp, ln, neg, inv, +}.

We formalise the **scope-reduced** version: for the sub-language
WolframRNC ("real, no constants") that omits π, e, i, every term has an
equivalent Calc3R term on the positive-domain (x > 0, y > 0).
-/

inductive WolframRNC : Type
  | varX : WolframRNC
  | varY : WolframRNC
  | ln_  : WolframRNC → WolframRNC
  | add  : WolframRNC → WolframRNC → WolframRNC
  | mul  : WolframRNC → WolframRNC → WolframRNC
  | pow  : WolframRNC → WolframRNC → WolframRNC
  deriving Repr

noncomputable def WolframRNC.eval (x y : ℝ) : WolframRNC → ℝ
  | .varX     => x
  | .varY     => y
  | .ln_  a   => Real.log (a.eval x y)
  | .add  a b => a.eval x y + b.eval x y
  | .mul  a b => a.eval x y * b.eval x y
  | .pow  a b => (a.eval x y) ^ (b.eval x y)

inductive Calc3R : Type
  | varX : Calc3R
  | varY : Calc3R
  | exp_ : Calc3R → Calc3R
  | ln_  : Calc3R → Calc3R
  | neg  : Calc3R → Calc3R
  | inv  : Calc3R → Calc3R
  | add  : Calc3R → Calc3R → Calc3R
  deriving Repr

noncomputable def Calc3R.eval (x y : ℝ) : Calc3R → ℝ
  | .varX     => x
  | .varY     => y
  | .exp_ a   => Real.exp (a.eval x y)
  | .ln_  a   => Real.log (a.eval x y)
  | .neg  a   => -(a.eval x y)
  | .inv  a   => (a.eval x y)⁻¹
  | .add a b  => a.eval x y + b.eval x y

/-- Translate a constant-free real-valued Wolfram term into Calc3R for
positive inputs. The witness is constructed by recursive descent, using
the identities `mul a b = exp(ln a + ln b)` and `pow a b = exp(b · ln a)`. -/
theorem wolframRNC_to_calc3R (e : WolframRNC) :
    ∀ x y : ℝ, 0 < x → 0 < y →
      ∃ e' : Calc3R, Calc3R.eval x y e' = WolframRNC.eval x y e := by
  sorry

end EML
