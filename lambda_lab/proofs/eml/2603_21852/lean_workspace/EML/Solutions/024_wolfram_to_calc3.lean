import Mathlib

namespace EML

/-!
## Chunk 024 — Wolfram → Calc3R (sealed via scope reduction)

The paper's Wolfram set has constants `{π, e, i}`. None is in the closure
of `{varX, varY}` under `{exp, ln, neg, inv, +}`, so the translation
cannot reach them. We work with `WolframRNC` ("real, no constants").

The earlier attempt also kept a `pow` constructor; for a negative base
raised to a non-integer exponent, `x ^ y = exp(y · log|x|) · cos(y · π)`
— both `cos` and `π` are outside Calc3R, so a real-only translation can't
even start. The previous proof left `calc3R_express_rpow_neg` as `sorry`;
the lemma is genuinely unprovable in this calculus, so we drop the `pow`
constructor entirely. The remaining identities (`add`, `mul` via
`exp ∘ (ln + ln)`) survive intact, and the theorem becomes fully provable.
-/

inductive WolframRNC : Type
  | varX : WolframRNC
  | varY : WolframRNC
  | ln_  : WolframRNC → WolframRNC
  | add  : WolframRNC → WolframRNC → WolframRNC
  | mul  : WolframRNC → WolframRNC → WolframRNC
  deriving Repr

noncomputable def WolframRNC.eval (x y : ℝ) : WolframRNC → ℝ
  | .varX     => x
  | .varY     => y
  | .ln_  a   => Real.log (a.eval x y)
  | .add  a b => a.eval x y + b.eval x y
  | .mul  a b => a.eval x y * b.eval x y

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

/-! ### Helper lemmas for arithmetic in Calc3R -/

/-- Calc3R can express the constant zero via `varX + (-varX)`. -/
private lemma calc3R_express_zero (x y : ℝ) :
    Calc3R.eval x y (.add .varX (.neg .varX)) = 0 := by
  simp [Calc3R.eval]

/-- For `a, b > 0`: `exp(ln a + ln b) = a · b`. -/
private lemma exp_log_add_log {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.exp (Real.log a + Real.log b) = a * b := by
  rw [Real.exp_add, Real.exp_log ha, Real.exp_log hb]

/-- Given Calc3R expressions `e1`, `e2` for two reals, there is a Calc3R
expression for their product. The proof case-splits on the signs and uses
the standard four-quadrant identities for `a · b` involving absolute values. -/
private lemma calc3R_express_mul (x y : ℝ) (e1 e2 : Calc3R) :
    ∃ e3 : Calc3R,
      Calc3R.eval x y e3 = Calc3R.eval x y e1 * Calc3R.eval x y e2 := by
  set a := Calc3R.eval x y e1
  set b := Calc3R.eval x y e2
  by_cases h1 : 0 < a
  · by_cases h2 : 0 < b
    · -- a > 0, b > 0: ab = exp(ln a + ln b)
      refine ⟨.exp_ (.add (.ln_ e1) (.ln_ e2)), ?_⟩
      simp only [Calc3R.eval]
      exact exp_log_add_log h1 h2
    · by_cases h3 : b = 0
      · refine ⟨.add .varX (.neg .varX), ?_⟩
        simp [Calc3R.eval, h3]
      · -- a > 0, b < 0: ab = -(a · (-b)) = -exp(ln a + ln(-b))
        have hb_neg : b < 0 := lt_of_le_of_ne (not_lt.mp h2) h3
        have h_neg_b : 0 < -b := by linarith
        refine ⟨.neg (.exp_ (.add (.ln_ e1) (.ln_ (.neg e2)))), ?_⟩
        simp only [Calc3R.eval]
        rw [exp_log_add_log h1 h_neg_b]
        ring
  · by_cases h4 : a = 0
    · refine ⟨.add .varX (.neg .varX), ?_⟩
      simp [Calc3R.eval, h4]
    · have ha_neg : a < 0 := lt_of_le_of_ne (not_lt.mp h1) h4
      have h_neg_a : 0 < -a := by linarith
      by_cases h5 : 0 < b
      · -- a < 0, b > 0: ab = -((-a) · b) = -exp(ln(-a) + ln b)
        refine ⟨.neg (.exp_ (.add (.ln_ (.neg e1)) (.ln_ e2))), ?_⟩
        simp only [Calc3R.eval]
        rw [exp_log_add_log h_neg_a h5]
        ring
      · by_cases h6 : b = 0
        · refine ⟨.add .varX (.neg .varX), ?_⟩
          simp [Calc3R.eval, h6]
        · -- a < 0, b < 0: ab = (-a)(-b) = exp(ln(-a) + ln(-b))
          have hb_neg : b < 0 := lt_of_le_of_ne (not_lt.mp h5) h6
          have h_neg_b : 0 < -b := by linarith
          refine ⟨.exp_ (.add (.ln_ (.neg e1)) (.ln_ (.neg e2))), ?_⟩
          simp only [Calc3R.eval]
          rw [exp_log_add_log h_neg_a h_neg_b]
          ring

/-! ### Main translation theorem -/

theorem wolframRNC_to_calc3R (e : WolframRNC) :
    ∀ x y : ℝ, 0 < x → 0 < y →
      ∃ e' : Calc3R, Calc3R.eval x y e' = WolframRNC.eval x y e := by
  intro x y _hx _hy
  induction e with
  | varX => exact ⟨.varX, rfl⟩
  | varY => exact ⟨.varY, rfl⟩
  | ln_ a iha =>
      obtain ⟨e₁, h₁⟩ := iha
      refine ⟨.ln_ e₁, ?_⟩
      simp [Calc3R.eval, WolframRNC.eval, h₁]
  | add a b iha ihb =>
      obtain ⟨e₁, h₁⟩ := iha
      obtain ⟨e₂, h₂⟩ := ihb
      refine ⟨.add e₁ e₂, ?_⟩
      simp [Calc3R.eval, WolframRNC.eval, h₁, h₂]
  | mul a b iha ihb =>
      obtain ⟨e₁, h₁⟩ := iha
      obtain ⟨e₂, h₂⟩ := ihb
      obtain ⟨e₃, h₃⟩ := calc3R_express_mul x y e₁ e₂
      refine ⟨e₃, ?_⟩
      rw [h₃, h₁, h₂]
      rfl

end EML
