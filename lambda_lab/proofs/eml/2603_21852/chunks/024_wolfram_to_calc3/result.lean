import Mathlib

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

/-! ### Helper lemmas -/

/-- Calc3R can express zero: `x + (-x) = 0`. -/
lemma calc3R_express_zero (x y : ℝ) :
    Calc3R.eval x y (.add .varX (.neg .varX)) = 0 := by
  simp [Calc3R.eval]

/-- Calc3R can express one: `exp(x + (-x)) = exp(0) = 1`. -/
lemma calc3R_express_one (x y : ℝ) :
    Calc3R.eval x y (.exp_ (.add .varX (.neg .varX))) = 1 := by
  simp [Calc3R.eval, Real.exp_zero]

/-
Product of two positive reals via `exp(ln a + ln b)`.
-/
lemma exp_log_add_log {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.exp (Real.log a + Real.log b) = a * b := by
  rw [ Real.exp_add, Real.exp_log ha, Real.exp_log hb ]

/-
Given Calc3R expressions for v1 and v2, there exists one for v1 * v2.
    This uses sign case-analysis and the identity `a*b = exp(ln|a| + ln|b|)`.
-/
lemma calc3R_express_mul (x y : ℝ) (_hx : 0 < x) (_hy : 0 < y)
    (e1 e2 : Calc3R) :
    ∃ e3 : Calc3R,
      Calc3R.eval x y e3 = Calc3R.eval x y e1 * Calc3R.eval x y e2 := by
  by_cases h1 : 0 < Calc3R.eval x y e1;
  · by_cases h2 : 0 < Calc3R.eval x y e2;
    · use .exp_ (.add (.ln_ e1) (.ln_ e2));
      convert exp_log_add_log h1 h2 using 1;
    · by_cases h3 : Calc3R.eval x y e2 = 0;
      · exact ⟨ .add .varX (.neg .varX), by simp +decide [ h3, calc3R_express_zero ] ⟩;
      · use .neg (.exp_ (.add (.ln_ e1) (.ln_ (.neg e2))));
        simp_all +decide [ Calc3R.eval ];
        rw [ Real.exp_add, Real.exp_log h1, Real.exp_log_eq_abs, abs_of_nonpos ] <;> cases lt_or_gt_of_ne h3 <;> linarith;
  · by_cases h2 : 0 < Calc3R.eval x y e2;
    · by_cases h3 : Calc3R.eval x y e1 < 0;
      · use .neg (.exp_ (.add (.ln_ (.neg e1)) (.ln_ e2)));
        simp +decide [ Calc3R.eval, Real.exp_add, Real.exp_log, h2 ];
        rw [ Real.exp_log_eq_abs, abs_of_neg ] <;> linarith;
      · grind +suggestions;
    · by_cases h3 : 0 < -Calc3R.eval x y e1;
      · by_cases h4 : 0 < -Calc3R.eval x y e2;
        · use .exp_ (.add (.ln_ (.neg e1)) (.ln_ (.neg e2)));
          simp_all +decide [ Calc3R.eval ];
          rw [ Real.exp_add, Real.exp_log_eq_abs, Real.exp_log_eq_abs ] <;> cases abs_cases ( Calc3R.eval x y e1 ) <;> cases abs_cases ( Calc3R.eval x y e2 ) <;> nlinarith;
        · norm_num [ show Calc3R.eval x y e2 = 0 by linarith ] at *;
          exact ⟨ .add .varX ( .neg .varX ), calc3R_express_zero x y ⟩;
      · norm_num [ show Calc3R.eval x y e1 = 0 by linarith ] at *;
        exact ⟨ .add .varX ( .neg .varX ), by simp +decide [ Calc3R.eval ] ⟩

/-
Given Calc3R expressions for v1 > 0 and v2, there exists one for v1 ^ v2
    (real power with positive base). Uses `v1^v2 = exp(log(v1)*v2)`.
-/
lemma calc3R_express_rpow_pos (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (e1 e2 : Calc3R) (h1 : 0 < Calc3R.eval x y e1) :
    ∃ e3 : Calc3R,
      Calc3R.eval x y e3 = (Calc3R.eval x y e1) ^ (Calc3R.eval x y e2) := by
  -- Use `calc3R_express_mul` for steps following `h_mul`
  obtain ⟨e_prod, h_prod⟩ : ∃ e_prod : Calc3R,
       (Calc3R.eval x y e_prod) = (Real.log (Calc3R.eval x y e1)) * (Calc3R.eval x y e2) := by
         convert calc3R_express_mul x y hx hy _ _ using 1;
         rotate_left;
         exact .ln_ e1;
         exact e2;
         rfl;
  exact ⟨ Calc3R.exp_ e_prod, by rw [ Calc3R.eval ] ; rw [ h_prod, Real.rpow_def_of_pos h1 ] ⟩

/-
For zero base: 0^v = 0 if v ≠ 0, and 0^0 = 1. Both are Calc3R-expressible.
-/
lemma calc3R_express_rpow_zero (x y : ℝ) (_hx : 0 < x) (_hy : 0 < y)
    (e2 : Calc3R) :
    ∃ e3 : Calc3R,
      Calc3R.eval x y e3 = (0 : ℝ) ^ (Calc3R.eval x y e2) := by
  -- By definition of Calc3R.eval, we can rewrite the goal using the definition of exponentiation.
  by_cases h : Calc3R.eval x y e2 = 0 <;> simp_all +decide;
  · exact ⟨ _, calc3R_express_one x y ⟩;
  · exact ⟨ .add .varX ( .neg .varX ), by simp +decide [ Calc3R.eval ] ⟩

/-- For negative base: x^y = exp(log x * y) * cos(y * π).
    This involves cos and π, which have no Calc3R primitives.
    We leave this as sorry — it is not provable in general. -/
lemma calc3R_express_rpow_neg (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (e1 e2 : Calc3R) (h1 : Calc3R.eval x y e1 < 0) :
    ∃ e3 : Calc3R,
      Calc3R.eval x y e3 = (Calc3R.eval x y e1) ^ (Calc3R.eval x y e2) := by
  sorry

/-
Unprovable: requires expressing cos(v₂ · π) in Calc3R

Translate a constant-free real-valued Wolfram term into Calc3R for
positive inputs. The witness is constructed by recursive descent, using
the identities `mul a b = exp(ln a + ln b)` and `pow a b = exp(b · ln a)`.
-/
theorem wolframRNC_to_calc3R (e : WolframRNC) :
    ∀ x y : ℝ, 0 < x → 0 < y →
      ∃ e' : Calc3R, Calc3R.eval x y e' = WolframRNC.eval x y e := by
  intro x y hx hy;
  induction' e with a b ih_a ih_b;
  exact ⟨ .varX, rfl ⟩;
  · exact ⟨ .varY, rfl ⟩;
  · exact ⟨ .ln_ b.choose, by rw [ Calc3R.eval ] ; exact congr_arg Real.log b.choose_spec ⟩;
  · rename_i h₁ h₂;
    exact ⟨ Calc3R.add h₁.choose h₂.choose, by rw [ Calc3R.eval, h₁.choose_spec, h₂.choose_spec ] ; rfl ⟩;
  · rename_i a b ha hb;
    obtain ⟨ e₁, he₁ ⟩ := ha; obtain ⟨ e₂, he₂ ⟩ := hb; obtain ⟨ e₃, he₃ ⟩ := calc3R_express_mul x y hx hy e₁ e₂; use e₃; aesop;
  · rename_i a b ha hb;
    obtain ⟨ e₁, he₁ ⟩ := ha
    obtain ⟨ e₂, he₂ ⟩ := hb
    by_cases h₁ : 0 < Calc3R.eval x y e₁;
    · exact calc3R_express_rpow_pos x y hx hy e₁ e₂ h₁ |> fun ⟨ e₃, he₃ ⟩ => ⟨ e₃, by aesop ⟩;
    · by_cases h₂ : Calc3R.eval x y e₁ < 0;
      · exact calc3R_express_rpow_neg x y hx hy e₁ e₂ h₂ |> fun ⟨ e₃, he₃ ⟩ => ⟨ e₃, by aesop ⟩;
      · -- Since $a$ is not positive and not negative, it must be zero.
        have h_zero : WolframRNC.eval x y a = 0 := by
          linarith;
        obtain ⟨ e₃, he₃ ⟩ := calc3R_express_rpow_zero x y hx hy e₂; use e₃; simp_all +decide [ WolframRNC.eval ] ;

end EML
