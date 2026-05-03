import Mathlib

namespace EML

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
restriction. -/
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

/-! ## Key facts used in constant encodings -/

private lemma piI_ne_zero : ↑Real.pi * Complex.I ≠ (0 : ℂ) :=
  mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero

private lemma two_inv_ne_zero : (2 : ℂ)⁻¹ ≠ 0 := by norm_num

private lemma neg_I_ne_zero : (-Complex.I : ℂ) ≠ 0 := by
  simp [Complex.I_ne_zero]

/-
exp(πi/2) = i.
-/
private lemma exp_piI_div2 :
    Complex.exp (↑Real.pi * Complex.I * (2 : ℂ)⁻¹) = Complex.I := by
  norm_num [ mul_div, Complex.ext_iff, Complex.exp_re, Complex.exp_im ]

/-- πi * (-i) = π. -/
private lemma piI_mul_negI :
    ↑Real.pi * Complex.I * (-Complex.I) = (↑Real.pi : ℂ) := by
  ring_nf; simp [Complex.I_sq]

/-! ## The main theorem -/

/-
**Wolfram → Calc 3, complex extension.** Every `Wolframℂ` term is
realisable in `Calc3ℂ`, with no positivity precondition on the `pow`
base.
-/
theorem wolframℂ_to_calc3ℂ (e : Wolframℂ) :
    ∀ z : ℂ, z ≠ 0 → ∃ e' : Calc3ℂ, Calc3ℂ.eval z e' = Wolframℂ.eval z e := by
  intro z hz;
  induction' e with e ih generalizing z;
  all_goals norm_num [ Wolframℂ.eval ];
  exact ⟨ Calc3ℂ.varX, rfl ⟩;
  have h_pi : ∃ e' : Calc3ℂ, Calc3ℂ.eval z e' = Real.pi := by
    have h_piI : ∃ e' : Calc3ℂ, Calc3ℂ.eval z e' = Real.pi * Complex.I := by
      -- Let's choose the Calc3ℂ term that evaluates to πi.
      use Calc3ℂ.ln_ (Calc3ℂ.neg (Calc3ℂ.exp_ (Calc3ℂ.add (Calc3ℂ.neg (Calc3ℂ.varX)) (Calc3ℂ.varX))));
      simp_all +decide [ Calc3ℂ.eval ];
      exact Complex.log_neg_one
    obtain ⟨ e', he' ⟩ := h_piI;
    obtain ⟨e'', he''⟩ : ∃ e'' : Calc3ℂ, e''.eval z = -Complex.I := by
      obtain ⟨e'', he''⟩ : ∃ e'' : Calc3ℂ, e''.eval z = Complex.I := by
        use .exp_ (.exp_ (.add (.ln_ e') (.ln_ (.inv (.add (.exp_ (.add (.neg (.exp_ (.varX))) (.exp_ (.varX))) ) (.exp_ (.add (.neg (.exp_ (.varX))) (.exp_ (.varX))) ) ) ) ) ) ) ; simp_all +decide [ Calc3ℂ.eval ] ; (
        rw [ Complex.exp_add, Complex.exp_log, Complex.exp_log ] <;> norm_num [ Complex.ext_iff, Real.pi_ne_zero ];
        norm_num [ Complex.exp_re, Complex.exp_im, mul_div ])
      generalize_proofs at *; (
      exact ⟨ Calc3ℂ.inv e'', by simp +decide [ he'', Calc3ℂ.eval ] ⟩)
    generalize_proofs at *; (
    use .exp_ (.add (.ln_ e') (.ln_ e''));
    simp_all +decide [ Calc3ℂ.eval ];
    rw [ Complex.exp_add, Complex.exp_log, Complex.exp_log ] <;> norm_num [ Complex.ext_iff, Real.pi_ne_zero ]);
  exact h_pi;
  exact ⟨ Calc3ℂ.exp_ ( Calc3ℂ.exp_ ( Calc3ℂ.add ( Calc3ℂ.neg ( Calc3ℂ.varX ) ) ( Calc3ℂ.varX ) ) ), by simp +decide [ Calc3ℂ.eval ] ⟩;
  · -- Let's choose the encoding for $i$.
    use .exp_ (.exp_ (.add (.ln_ (.ln_ (.neg (.exp_ (.add (.neg .varX) .varX))))) (.ln_ (.inv (.add (.exp_ (.add (.neg .varX) .varX)) (.exp_ (.add (.neg .varX) .varX)))))));
    simp +decide [ Calc3ℂ.eval ];
    norm_num [ Complex.log, Complex.ext_iff, Complex.exp_re, Complex.exp_im ];
    norm_num [ Complex.arg ] ; ring_nf ; norm_num [ Real.exp_add, Real.exp_neg, Real.exp_log, Real.pi_pos ];
    norm_num [ abs_of_pos Real.pi_pos, mul_div, Real.pi_ne_zero ];
  · obtain ⟨ e', he' ⟩ := ih z hz; exact ⟨ Calc3ℂ.ln_ e', by simp +decide [ he', Calc3ℂ.eval ] ⟩ ;
  · rename_i a b ha hb;
    obtain ⟨ e₁, he₁ ⟩ := ha z hz; obtain ⟨ e₂, he₂ ⟩ := hb z hz; exact ⟨ Calc3ℂ.add e₁ e₂, by simp +decide [ he₁, he₂, Calc3ℂ.eval ] ⟩ ;
  · rename_i a b ha hb;
    by_cases ha0 : Wolframℂ.eval z a = 0;
    · exact ⟨ Calc3ℂ.add ( Calc3ℂ.neg ( Calc3ℂ.varX ) ) ( Calc3ℂ.varX ), by simp +decide [ ha0, Calc3ℂ.eval ] ⟩;
    · by_cases hb0 : Wolframℂ.eval z b = 0;
      · exact ⟨ Calc3ℂ.add ( Calc3ℂ.neg ( Calc3ℂ.varX ) ) ( Calc3ℂ.varX ), by simp +decide [ hb0, Calc3ℂ.eval ] ⟩;
      · obtain ⟨ e', he' ⟩ := ha z hz
        obtain ⟨ f', hf' ⟩ := hb z hz
        use Calc3ℂ.exp_ (Calc3ℂ.add (Calc3ℂ.ln_ e') (Calc3ℂ.ln_ f'));
        simp +decide [ *, Calc3ℂ.eval ];
        rw [ Complex.exp_add, Complex.exp_log ha0, Complex.exp_log hb0 ];
  · rename_i a b ha hb;
    by_cases ha0 : Wolframℂ.eval z a = 0;
    · by_cases hb0 : Wolframℂ.eval z b = 0 <;> simp_all +decide [ Complex.cpow_def ];
      · exact ⟨ Calc3ℂ.exp_ ( Calc3ℂ.add ( Calc3ℂ.neg ( Calc3ℂ.varX ) ) ( Calc3ℂ.varX ) ), by simp +decide [ Calc3ℂ.eval ] ⟩;
      · exact ⟨ Calc3ℂ.add ( Calc3ℂ.neg ( Calc3ℂ.varX ) ) ( Calc3ℂ.varX ), by simp +decide [ Calc3ℂ.eval ] ⟩;
    · by_cases hb0 : Wolframℂ.eval z b = 0;
      · simp_all +decide;
        exact ⟨ Calc3ℂ.exp_ ( Calc3ℂ.add ( Calc3ℂ.neg ( Calc3ℂ.varX ) ) ( Calc3ℂ.varX ) ), by simp +decide [ Calc3ℂ.eval ] ⟩;
      · obtain ⟨ e', he' ⟩ := ha z hz
        obtain ⟨ f', hf' ⟩ := hb z hz;
        by_cases hlog : Complex.log (Wolframℂ.eval z a) = 0;
        · have h_exp : Wolframℂ.eval z a = 1 := by
            rw [ ← Complex.exp_log ha0, hlog, Complex.exp_zero ];
          exact ⟨ Calc3ℂ.exp_ ( Calc3ℂ.add ( Calc3ℂ.neg ( Calc3ℂ.varX ) ) ( Calc3ℂ.varX ) ), by simp +decide [ h_exp, Calc3ℂ.eval ] ⟩;
        · use Calc3ℂ.exp_ (Calc3ℂ.exp_ (Calc3ℂ.add (Calc3ℂ.ln_ (Calc3ℂ.ln_ e')) (Calc3ℂ.ln_ f')));
          simp +decide [ *, Calc3ℂ.eval ];
          rw [ Complex.exp_add, Complex.exp_log hlog, Complex.exp_log hb0, Complex.cpow_def_of_ne_zero ha0 ]

end EML