import Mathlib

/-!
# Polynomial-binary impossibility — paper §5 / GPT Pro #4 frontier

The headline result: no single bivariate polynomial binary operation,
applied freely with constants and a single variable, can equal
`Real.exp` on all of ℝ.

The proof has two pieces:
1. A composition lemma: any `BTerm` (built from `var`, `const`, and `app`)
   whose binary `B` is polynomial evaluates to a univariate polynomial
   when the environment is constant.
2. A growth-bound contradiction: `Polynomial.tendsto_div_exp_atTop`
   says every polynomial divided by `exp` tends to 0, but the
   identity `P.eval x = Real.exp x` would force the ratio to be 1.

Aristotle is asked to fill in both `polynomial_binary_terms_are_polynomial`
and `no_polynomial_binary_generates_exp`.
-/

inductive BTerm where
  | var : Nat → BTerm
  | const : ℝ → BTerm
  | app : BTerm → BTerm → BTerm

namespace BTerm

noncomputable def eval (B : ℝ → ℝ → ℝ) (env : Nat → ℝ) : BTerm → ℝ
  | .var n => env n
  | .const c => c
  | .app a b => B (a.eval B env) (b.eval B env)

end BTerm

def IsPolynomialBinary (B : ℝ → ℝ → ℝ) : Prop :=
  ∃ P : MvPolynomial (Fin 2) ℝ,
    ∀ x y, B x y = MvPolynomial.eval ![x, y] P

/-
**Composition lemma.** Every `BTerm`, evaluated under a polynomial
binary `B` and a constant environment, gives the value of a univariate
polynomial in the environment value.
-/
theorem polynomial_binary_terms_are_polynomial
    {B : ℝ → ℝ → ℝ} (hB : IsPolynomialBinary B)
    (t : BTerm) :
    ∃ P : Polynomial ℝ, ∀ x : ℝ, t.eval B (fun _ => x) = P.eval x := by
  revert hB t;
  -- We proceed by induction on the structure of `BTerm`.
  intro hB t
  induction' t with n c a b ha hb generalizing B;
  · exact ⟨ Polynomial.X, fun x => by simp +decide [ BTerm.eval ] ⟩;
  · exact ⟨ Polynomial.C c, fun x => by simp +decide [ BTerm.eval ] ⟩;
  · obtain ⟨ Q, hQ ⟩ := ha hB
    obtain ⟨ R, hR ⟩ := hb hB
    obtain ⟨ P, hP ⟩ := hB
    use (MvPolynomial.aeval (fun i => if i = 0 then Q else R)) P;
    intro x; rw [ BTerm.eval ] ; simp +decide [ hP, hQ, hR ] ;
    erw [ MvPolynomial.eval_eq', MvPolynomial.aeval_eq_eval₂Hom ];
    simp +decide [ Polynomial.eval_finset_sum, MvPolynomial.eval₂Hom, MvPolynomial.eval₂_eq' ]

/-
**Polynomial-binary impossibility.** No bivariate polynomial
binary operation, applied freely, can equal the real exponential
function on all of ℝ.
-/
theorem no_polynomial_binary_generates_exp
    {B : ℝ → ℝ → ℝ} (hB : IsPolynomialBinary B) :
    ¬ ∃ t : BTerm, ∀ x : ℝ, t.eval B (fun _ => x) = Real.exp x := by
  by_contra h_contra
  obtain ⟨t, ht⟩ := h_contra
  obtain ⟨P, hP⟩ := polynomial_binary_terms_are_polynomial hB t
  have h_eq : ∀ x, P.eval x = Real.exp x := by
    exact fun x => hP x ▸ ht x
  have h_lim : Filter.Tendsto (fun x => P.eval x / Real.exp x) Filter.atTop (nhds 0) := by
    exact Polynomial.tendsto_div_exp_atTop P
  have h_contra : Filter.Tendsto (fun x => Real.exp x / Real.exp x) Filter.atTop (nhds 0) := by
    simpa only [ h_eq ] using h_lim
  simp at h_contra