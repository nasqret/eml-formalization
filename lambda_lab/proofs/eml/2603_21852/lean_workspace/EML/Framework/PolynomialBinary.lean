import Mathlib

/-!
# PolynomialBinary — paper §5 / Pro #4 frontier (scaffold)

This module sets up the **definitions** for the polynomial-binary
impossibility result that GPT Pro recommended as the right entry
point into universal minimality. The headline statement is:

> *No bivariate polynomial binary operation, applied freely with
> constants and a single variable, can equal `Real.exp` on all of ℝ.*

The proof has two pieces (sketches in `gpt_pro_bundle/frontier_questions/RESPONSE.md`):

1. A composition lemma: any `BTerm` evaluated under a polynomial
   binary `B` and a constant environment gives a univariate polynomial
   in the environment value. By induction; the `app` case substitutes
   via `MvPolynomial.aeval`.

2. A growth-bound contradiction: `Polynomial.tendsto_div_exp_atTop`
   says every `P.eval x / Real.exp x` tends to 0 at infinity, but
   `P.eval x = Real.exp x` for all `x` would force the ratio to be 1.

The composition lemma's `app` case requires precise handling of
`MvPolynomial.aeval` / `eval₂Hom` interaction with `Polynomial.eval`,
which is non-trivial Mathlib API surface. This module **states** the
two theorems and the supporting definitions; the proofs are delegated
to Aristotle (chunk 091) and not yet integrated.

When the proofs return clean, the headline `Prop` is:
`PolynomialBinaryImpossibility` below.
-/

/-- Free term language over a single binary operation `B`, with
free variables (`var n`) and real constants (`const c`). -/
inductive BTerm where
  | var   : Nat → BTerm
  | const : ℝ   → BTerm
  | app   : BTerm → BTerm → BTerm

namespace BTerm

/-- Evaluate a `BTerm` against a binary operation `B` and an
environment for variables. -/
noncomputable def eval (B : ℝ → ℝ → ℝ) (env : Nat → ℝ) : BTerm → ℝ
  | .var n   => env n
  | .const c => c
  | .app a b => B (a.eval B env) (b.eval B env)

@[simp] lemma eval_var (B : ℝ → ℝ → ℝ) (env : Nat → ℝ) (n : Nat) :
    BTerm.eval B env (.var n) = env n := rfl

@[simp] lemma eval_const (B : ℝ → ℝ → ℝ) (env : Nat → ℝ) (c : ℝ) :
    BTerm.eval B env (.const c) = c := rfl

@[simp] lemma eval_app (B : ℝ → ℝ → ℝ) (env : Nat → ℝ) (a b : BTerm) :
    BTerm.eval B env (.app a b) = B (a.eval B env) (b.eval B env) := rfl

end BTerm

/-- A binary operation `B : ℝ → ℝ → ℝ` is **polynomial** when there
is a bivariate polynomial witness `MvP ∈ MvPolynomial (Fin 2) ℝ` such
that `B x y = MvP.eval ![x, y]` for all real `x, y`. -/
def IsPolynomialBinary (B : ℝ → ℝ → ℝ) : Prop :=
  ∃ P : MvPolynomial (Fin 2) ℝ,
    ∀ x y : ℝ, B x y = MvPolynomial.eval ![x, y] P

/-- **Composition lemma (Aristotle chunk 091).** Any `BTerm` evaluated
under a polynomial binary `B` and a constant environment gives a
univariate polynomial in the constant. Proof structure: induction on
the term; the `app` case substitutes the inductive polynomial witnesses
for the two sub-terms into the bivariate witness for `B` via
`MvPolynomial.aeval`. -/
theorem polynomial_binary_terms_are_polynomial
    {B : ℝ → ℝ → ℝ} (hB : IsPolynomialBinary B)
    (t : BTerm) :
    ∃ P : Polynomial ℝ, ∀ x : ℝ, t.eval B (fun _ => x) = P.eval x := by
  revert hB t
  intro hB t
  induction' t with n c a b ha hb generalizing B
  · exact ⟨ Polynomial.X, fun x => by simp +decide [ BTerm.eval ] ⟩
  · exact ⟨ Polynomial.C c, fun x => by simp +decide [ BTerm.eval ] ⟩
  · obtain ⟨ Q, hQ ⟩ := ha hB
    obtain ⟨ R, hR ⟩ := hb hB
    obtain ⟨ P, hP ⟩ := hB
    use (MvPolynomial.aeval (fun i => if i = 0 then Q else R)) P
    intro x; rw [ BTerm.eval ]; simp +decide [ hP, hQ, hR ]
    erw [ MvPolynomial.eval_eq', MvPolynomial.aeval_eq_eval₂Hom ]
    simp +decide [ Polynomial.eval_finset_sum, MvPolynomial.eval₂Hom,
                   MvPolynomial.eval₂_eq' ]

/-- **Polynomial-binary impossibility (paper §5, polynomial-class
first cut).** No bivariate polynomial binary operation, applied freely
with constants and a single variable, can equal the real exponential
function on all of ℝ.

Proof: by `polynomial_binary_terms_are_polynomial`, any candidate
term gives a univariate polynomial `P` with `P.eval x = Real.exp x`
for all `x`. Then `P.eval x / Real.exp x = 1` for every `x`, but
`Polynomial.tendsto_div_exp_atTop` says this ratio tends to `0` at
infinity. The constant function `1` cannot also tend to `0`. -/
theorem no_polynomial_binary_generates_exp
    {B : ℝ → ℝ → ℝ} (hB : IsPolynomialBinary B) :
    ¬ ∃ t : BTerm, ∀ x : ℝ, t.eval B (fun _ => x) = Real.exp x := by
  rintro ⟨t, ht⟩
  obtain ⟨P, hP⟩ := polynomial_binary_terms_are_polynomial hB t
  have h_eq : ∀ x, P.eval x = Real.exp x := fun x => hP x ▸ ht x
  -- The polynomial-over-exp ratio tends to 0.
  have h_lim : Filter.Tendsto (fun x => P.eval x / Real.exp x)
      Filter.atTop (nhds 0) := Polynomial.tendsto_div_exp_atTop P
  -- But under the identity hypothesis, the ratio is constantly 1.
  have h_const : (fun x => P.eval x / Real.exp x) = (fun _ => (1 : ℝ)) := by
    funext x
    rw [h_eq x, div_self (Real.exp_pos x).ne']
  rw [h_const] at h_lim
  -- Tendsto of `fun _ => 1` to `0` contradicts uniqueness against `1`.
  have h_one : Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  exact absurd (tendsto_nhds_unique h_lim h_one) (by norm_num)
