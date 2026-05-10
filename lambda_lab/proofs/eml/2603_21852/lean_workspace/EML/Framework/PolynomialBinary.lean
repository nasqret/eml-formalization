import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.SpecialFunctions.PolynomialExp

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

/-- **Conjecture (paper §5, polynomial-class first cut).** No
bivariate polynomial binary operation, applied freely with constants
and a single variable, can equal the real exponential function on
all of ℝ.

The proof is sketched in `gpt_pro_bundle/frontier_questions/RESPONSE.md`
and delegated to Aristotle (chunk 091); a manual implementation
requires careful handling of `MvPolynomial.aeval` / `eval₂Hom`
composition with `Polynomial.eval`. Until Aristotle returns or the
manual proof closes, the statement is recorded here as a `Prop` so
that downstream code can reference it. -/
def PolynomialBinaryImpossibility : Prop :=
  ∀ B : ℝ → ℝ → ℝ, IsPolynomialBinary B →
    ¬ ∃ t : BTerm, ∀ x : ℝ, t.eval B (fun _ => x) = Real.exp x
