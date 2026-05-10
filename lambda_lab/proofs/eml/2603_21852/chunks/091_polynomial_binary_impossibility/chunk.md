# Chunk 091 — Polynomial-binary impossibility (paper §5 / Pro #4)

## Target

Prove that no single bivariate polynomial binary operation, applied freely with constants and a single variable, can equal the real exponential function. This is GPT Pro's recommended first serious lemma toward the universal-minimality direction (paper §5).

## Statement

```lean
inductive BTerm where
  | var : Nat → BTerm
  | const : ℝ → BTerm
  | app : BTerm → BTerm → BTerm

noncomputable def BTerm.eval (B : ℝ → ℝ → ℝ) (env : Nat → ℝ) : BTerm → ℝ
  | .var n => env n
  | .const c => c
  | .app a b => B (a.eval B env) (b.eval B env)

def IsPolynomialBinary (B : ℝ → ℝ → ℝ) : Prop :=
  ∃ P : MvPolynomial (Fin 2) ℝ,
    ∀ x y, B x y = MvPolynomial.eval ![x, y] P

theorem polynomial_binary_terms_are_polynomial
    {B : ℝ → ℝ → ℝ} (hB : IsPolynomialBinary B)
    (t : BTerm) :
    ∃ P : Polynomial ℝ,
      ∀ x, BTerm.eval B (fun _ => x) t = P.eval x

theorem no_polynomial_binary_generates_exp
    {B : ℝ → ℝ → ℝ} (hB : IsPolynomialBinary B) :
    ¬ ∃ t : BTerm,
      ∀ x : ℝ, BTerm.eval B (fun _ => x) t = Real.exp x
```

## Proof strategy

### Lemma `polynomial_binary_terms_are_polynomial`

By induction on `t : BTerm`:

- **`var n`** case: take `P = Polynomial.X` (the identity polynomial). Then `BTerm.eval B (fun _ => x) (var n) = x = Polynomial.X.eval x`.

- **`const c`** case: take `P = Polynomial.C c`. Then `BTerm.eval B (fun _ => x) (const c) = c = (Polynomial.C c).eval x`.

- **`app a b`** case: by IH, `∃ Pa, BTerm.eval ... a = Pa.eval x` and similarly `Pb`. We need a `P_app` with `B (Pa.eval x) (Pb.eval x) = P_app.eval x`.

  Use `MvPolynomial.aeval` with the homomorphism `f : Fin 2 → Polynomial ℝ` given by `f 0 = Pa, f 1 = Pb`. Then `P_app := MvPolynomial.aeval f MvP` (where `MvP` is the bivariate polynomial witness for `B`).

  The key identity is `(MvPolynomial.aeval f MvP).eval x = MvPolynomial.eval (fun i => (f i).eval x) MvP`, which in Mathlib follows from `MvPolynomial.aeval_def` plus `Polynomial.eval₂_eq_eval_map` / `MvPolynomial.eval_map` / similar coercion lemmas.

### Theorem `no_polynomial_binary_generates_exp`

Suppose for contradiction `∃ t, ∀ x, BTerm.eval B (fun _ => x) t = Real.exp x`. By the lemma, there's some `P : Polynomial ℝ` with `∀ x, P.eval x = Real.exp x`. Then `P.eval x / Real.exp x = 1` for all `x`. But Mathlib has

```
Polynomial.tendsto_div_exp_atTop :
    Tendsto (fun x => P.eval x / Real.exp x) atTop (𝓝 0)
```

(every polynomial divided by `exp` tends to 0). The constant function `1` does not tend to `0`. Contradiction.

## Mathlib pointers

- `Mathlib.Algebra.MvPolynomial.Basic` — `MvPolynomial`, `MvPolynomial.eval`, `MvPolynomial.aeval`
- `Mathlib.Algebra.Polynomial.Eval.Basic` — `Polynomial.eval`, `Polynomial.eval₂`
- `Mathlib.Analysis.SpecialFunctions.PolynomialExp` — `Polynomial.tendsto_div_exp_atTop`
- `Mathlib.Topology.Algebra.Order.LiminfLimsup` — auxiliary

## Why this matters

Paper §5 asks: *is `{1, eml}` minimal?* The polynomial-binary impossibility kills the most natural narrow candidate class for a "simpler" Sheffer operator. It's a partial answer to universal minimality — the real question (over arbitrary continuous/analytic/etc. classes) remains paper-open, but ruling out the polynomial class is a clean Lean-checkable lower bound.

## Status

Submitted to Aristotle 2026-05-10.
