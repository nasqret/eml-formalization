import Mathlib

/-!
# Plan D wide search — speculative EDL primitive witnesses

Try to find EDL witnesses for harder primitives. Some are likely
unreachable from closed EDL terms (without `0` or negation), but
Aristotle may discover clever compositions. Each theorem is `sorry` —
solve as many as possible, leave others as `sorry` with brief
analytical reason.

EDL grammar:
```
EDLTerm ::= 1 ∣ xₙ ∣ e ∣ edl(T, T)        edl(x, y) := exp(x) / log(y)
```
-/

namespace EDL

inductive EDLTerm
  | one : EDLTerm
  | var : Nat → EDLTerm
  | e_const : EDLTerm
  | edl : EDLTerm → EDLTerm → EDLTerm
  deriving Repr

noncomputable def EDLTerm.eval? (env : Nat → ℝ) : EDLTerm → Option ℝ
  | .one => some 1
  | .var n => some (env n)
  | .e_const => some (Real.exp 1)
  | .edl a b => (a.eval? env).bind fun va =>
                  (b.eval? env).bind fun vb =>
                    if Real.log vb = 0 then none
                    else some (Real.exp va / Real.log vb)

/-- **D14** — `exp(log x) = x` (tautology). Witness: `var 0`.
The identity `var 0` trivially evaluates to `env 0`. A more
interesting compositional witness `edl(LOG_X, e)` also works,
where `LOG_X = edl(1, edl(edl(1, x₀), e))` computes `log(x)`
via `e/(e/log(x))`, and wrapping in `edl(·, e)` applies
`exp(·)/log(e) = exp(·)/1`, giving `exp(log(x)) = x`. -/
theorem edl_witness_exp_log_x :
    ∃ t : EDLTerm, ∀ env : Nat → ℝ, 0 < env 0 → env 0 ≠ 1 →
      t.eval? env = some (env 0) := by
  exact ⟨.var 0, fun _ _ _ => rfl⟩

/-- **D15** — `log(exp x) = x` (tautology). Witness: `var 0`.
Similarly, `edl(1, edl(edl(1, edl(x₀, e)), e))` computes
`log(exp x) = x` compositionally, but `var 0` suffices. -/
theorem edl_witness_log_exp_x :
    ∃ t : EDLTerm, ∀ env : Nat → ℝ,
      Real.exp (env 0) ≠ 1 →
      t.eval? env = some (env 0) := by
  exact ⟨.var 0, fun _ _ => rfl⟩

/-- **D16** — `x²` (squared). **Unreachable in closed EDL.**

Analytical justification: `x² = exp(2·log x)` requires producing the
constant `2` or, equivalently, adding `log x` to itself. The EDL
combinator `edl(a,b) = exp(a)/log(b)` provides no mechanism for
addition of two sub-expression values — each application wraps one
sub-expression inside `exp(·)` and divides by `log(·)` of another.
Since the base constants `{1, e}` and the variable `x` generate a
tower of iterated exp/log compositions but never yield a sum of two
like terms, the function `x ↦ x²` lies outside the EDL-definable
function class. -/
theorem edl_witness_sqr :
    ∃ t : EDLTerm, ∀ env : Nat → ℝ, 0 < env 0 → env 0 ≠ 1 →
      t.eval? env = some ((env 0) ^ 2) := by
  sorry

/-- **D17** — `√x`. **Unreachable in closed EDL.**

Analytical justification: `√x = exp(½·log x)` requires producing the
constant `1/2` or halving `log x`. By the same argument as D16, the
EDL combinator cannot produce addition or scalar multiplication of
sub-expression values, so the function `x ↦ √x` is not
EDL-definable. -/
theorem edl_witness_sqrt :
    ∃ t : EDLTerm, ∀ env : Nat → ℝ, 0 < env 0 → env 0 ≠ 1 →
      t.eval? env = some (Real.sqrt (env 0)) := by
  sorry

end EDL
