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

/-- **D14** — `exp(log x) = x` (tautology). Witness: `edl D8 e_const`
or simpler: just D8 followed by exp via D4 should give x back. -/
theorem edl_witness_exp_log_x :
    ∃ t : EDLTerm, ∀ env : Nat → ℝ, 0 < env 0 → env 0 ≠ 1 →
      t.eval? env = some (env 0) := by
  sorry

/-- **D15** — `log(exp x) = x` (tautology). -/
theorem edl_witness_log_exp_x :
    ∃ t : EDLTerm, ∀ env : Nat → ℝ,
      Real.exp (env 0) ≠ 1 →
      t.eval? env = some (env 0) := by
  sorry

/-- **D16** — `x²` (squared). Likely blocked: x² = exp(2 log x) needs
multiplication. -/
theorem edl_witness_sqr :
    ∃ t : EDLTerm, ∀ env : Nat → ℝ, 0 < env 0 → env 0 ≠ 1 →
      t.eval? env = some ((env 0) ^ 2) := by
  sorry

/-- **D17** — sqrt. Likely blocked: needs (1/2) · log x. -/
theorem edl_witness_sqrt :
    ∃ t : EDLTerm, ∀ env : Nat → ℝ, 0 < env 0 → env 0 ≠ 1 →
      t.eval? env = some (Real.sqrt (env 0)) := by
  sorry

end EDL
