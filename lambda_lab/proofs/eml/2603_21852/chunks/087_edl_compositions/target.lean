import Mathlib

/-!
# Plan D — EDL composition witnesses

Two more EDL primitives reachable by composition of D4 (exp) and D8 (log):

- **`exp(exp x)`**: `edl(D4_witness, e_const)` — wait, that's exp(D4)/log(e)
  = exp(exp x)/1 = exp(exp x). So `edl (edl (var 0) e_const) e_const`.

- **`log(log x)`**: D8 applied to D8's witness — but D8 is parametric in
  var 0. The composition needs reformulating: log(log x) requires
  applying D8's construction using D8's output as the variable.
  Possibly: `edl 1 (edl (edl 1 (D8_witness)) e_const)`.

These compositions test the depth-2 closure under EDL.
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

/-- **D10** — `exp(exp x)`. Witness: `edl (edl (var 0) e_const) e_const`. -/
theorem edl_witness_exp_exp :
    ∃ t : EDLTerm, ∀ env : Nat → ℝ,
      t.eval? env = some (Real.exp (Real.exp (env 0))) := by
  sorry

/-- **D11** — `log(log x)`. Domain: `0 < env 0`, `env 0 ≠ 1`,
`0 < log(env 0)`, `log(env 0) ≠ 1` (so log(log(env 0)) is well-defined). -/
theorem edl_witness_log_log :
    ∃ t : EDLTerm, ∀ env : Nat → ℝ,
      0 < env 0 → env 0 ≠ 1 →
      0 < Real.log (env 0) → Real.log (env 0) ≠ 1 →
      t.eval? env = some (Real.log (Real.log (env 0))) := by
  sorry

end EDL
