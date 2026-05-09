import Mathlib

/-!
# Plan D — EDL division witness `x / y`

Building on chunk 084 (D4 = exp via `edl(x, e)`) and chunk 085 (D8 =
log via `edl(1, edl(edl(1, x), e))`), the division primitive `x / y`
should be reachable as `edl(D8(x), D4(y)) = exp(log x) / log(exp y) =
x / y`.

Domain: `0 < env 0` and `env 0 ≠ 1` (for D8 to apply); `env 1` arbitrary.
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

/-- **D9** — Witness for division `env 0 / env 1`.

Strategy: `edl (D8 of var 0) (D4 of var 1)` where D8 gives log(env 0)
and D4 (with var 1) gives exp(env 1). Then
`edl(log x, exp y) = exp(log x) / log(exp y) = x / y` for x > 0, x ≠ 1. -/
theorem edl_witness_div :
    ∃ t : EDLTerm, ∀ env : Nat → ℝ,
      0 < env 0 → env 0 ≠ 1 →
      t.eval? env = some (env 0 / env 1) := by
  sorry

end EDL
