import Mathlib

/-!
# Plan D — EDL constant atoms `−1`, `2`, `½`, `log x`

Continues `084_edl_atoms_pilot` with harder atoms. EDL has only `1`,
variable, the constant `e`, and `edl(x, y) = exp(x) / log(y)`. So all
values are quotients `exp(a)/log(b)`. Achieving negatives and rationals
requires clever compositions (`log b < 0` requires `b ∈ (0, 1)` etc.).

These atoms may or may not be reachable in pure EDL — the paper says
EDL completeness is *conjectured*, not proven. If Aristotle finds
witnesses, that's a meaningful contribution to Plan D.
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

/-- **D5** — Witness for `−1`. Reachable via clever `edl` composition?
Hint: `log b = −1` iff `b = 1/e`. So we'd need `1/e` first. But
`edl(0, e_const) = 1/log(e) = 1`, not `1/e`. -/
theorem edl_witness_neg_one :
    ∃ t : EDLTerm, ∀ env : Nat → ℝ, t.eval? env = some (-1 : ℝ) := by
  sorry

/-- **D6** — Witness for `2`. Reachable iff we can build `b` with
`log b = 1/2`, i.e. `b = √e`. -/
theorem edl_witness_two :
    ∃ t : EDLTerm, ∀ env : Nat → ℝ, t.eval? env = some (2 : ℝ) := by
  sorry

/-- **D7** — Witness for `1/2`. Reachable iff we can build `b` with
`log b = 2`, i.e. `b = e²`. Note: `edl(2, e) = exp(2) = e²`, so
`edl(0, edl(2, e)) = 1/log(e²) = 1/2` if `2` is reachable
(self-referentially via D6). -/
theorem edl_witness_half :
    ∃ t : EDLTerm, ∀ env : Nat → ℝ, t.eval? env = some ((1 : ℝ) / 2) := by
  sorry

/-- **D8** — Witness for `log x` (the unary log primitive). For `x > 0`,
this is the hardest of the easy atoms. Hint: we want
`exp(a) / log(b) = log x`. One natural attempt: take `b = exp(exp(a) /
log x) = ...` (circular). The witness, if it exists, requires careful
composition.

If unprovable, return `sorry` — this is genuine paper-open territory. -/
theorem edl_witness_log_x :
    ∃ t : EDLTerm, ∀ env : Nat → ℝ, 0 < env 0 → env 0 ≠ 1 →
      t.eval? env = some (Real.log (env 0)) := by
  sorry

end EDL
