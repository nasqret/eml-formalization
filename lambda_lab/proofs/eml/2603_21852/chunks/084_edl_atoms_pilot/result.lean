import Mathlib

/-!
# Plan D pilot — EDL atom witnesses

The EDL grammar:
```
EDLTerm ::= 1 ∣ xₙ ∣ e ∣ edl(T, T)        edl(x, y) := exp(x) / log(y)
```
paired with the constant `e` (Euler's number).

This pilot chunk proves witness existence for 4 trivial atoms — `1`,
the variable `x`, the constant `e`, and `exp(x)`. The harder atoms
(`log x`, `neg x`, `+`, `*`, `/`, etc., and especially the trig
family) are paper-open per-primitive completeness for EDL.

Goal: produce literal `EDLTerm` witnesses for each atom.
-/

namespace EDL

/-- The EDL term grammar: `1`, variable, the paired constant `e`, and
the binary operator `edl(x, y) = exp(x) / log(y)`. -/
inductive EDLTerm
  | one : EDLTerm
  | var : Nat → EDLTerm
  | e_const : EDLTerm
  | edl : EDLTerm → EDLTerm → EDLTerm
  deriving Repr

/-- Partial evaluation. Returns `none` exactly when some `edl(_, b)`
has `log b = 0` (i.e. `b = 1` or `b ≤ 0`). -/
noncomputable def EDLTerm.eval? (env : Nat → ℝ) : EDLTerm → Option ℝ
  | .one => some 1
  | .var n => some (env n)
  | .e_const => some (Real.exp 1)
  | .edl a b => (a.eval? env).bind fun va =>
                  (b.eval? env).bind fun vb =>
                    if Real.log vb = 0 then none
                    else some (Real.exp va / Real.log vb)

/-
**D1** — Witness for the constant `1`.
-/
theorem edl_witness_one :
    ∃ t : EDLTerm, ∀ env : Nat → ℝ, t.eval? env = some 1 := by
  exact ⟨ .one, fun env => rfl ⟩

/-
**D2** — Witness for the variable `x` (i.e. `env 0`).
-/
theorem edl_witness_var :
    ∃ t : EDLTerm, ∀ env : Nat → ℝ, t.eval? env = some (env 0) := by
  exact ⟨ EDLTerm.var 0, fun env => rfl ⟩

/-
**D3** — Witness for the constant `e` (Euler's number).
-/
theorem edl_witness_e_const :
    ∃ t : EDLTerm, ∀ env : Nat → ℝ, t.eval? env = some (Real.exp 1) := by
  -- Use the provided witness for the constant `e`.
  use EDLTerm.e_const
  simp [EDLTerm.eval?]

/-
**D4** — Witness for `exp x` via `edl(x, e) = exp(x) / log(e) =
exp(x) / 1 = exp(x)`.
-/
theorem edl_witness_exp :
    ∃ t : EDLTerm, ∀ env : Nat → ℝ, t.eval? env = some (Real.exp (env 0)) := by
  -- Use witness `.edl (.var 0) .e_const`.
  use .edl (.var 0) .e_const;
  -- By definition of `eval?`, we have:
  intro env
  simp [EDLTerm.eval?];
  linarith [ Real.exp_pos 1 ]

end EDL