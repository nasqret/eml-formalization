import Mathlib

/-!
# Plan D — EDL division witness `x / y`

Building on chunk 084 (D4 = exp via `edl(x, e)`) and chunk 085 (D8 =
log via `edl(1, edl(edl(1, x), e))`), the division primitive `x / y`
should be reachable as `edl(D8(x), D4(y)) = exp(log x) / log(exp y) =
x / y`.

Domain: `0 < env 0` and `env 0 ≠ 1` (for D8 to apply); `env 1 ≠ 0`
(so that `log(exp(env 1)) = env 1 ≠ 0` and the outer `edl` is defined).
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

/-
The original statement is false: when `env 1 = 0`, we would need
`t.eval? env = some 0`, but every `edl` node produces `exp(va)/log(vb)`
which is never zero (since `exp > 0` and `log(vb) ≠ 0` by the guard),
and the base cases (`one`, `var`, `e_const`) cannot universally equal zero
for all valid environments. Hence `env 1 ≠ 0` is required.

theorem edl_witness_div :
    ∃ t : EDLTerm, ∀ env : Nat → ℝ,
      0 < env 0 → env 0 ≠ 1 →
      t.eval? env = some (env 0 / env 1) := by
  sorry

**D9** — Witness for division `env 0 / env 1`.

Strategy: `edl (D8 of var 0) (D4 of var 1)` where D8 gives log(env 0)
and D4 (with var 1) gives exp(env 1). Then
`edl(log x, exp y) = exp(log x) / log(exp y) = x / y` for x > 0, x ≠ 1, y ≠ 0.

**Correction**: Added `env 1 ≠ 0` hypothesis — see comment above.
-/
theorem edl_witness_div :
    ∃ t : EDLTerm, ∀ env : Nat → ℝ,
      0 < env 0 → env 0 ≠ 1 → env 1 ≠ 0 →
      t.eval? env = some (env 0 / env 1) := by
  -- Define `t` as the witness for the division formula.
  use .edl (.edl .one (.edl (.edl .one (.var 0)) .e_const)) (.edl (.var 1) .e_const);
  intros env h₀ h₁ h₂;
  -- Simplify the expression using the definitions of `edl` and `eval?`.
  simp [EDLTerm.eval?] at *;
  split_ifs <;> simp_all +decide [ Real.exp_ne_zero ];
  · linarith [ Real.exp_pos 1 ];
  · grind;
  · linarith [ Real.exp_pos 1 ];
  · split_ifs <;> simp_all +decide [ ne_of_gt ];
    · linarith [ Real.exp_pos ( Real.exp 1 / Real.log ( env 0 ) ) ];
    · linarith [ Real.exp_pos ( Real.exp 1 / Real.log ( env 0 ) ) ];
    · linarith [ Real.exp_pos ( env 1 ) ];
    · rw [ Real.exp_log h₀ ]

end EDL