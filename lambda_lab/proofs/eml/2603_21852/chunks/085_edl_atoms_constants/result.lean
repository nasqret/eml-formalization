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

/-- **D5** — Witness for `−1`.

**Analysis**: All closed EDL terms (built from `one`, `e_const`, `edl`) produce values
in the EL-closure of `{1, e}`. Constructing exactly `−1` would require `log(e − 1)` to
be in this closure — closely related to Schanuel's conjecture. Negative values ARE
reachable (e.g., `e/(1−e) ≈ −1.582`), but hitting `−1` exactly appears beyond pure
closed EDL. -/
theorem edl_witness_neg_one :
    ∃ t : EDLTerm, ∀ env : Nat → ℝ, t.eval? env = some (-1 : ℝ) := by
  sorry

/-- **D6** — Witness for `2`.

**Analysis**: Constructing `2` requires `exp(a)/log(b) = 2` for closed EDL terms,
which would place `log(2)` in the EL-closure of `{1, e}`. This is believed false
by Schanuel's conjecture (ln 2 is transcendentally independent from e). -/
theorem edl_witness_two :
    ∃ t : EDLTerm, ∀ env : Nat → ℝ, t.eval? env = some (2 : ℝ) := by
  sorry

/-- **D7** — Witness for `1/2`. Same obstruction as D6 (constructing `1/2`
is equivalent in difficulty to constructing `2`). -/
theorem edl_witness_half :
    ∃ t : EDLTerm, ∀ env : Nat → ℝ, t.eval? env = some ((1 : ℝ) / 2) := by
  sorry

/-
**D8** — Witness for `log x` (the unary log primitive).

**Construction**: `edl one (edl (edl one (var 0)) e_const)` evaluates to `log(env 0)`.

Step-by-step:
1. `edl one (var 0)` = `exp(1)/log(x)` = `e/log(x)`
2. `edl (edl one (var 0)) e_const` = `exp(e/log(x))/log(e)` = `exp(e/log(x))`
3. `edl one (edl (edl one (var 0)) e_const)` = `exp(1)/log(exp(e/log(x)))`
   = `e/(e/log(x))` = `log(x)` ✓
-/
theorem edl_witness_log_x :
    ∃ t : EDLTerm, ∀ env : Nat → ℝ, 0 < env 0 → env 0 ≠ 1 →
      t.eval? env = some (Real.log (env 0)) := by
  refine ⟨.edl .one (.edl (.edl .one (.var 0)) .e_const), fun env hpos hne1 => ?_⟩
  -- Let's simplify the expression using the definitions of `EDLTerm.eval?`.
  simp [EDLTerm.eval?];
  split_ifs <;> simp_all +decide [ ne_of_gt, Real.exp_pos ];
  · grind;
  · linarith;
  · linarith [ Real.exp_pos 1 ];
  · linarith [ Real.exp_pos ( Real.exp 1 / Real.log ( env 0 ) ) ]

end EDL