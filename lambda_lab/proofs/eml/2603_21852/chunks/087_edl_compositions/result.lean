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

private lemma eval_edl_of_log_ne_zero {env : Nat → ℝ} {a b : EDLTerm}
    {va vb : ℝ} (ha : a.eval? env = some va) (hb : b.eval? env = some vb)
    (hlog : Real.log vb ≠ 0) :
    (EDLTerm.edl a b).eval? env = some (Real.exp va / Real.log vb) := by
  simp only [EDLTerm.eval?, ha, hb, Option.bind_some]
  simp only [if_neg hlog]

private lemma log_exp1_eq : Real.log (Real.exp 1) = (1 : ℝ) := Real.log_exp 1

private lemma log_exp1_ne_zero : Real.log (Real.exp 1) ≠ (0 : ℝ) := by
  rw [log_exp1_eq]; exact one_ne_zero

private lemma eval_edl_e {env : Nat → ℝ} {a : EDLTerm} {va : ℝ}
    (ha : a.eval? env = some va) :
    (EDLTerm.edl a .e_const).eval? env = some (Real.exp va) := by
  rw [eval_edl_of_log_ne_zero ha rfl log_exp1_ne_zero, log_exp1_eq, div_one]

/-- **D10** — `exp(exp x)`. Witness: `edl (edl (var 0) e_const) e_const`. -/
theorem edl_witness_exp_exp :
    ∃ t : EDLTerm, ∀ env : Nat → ℝ,
      t.eval? env = some (Real.exp (Real.exp (env 0))) := by
  exact ⟨.edl (.edl (.var 0) .e_const) .e_const, fun env =>
    eval_edl_e (eval_edl_e rfl)⟩

-- D8 witness: computes log(env 0) from edl one (edl (edl one (var 0)) e_const)
-- Key idea: edl(1, x) = e/log(x), edl(e/log(x), e) = exp(e/log(x)),
-- edl(1, exp(e/log(x))) = e / log(exp(e/log(x))) = e / (e/log(x)) = log(x)
private noncomputable def d8 : EDLTerm :=
  .edl .one (.edl (.edl .one (.var 0)) .e_const)

private lemma d8_eval (env : Nat → ℝ) (h0 : 0 < env 0) (h1 : env 0 ≠ 1) :
    d8.eval? env = some (Real.log (env 0)) := by
  convert eval_edl_of_log_ne_zero _ _ _ using 1;
  rotate_left;
  exact 1;
  exact Real.exp ( Real.exp 1 / Real.log ( env 0 ) );
  · rfl;
  · convert eval_edl_e _ using 1;
    convert eval_edl_of_log_ne_zero _ _ _ using 1;
    · rfl;
    · rfl;
    · exact fun h => h1 <| Real.eq_one_of_pos_of_log_eq_zero h0 h;
  · norm_num;
    exact ⟨ h0.ne', h1, by linarith ⟩;
  · norm_num [ Real.exp_ne_zero, Real.log_exp ]

/-- The witness for log(log(x)) is obtained by substituting d8 for var 0 in d8. -/
private noncomputable def d8d8 : EDLTerm :=
  .edl .one (.edl (.edl .one d8) .e_const)

private lemma d8d8_eval (env : Nat → ℝ)
    (h0 : 0 < env 0) (h1 : env 0 ≠ 1)
    (h2 : 0 < Real.log (env 0)) (h3 : Real.log (env 0) ≠ 1) :
    d8d8.eval? env = some (Real.log (Real.log (env 0))) := by
  -- Apply the definition of `d8d8` and the properties of `eval?`.
  have h_eval : (EDLTerm.edl (.edl .one d8) .e_const).eval? env = some (Real.exp (Real.exp 1 / Real.log (Real.log (env 0)))) := by
    rw [ eval_edl_e ];
    apply eval_edl_of_log_ne_zero;
    · rfl;
    · exact d8_eval env h0 h1;
    · exact fun h => h3 <| Real.eq_one_of_pos_of_log_eq_zero h2 h;
  -- Apply the definition of `d8d8` and the properties of `eval?` to conclude the proof.
  have h_final : (EDLTerm.edl .one (.edl (.edl .one d8) .e_const)).eval? env = some (Real.exp 1 / Real.log (Real.exp (Real.exp 1 / Real.log (Real.log (env 0))))) := by
    rw [ eval_edl_of_log_ne_zero ] <;> norm_num [ h_eval ];
    · rfl;
    · exact ⟨ ⟨ h0.ne', h1, by linarith ⟩, h3, by linarith ⟩;
  convert h_final using 2 ; norm_num [ Real.exp_ne_zero ]

/-- **D11** — `log(log x)`. Domain: `0 < env 0`, `env 0 ≠ 1`,
`0 < log(env 0)`, `log(env 0) ≠ 1` (so log(log(env 0)) is well-defined). -/
theorem edl_witness_log_log :
    ∃ t : EDLTerm, ∀ env : Nat → ℝ,
      0 < env 0 → env 0 ≠ 1 →
      0 < Real.log (env 0) → Real.log (env 0) ≠ 1 →
      t.eval? env = some (Real.log (Real.log (env 0))) := by
  exact ⟨d8d8, fun env h0 h1 h2 h3 => d8d8_eval env h0 h1 h2 h3⟩

end EDL