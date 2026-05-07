import EML.Framework.EMLPartial

/-!
# EML term builders

Compositional builders that take EMLTerm sub-terms and produce a new
EMLTerm whose partial evaluation is a known function of the
sub-terms' evaluations. These are the workhorses of the EL → EML
compiler: each EL constructor `Op` dispatches to a builder
`mkOp` plus a correctness lemma `mkOp_eval`.

Patterns ported (and generalized to multi-variable `EMLTerm`) from
`Solutions/059_emlterm_for_arsinh_x.lean`'s well-tested helper library.

Conventions:
* `mkExp t` is unconditional (Identity 4).
* `mkLog t` is unconditional in Lean's total semantics but only
  paper-faithful when `t > 0`. In partial semantics, the spec
  requires `0 < t.eval? env`.
* `mkAddPos f g` (and friends) require `0 < f.eval? env` so the
  inner `mkLog f` is well-defined.
-/

namespace EML

namespace EMLTerm

/-! ## Identity 4: `exp x = eml(x, 1)` -/

/-- `mkExp t` evaluates to `Real.exp t.eval`. Always defined. -/
def mkExp (t : EMLTerm) : EMLTerm := .eml t .one

/-- `mkExp` partial-eval spec: always `some (exp t)`. -/
lemma mkExp_eval? (env : Nat → ℝ) (t : EMLTerm) {v : ℝ}
    (hv : t.eval? env = some v) :
    (mkExp t).eval? env = some (Real.exp v) := by
  unfold mkExp
  rw [eval?_eml_of_pos hv (by simp [eval?_one] : EMLTerm.one.eval? env = some 1)
       zero_lt_one]
  congr 1
  rw [Real.log_one, sub_zero]

/-! ## Identity 5: `log z = eml(1, eml(eml(1, z), 1))` -/

/-- `mkLog t` evaluates to `Real.log t.eval` when `t > 0`. -/
def mkLog (t : EMLTerm) : EMLTerm := .eml .one (.eml (.eml .one t) .one)

/-- `mkLog` partial-eval spec: requires `0 < t.eval`. -/
lemma mkLog_eval? (env : Nat → ℝ) (t : EMLTerm) {v : ℝ}
    (hv : t.eval? env = some v) (hpos : 0 < v) :
    (mkLog t).eval? env = some (Real.log v) := by
  unfold mkLog
  -- Inner: eml(.one, t) = exp 1 - log v = e - log v
  have h_inner : (EMLTerm.eml .one t).eval? env = some (Real.exp 1 - Real.log v) := by
    apply eval?_eml_of_pos (by simp [eval?_one] : EMLTerm.one.eval? env = some 1) hv hpos
  -- Middle: eml((inner), .one) = exp(e - log v) - log 1 = exp(e - log v)
  have h_middle : (EMLTerm.eml (.eml .one t) .one).eval? env =
      some (Real.exp (Real.exp 1 - Real.log v)) := by
    have h1 : EMLTerm.one.eval? env = some 1 := by simp [eval?_one]
    rw [eval?_eml_of_pos h_inner h1 zero_lt_one, Real.log_one, sub_zero]
  -- Outer: eml(.one, middle) = e - log(exp(e - log v)) = e - (e - log v) = log v
  have h_pos_middle : 0 < Real.exp (Real.exp 1 - Real.log v) := Real.exp_pos _
  have h1 : EMLTerm.one.eval? env = some 1 := by simp [eval?_one]
  rw [eval?_eml_of_pos h1 h_middle h_pos_middle, Real.log_exp]
  congr 1
  ring

/-! ## Composing exp and log: subtraction (when first arg is positive)

`subT a b = eml(log a, exp b) = exp(log a) - log(exp b) = a - b`,
using `Real.exp_log` (requires `a > 0`) and `Real.log_exp` (free).
-/

/-- `mkSubPos a b` evaluates to `a.eval - b.eval` when `a.eval > 0`. -/
def mkSubPos (a b : EMLTerm) : EMLTerm := .eml (mkLog a) (mkExp b)

/-- `mkSubPos` partial-eval spec: requires `0 < a.eval`. -/
lemma mkSubPos_eval? (env : Nat → ℝ) (a b : EMLTerm) {va vb : ℝ}
    (ha : a.eval? env = some va) (hb : b.eval? env = some vb)
    (hpos : 0 < va) :
    (mkSubPos a b).eval? env = some (va - vb) := by
  unfold mkSubPos
  have h_log : (mkLog a).eval? env = some (Real.log va) := mkLog_eval? env a ha hpos
  have h_exp : (mkExp b).eval? env = some (Real.exp vb) := mkExp_eval? env b hb
  rw [eval?_eml_of_pos h_log h_exp (Real.exp_pos _),
      Real.exp_log hpos, Real.log_exp]

end EMLTerm

end EML
