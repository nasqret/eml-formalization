import EML.Framework.Builders

/-!
# Arithmetic EML term builders

Compositional builders that take EMLTerm sub-terms and produce a new
EMLTerm whose partial evaluation is the corresponding arithmetic
operation on the sub-terms' evaluations. These are the workhorses
dispatched by the EL → EML compiler for arithmetic primitives.

The witnesses are ports (with the chunk-local single variable replaced
by a generic sub-term `a` or two sub-terms `a`, `b`) of the proven
single- and two-variable witnesses in
`Solutions/036_emlterm_for_neg_x.lean` (`-x`),
`Solutions/037_emlterm_for_inv_x.lean` (`1/x` for `x>0`),
`Solutions/038_emlterm_for_sq_x.lean` (`x²` for `x>0`),
`Solutions/040_emlterm_for_add_xy.lean` (`x+y` unconditional),
`Solutions/041_emlterm_for_mul_xy.lean` (`x*y` for `x,y>0`).

Conventions:
* `mkNeg a` is unconditional (the `-x` identity does not funnel through
  `log a`; the only nested `log` is on `exp(va) - va`, which is
  always positive).
* `mkAdd a b` is unconditional (same trick).
* `mkSub a b := mkAdd a (mkNeg b)` is unconditional.
* `mkMulPos a b` requires `0 < va` and `0 < vb`.
* `mkInvPos a` and `mkSqPos a` require `0 < va`.
-/

namespace EML

namespace EMLTerm

/-! ## Helper positivity facts -/

private lemma exp_sub_self_pos (x : ℝ) : 0 < Real.exp x - x := by
  linarith [Real.add_one_le_exp x]

private lemma sub_log_pos {x : ℝ} (hx : 0 < x) : 0 < x - Real.log x := by
  linarith [Real.log_le_sub_one_of_pos hx]

/-! ## `mkNeg`: `-a`, unconditional

Port of chunk 036. With `a` standing in for `var`:
* `w(a)    := eml a (eml a one)`           evaluates to `exp(va) - va` (positive).
* `expA(a) := eml a one`                    evaluates to `exp(va)`.
* `logW    := eml one (eml (eml one w) one)` evaluates to `log(exp(va) - va)`.
* `mkNeg a := eml logW (eml expA one)`       evaluates to `-va`.
-/

/-- `mkNeg a` evaluates to `-a.eval`. Always defined. -/
def mkNeg (a : EMLTerm) : EMLTerm :=
  let w    : EMLTerm := .eml a (.eml a .one)
  let expA : EMLTerm := .eml a .one
  let logW : EMLTerm := .eml .one (.eml (.eml .one w) .one)
  .eml logW (.eml expA .one)

/-- `mkNeg` partial-eval spec: always `some (-va)`. -/
lemma mkNeg_eval? (env : Nat → ℝ) (a : EMLTerm) {va : ℝ}
    (ha : a.eval? env = some va) :
    (mkNeg a).eval? env = some (-va) := by
  unfold mkNeg
  -- `one` evaluates to `some 1`.
  have h1 : (EMLTerm.one).eval? env = some 1 := by simp
  -- `eml a one` evaluates to `some (exp va)`.
  have h_expA : (EMLTerm.eml a .one).eval? env = some (Real.exp va) := by
    rw [eval?_eml_of_pos ha h1 zero_lt_one, Real.log_one, sub_zero]
  -- `eml a (eml a one)` evaluates to `some (exp va - va)`.
  have h_w : (EMLTerm.eml a (.eml a .one)).eval? env =
      some (Real.exp va - va) := by
    rw [eval?_eml_of_pos ha h_expA (Real.exp_pos _), Real.log_exp]
  -- positivity of `exp va - va`.
  have h_w_pos : 0 < Real.exp va - va := exp_sub_self_pos va
  -- `eml one w` = `exp 1 - log (exp va - va) = e - log(exp va - va)`.
  have h_eml_one_w : (EMLTerm.eml .one (.eml a (.eml a .one))).eval? env =
      some (Real.exp 1 - Real.log (Real.exp va - va)) := by
    exact eval?_eml_of_pos h1 h_w h_w_pos
  -- `eml (eml one w) one` = `exp(e - log(exp va - va)) - log 1 = exp(e - log(exp va - va))`.
  have h_eml_eml_one_w_one :
      (EMLTerm.eml (.eml .one (.eml a (.eml a .one))) .one).eval? env =
      some (Real.exp (Real.exp 1 - Real.log (Real.exp va - va))) := by
    rw [eval?_eml_of_pos h_eml_one_w h1 zero_lt_one, Real.log_one, sub_zero]
  -- `logW = eml one (eml (eml one w) one)` evaluates to `log(exp va - va)`.
  have h_pos_inner : 0 < Real.exp (Real.exp 1 - Real.log (Real.exp va - va)) :=
    Real.exp_pos _
  have h_logW :
      (EMLTerm.eml .one (.eml (.eml .one (.eml a (.eml a .one))) .one)).eval? env =
      some (Real.log (Real.exp va - va)) := by
    rw [eval?_eml_of_pos h1 h_eml_eml_one_w_one h_pos_inner, Real.log_exp]
    congr 1
    ring
  -- `eml expA one` = `exp(exp va) - log 1 = exp(exp va)`.
  have h_eml_expA_one : (EMLTerm.eml (.eml a .one) .one).eval? env =
      some (Real.exp (Real.exp va)) := by
    rw [eval?_eml_of_pos h_expA h1 zero_lt_one, Real.log_one, sub_zero]
  -- final.
  rw [eval?_eml_of_pos h_logW h_eml_expA_one (Real.exp_pos _),
      Real.exp_log h_w_pos, Real.log_exp]
  congr 1
  ring

/-! ## `mkAdd`: `a + b`, unconditional

Port of chunk 040. With `varX → a`, `varY → b`:
* LHS subterm `mkLog (mkExp a)` evaluates to `va`.
* RHS subterm:
  - `w := eml a (eml a one)` evaluates to `exp(va) - va` (positive),
  - `logW := mkLog (...)` (manual unfolding) evaluates to `log(exp(va) - va)`,
  - `mid := eml logW (eml b one) = (exp(va)-va) - vb`,
  - `wrap := eml mid one = exp((exp(va)-va) - vb)`.
* Full: `eml LHS RHS` = `exp(va) - log(exp((exp(va)-va)-vb))`
                      = `exp(va) - ((exp(va)-va)-vb)` = `va + vb`.
-/

/-- `mkAdd a b` evaluates to `a.eval + b.eval`. Always defined. -/
def mkAdd (a b : EMLTerm) : EMLTerm :=
  let lhs : EMLTerm :=
    .eml .one (.eml (.eml .one (.eml a .one)) .one)
  let rhs : EMLTerm :=
    .eml
      (.eml (.eml .one (.eml (.eml .one (.eml a (.eml a .one))) .one))
            (.eml b .one))
      .one
  .eml lhs rhs

/-- `mkAdd` partial-eval spec: always `some (va + vb)`. -/
lemma mkAdd_eval? (env : Nat → ℝ) (a b : EMLTerm) {va vb : ℝ}
    (ha : a.eval? env = some va) (hb : b.eval? env = some vb) :
    (mkAdd a b).eval? env = some (va + vb) := by
  unfold mkAdd
  have h1 : (EMLTerm.one).eval? env = some 1 := by simp
  -- LHS: log(exp(va)) = va.
  -- expA = eml a one
  have h_expA : (EMLTerm.eml a .one).eval? env = some (Real.exp va) := by
    rw [eval?_eml_of_pos ha h1 zero_lt_one, Real.log_one, sub_zero]
  -- eml one expA = exp 1 - log(exp va) = exp 1 - va
  have h_eml_one_expA :
      (EMLTerm.eml .one (.eml a .one)).eval? env =
      some (Real.exp 1 - va) := by
    rw [eval?_eml_of_pos h1 h_expA (Real.exp_pos _), Real.log_exp]
  -- eml (eml one expA) one = exp(exp 1 - va) - log 1 = exp(exp 1 - va)
  have h_eml_eml_one_expA_one :
      (EMLTerm.eml (.eml .one (.eml a .one)) .one).eval? env =
      some (Real.exp (Real.exp 1 - va)) := by
    rw [eval?_eml_of_pos h_eml_one_expA h1 zero_lt_one, Real.log_one, sub_zero]
  -- LHS: eml one (eml (eml one (eml a one)) one) = exp 1 - log(exp(exp 1 - va))
  --                                              = exp 1 - (exp 1 - va) = va
  have h_lhs :
      (EMLTerm.eml .one (.eml (.eml .one (.eml a .one)) .one)).eval? env =
      some va := by
    rw [eval?_eml_of_pos h1 h_eml_eml_one_expA_one (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  -- RHS:
  -- inner w = eml a (eml a one), evaluates to exp(va) - va, positive.
  have h_w : (EMLTerm.eml a (.eml a .one)).eval? env =
      some (Real.exp va - va) := by
    rw [eval?_eml_of_pos ha h_expA (Real.exp_pos _), Real.log_exp]
  have h_w_pos : 0 < Real.exp va - va := exp_sub_self_pos va
  -- eml one w = exp 1 - log(exp(va) - va)
  have h_eml_one_w :
      (EMLTerm.eml .one (.eml a (.eml a .one))).eval? env =
      some (Real.exp 1 - Real.log (Real.exp va - va)) :=
    eval?_eml_of_pos h1 h_w h_w_pos
  -- eml (eml one w) one = exp(exp 1 - log(exp(va)-va))
  have h_eml_eml_one_w_one :
      (EMLTerm.eml (.eml .one (.eml a (.eml a .one))) .one).eval? env =
      some (Real.exp (Real.exp 1 - Real.log (Real.exp va - va))) := by
    rw [eval?_eml_of_pos h_eml_one_w h1 zero_lt_one, Real.log_one, sub_zero]
  -- logW := eml one (eml (eml one w) one) = log(exp(va) - va)
  have h_pos_inner : 0 < Real.exp (Real.exp 1 - Real.log (Real.exp va - va)) :=
    Real.exp_pos _
  have h_logW :
      (EMLTerm.eml .one (.eml (.eml .one (.eml a (.eml a .one))) .one)).eval? env =
      some (Real.log (Real.exp va - va)) := by
    rw [eval?_eml_of_pos h1 h_eml_eml_one_w_one h_pos_inner, Real.log_exp]
    congr 1
    ring
  -- eml b one = exp(vb)
  have h_expB : (EMLTerm.eml b .one).eval? env = some (Real.exp vb) := by
    rw [eval?_eml_of_pos hb h1 zero_lt_one, Real.log_one, sub_zero]
  -- eml logW (eml b one) = exp(log(exp(va)-va)) - log(exp vb) = (exp(va)-va) - vb
  have h_mid :
      (EMLTerm.eml
        (.eml .one (.eml (.eml .one (.eml a (.eml a .one))) .one))
        (.eml b .one)).eval? env =
      some ((Real.exp va - va) - vb) := by
    rw [eval?_eml_of_pos h_logW h_expB (Real.exp_pos _),
        Real.exp_log h_w_pos, Real.log_exp]
  -- wrap: eml mid one = exp((exp(va)-va) - vb)
  have h_wrap :
      (EMLTerm.eml
        (.eml (.eml .one (.eml (.eml .one (.eml a (.eml a .one))) .one))
              (.eml b .one))
        .one).eval? env =
      some (Real.exp ((Real.exp va - va) - vb)) := by
    rw [eval?_eml_of_pos h_mid h1 zero_lt_one, Real.log_one, sub_zero]
  -- final: eml lhs wrap = exp(va) - log(exp((exp(va)-va)-vb))
  --                     = exp(va) - ((exp(va)-va) - vb) = va + vb
  rw [eval?_eml_of_pos h_lhs h_wrap (Real.exp_pos _), Real.log_exp]
  congr 1
  ring

/-! ## `mkSub`: `a - b`, unconditional, defined as `mkAdd a (mkNeg b)`. -/

/-- `mkSub a b` evaluates to `a.eval - b.eval`. Always defined. -/
def mkSub (a b : EMLTerm) : EMLTerm := mkAdd a (mkNeg b)

/-- `mkSub` partial-eval spec: always `some (va - vb)`. -/
lemma mkSub_eval? (env : Nat → ℝ) (a b : EMLTerm) {va vb : ℝ}
    (ha : a.eval? env = some va) (hb : b.eval? env = some vb) :
    (mkSub a b).eval? env = some (va - vb) := by
  unfold mkSub
  have h_neg : (mkNeg b).eval? env = some (-vb) := mkNeg_eval? env b hb
  have h := mkAdd_eval? env a (mkNeg b) ha h_neg
  simpa [sub_eq_add_neg] using h

/-! ## `mkInvPos`: `1/a`, requires `0 < va`

Port of chunk 037. With `var → a`:
* `logT  := mkLog a` evaluates to `log(va)`.
* `xML   := eml logT a` evaluates to `exp(log(va)) - log(va) = va - log(va)` (positive).
* `logXML := mkLog xML` evaluates to `log(va - log(va))`.
* `negLog := eml logXML (eml a one)` evaluates to
   `exp(log(va - log(va))) - log(exp(va))` = `(va - log(va)) - va = -log(va)`.
* `mkInvPos a := eml negLog one = exp(-log(va)) - log 1 = 1/va`.
-/

/-- `mkInvPos a` evaluates to `1 / a.eval` when `a.eval > 0`. -/
def mkInvPos (a : EMLTerm) : EMLTerm :=
  let logT     : EMLTerm := mkLog a
  let xML      : EMLTerm := .eml logT a
  let logXML   : EMLTerm := mkLog xML
  let negLog   : EMLTerm := .eml logXML (.eml a .one)
  .eml negLog .one

/-- `mkInvPos` partial-eval spec: requires `0 < va`. -/
lemma mkInvPos_eval? (env : Nat → ℝ) (a : EMLTerm) {va : ℝ}
    (ha : a.eval? env = some va) (hpos : 0 < va) :
    (mkInvPos a).eval? env = some (1 / va) := by
  unfold mkInvPos
  have h1 : (EMLTerm.one).eval? env = some 1 := by simp
  -- log(va).
  have h_logT : (mkLog a).eval? env = some (Real.log va) :=
    mkLog_eval? env a ha hpos
  -- eml logT a = exp(log va) - log va = va - log va.
  have h_xML : (EMLTerm.eml (mkLog a) a).eval? env = some (va - Real.log va) := by
    rw [eval?_eml_of_pos h_logT ha hpos, Real.exp_log hpos]
  -- positivity of va - log va.
  have h_xML_pos : 0 < va - Real.log va := sub_log_pos hpos
  -- log(va - log va).
  have h_logXML : (mkLog (.eml (mkLog a) a)).eval? env =
      some (Real.log (va - Real.log va)) :=
    mkLog_eval? env (.eml (mkLog a) a) h_xML h_xML_pos
  -- eml a one = exp va.
  have h_expA : (EMLTerm.eml a .one).eval? env = some (Real.exp va) := by
    rw [eval?_eml_of_pos ha h1 zero_lt_one, Real.log_one, sub_zero]
  -- eml logXML (eml a one) = exp(log(va - log va)) - log(exp va) = (va - log va) - va = -log va.
  have h_negLog :
      (EMLTerm.eml (mkLog (.eml (mkLog a) a)) (.eml a .one)).eval? env =
      some (-Real.log va) := by
    rw [eval?_eml_of_pos h_logXML h_expA (Real.exp_pos _),
        Real.exp_log h_xML_pos, Real.log_exp]
    congr 1
    ring
  -- eml negLog one = exp(-log va) - log 1 = exp(-log va) = 1/va.
  rw [eval?_eml_of_pos h_negLog h1 zero_lt_one, Real.log_one, sub_zero,
      Real.exp_neg, Real.exp_log hpos, one_div]

/-! ## `mkSqPos`: `a^2`, requires `0 < va`

Port of chunk 038. The construction builds `2 * log(va)` via:
* `logT     := mkLog a` evaluates to `log(va)`.
* `xML      := eml logT a` evaluates to `va - log(va)` (positive).
* `logXML   := mkLog xML` evaluates to `log(va - log(va))`.
* `xM2L     := eml logXML (eml logT one) = exp(log(va - log va)) - log(exp(log va))
              = (va - log va) - log va = va - 2 log va`.
* `twoLog   := eml logT (eml xM2L one) = exp(log va) - log(exp(va - 2 log va))
              = va - (va - 2 log va) = 2 log va`.
* `mkSqPos a := eml twoLog one = exp(2 log va) - log 1 = va^2`.
-/

/-- `mkSqPos a` evaluates to `a.eval ^ 2` when `a.eval > 0`. -/
def mkSqPos (a : EMLTerm) : EMLTerm :=
  let logT   : EMLTerm := mkLog a
  let xML    : EMLTerm := .eml logT a
  let logXML : EMLTerm := mkLog xML
  let xM2L   : EMLTerm := .eml logXML (.eml logT .one)
  let twoLog : EMLTerm := .eml logT (.eml xM2L .one)
  .eml twoLog .one

/-- `mkSqPos` partial-eval spec: requires `0 < va`. -/
lemma mkSqPos_eval? (env : Nat → ℝ) (a : EMLTerm) {va : ℝ}
    (ha : a.eval? env = some va) (hpos : 0 < va) :
    (mkSqPos a).eval? env = some (va ^ 2) := by
  unfold mkSqPos
  have h1 : (EMLTerm.one).eval? env = some 1 := by simp
  -- log va.
  have h_logT : (mkLog a).eval? env = some (Real.log va) :=
    mkLog_eval? env a ha hpos
  -- xML = eml logT a = va - log va.
  have h_xML : (EMLTerm.eml (mkLog a) a).eval? env = some (va - Real.log va) := by
    rw [eval?_eml_of_pos h_logT ha hpos, Real.exp_log hpos]
  have h_xML_pos : 0 < va - Real.log va := sub_log_pos hpos
  -- log xML.
  have h_logXML : (mkLog (.eml (mkLog a) a)).eval? env =
      some (Real.log (va - Real.log va)) :=
    mkLog_eval? env (.eml (mkLog a) a) h_xML h_xML_pos
  -- eml logT one = exp(log va) - log 1 = va.
  have h_eml_logT_one : (EMLTerm.eml (mkLog a) .one).eval? env = some va := by
    rw [eval?_eml_of_pos h_logT h1 zero_lt_one, Real.log_one, sub_zero,
        Real.exp_log hpos]
  -- xM2L = eml logXML (eml logT one) = exp(log(va - log va)) - log va = (va - log va) - log va.
  -- Wait: exp(log(va - log va)) - log(va) = (va - log va) - log va = va - 2 log va.
  have h_xM2L :
      (EMLTerm.eml (mkLog (.eml (mkLog a) a)) (.eml (mkLog a) .one)).eval? env =
      some (va - 2 * Real.log va) := by
    rw [eval?_eml_of_pos h_logXML h_eml_logT_one hpos,
        Real.exp_log h_xML_pos]
    congr 1
    ring
  -- eml xM2L one = exp(va - 2 log va) - log 1 = exp(va - 2 log va).
  have h_eml_xM2L_one :
      (EMLTerm.eml (.eml (mkLog (.eml (mkLog a) a)) (.eml (mkLog a) .one)) .one).eval? env =
      some (Real.exp (va - 2 * Real.log va)) := by
    rw [eval?_eml_of_pos h_xM2L h1 zero_lt_one, Real.log_one, sub_zero]
  -- twoLog = eml logT (eml xM2L one) = exp(log va) - log(exp(va - 2 log va))
  --        = va - (va - 2 log va) = 2 log va.
  have h_twoLog :
      (EMLTerm.eml (mkLog a)
        (.eml (.eml (mkLog (.eml (mkLog a) a)) (.eml (mkLog a) .one)) .one)).eval? env =
      some (2 * Real.log va) := by
    rw [eval?_eml_of_pos h_logT h_eml_xM2L_one (Real.exp_pos _),
        Real.exp_log hpos, Real.log_exp]
    congr 1
    ring
  -- final: eml twoLog one = exp(2 log va) - log 1 = exp(2 log va) = va^2.
  rw [eval?_eml_of_pos h_twoLog h1 zero_lt_one, Real.log_one, sub_zero]
  congr 1
  rw [show (2 : ℝ) * Real.log va = Real.log va + Real.log va from by ring,
      Real.exp_add, Real.exp_log hpos, sq]

/-! ## `mkMulPos`: `a * b`, requires `0 < va` and `0 < vb`

Port of chunk 041. With `varX → a`, `varY → b`:
* `logA  := mkLog a` evaluates to `log(va)`.
* `xML   := eml logA a` evaluates to `va - log(va)` (positive).
* `logXML := mkLog xML` evaluates to `log(va - log(va))`.
* `mid   := eml logXML b = exp(log(va - log va)) - log(vb) = (va - log va) - log vb` (uses `0 < vb`).
* `wrap  := eml mid one = exp((va - log va) - log vb)`.
* `outer := eml logA wrap = exp(log va) - log(exp(...)) = va - ((va - log va) - log vb) = log va + log vb`.
* `mkMulPos a b := eml outer one = exp(log va + log vb) = va * vb`.
-/

/-- `mkMulPos a b` evaluates to `a.eval * b.eval` when `a.eval > 0` and `b.eval > 0`. -/
def mkMulPos (a b : EMLTerm) : EMLTerm :=
  let logA   : EMLTerm := mkLog a
  let xML    : EMLTerm := .eml logA a
  let logXML : EMLTerm := mkLog xML
  let mid    : EMLTerm := .eml logXML b
  let wrap   : EMLTerm := .eml mid .one
  let outer  : EMLTerm := .eml logA wrap
  .eml outer .one

/-- `mkMulPos` partial-eval spec: requires `0 < va` and `0 < vb`. -/
lemma mkMulPos_eval? (env : Nat → ℝ) (a b : EMLTerm) {va vb : ℝ}
    (ha : a.eval? env = some va) (hb : b.eval? env = some vb)
    (hap : 0 < va) (hbp : 0 < vb) :
    (mkMulPos a b).eval? env = some (va * vb) := by
  unfold mkMulPos
  have h1 : (EMLTerm.one).eval? env = some 1 := by simp
  -- log va.
  have h_logA : (mkLog a).eval? env = some (Real.log va) :=
    mkLog_eval? env a ha hap
  -- xML = va - log va.
  have h_xML : (EMLTerm.eml (mkLog a) a).eval? env = some (va - Real.log va) := by
    rw [eval?_eml_of_pos h_logA ha hap, Real.exp_log hap]
  have h_xML_pos : 0 < va - Real.log va := sub_log_pos hap
  -- log(va - log va).
  have h_logXML : (mkLog (.eml (mkLog a) a)).eval? env =
      some (Real.log (va - Real.log va)) :=
    mkLog_eval? env (.eml (mkLog a) a) h_xML h_xML_pos
  -- mid = eml logXML b = exp(log(va - log va)) - log vb = (va - log va) - log vb.
  have h_mid :
      (EMLTerm.eml (mkLog (.eml (mkLog a) a)) b).eval? env =
      some ((va - Real.log va) - Real.log vb) := by
    rw [eval?_eml_of_pos h_logXML hb hbp, Real.exp_log h_xML_pos]
  -- wrap = eml mid one = exp((va - log va) - log vb).
  have h_wrap :
      (EMLTerm.eml (.eml (mkLog (.eml (mkLog a) a)) b) .one).eval? env =
      some (Real.exp ((va - Real.log va) - Real.log vb)) := by
    rw [eval?_eml_of_pos h_mid h1 zero_lt_one, Real.log_one, sub_zero]
  -- outer = eml logA wrap = exp(log va) - log(exp((va - log va) - log vb))
  --       = va - ((va - log va) - log vb) = log va + log vb.
  have h_outer :
      (EMLTerm.eml (mkLog a)
        (.eml (.eml (mkLog (.eml (mkLog a) a)) b) .one)).eval? env =
      some (Real.log va + Real.log vb) := by
    rw [eval?_eml_of_pos h_logA h_wrap (Real.exp_pos _),
        Real.exp_log hap, Real.log_exp]
    congr 1
    ring
  -- final: eml outer one = exp(log va + log vb) - log 1 = exp(log va + log vb) = va * vb.
  rw [eval?_eml_of_pos h_outer h1 zero_lt_one, Real.log_one, sub_zero,
      Real.exp_add, Real.exp_log hap, Real.exp_log hbp]

end EMLTerm

end EML
