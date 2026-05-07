import EML.Framework.Builders
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Transcendental EML term builders

Compositional builders that take EMLTerm sub-terms and produce a new
EMLTerm whose partial evaluation is the corresponding transcendental
operation on the sub-terms' evaluations. Dispatched by the EL → EML
compiler for transcendental primitives.

* `mkSqrtPos a` — `√a` for `a > 0`,
* `mkPowPos a b` — `a^b` (`Real.rpow a b`) for `a, b > 0`,
* `mkDivPos a b` — `a / b` for `a, b > 0`,
* `mkHalvePos a` — `a / 2` for `a > 0`,
* `mkAvgPos a b` — `(a + b) / 2` for `a, b > 0`,
* `mkLogbPos a b` — `log_a b = log b / log a` for `1 < a` and `0 < b`,
* `mkHypotPos a b` — `√(a² + b²)` for `a, b > 0`.

Plus the closed helper `mkTwo : EMLTerm` evaluating to `2`.

Strategy notes:
* Each builder is built compositionally from a small set of inline
  helpers (`mkAddH`, `mkNegH`, `mkSubH`, `mkInvH`, `mkSqH`, `mkMulPosH`,
  `mkDivH`, plus the closed `mkTwo`/`mkHalfClosed`). The helpers port
  the proven witnesses in
  `Solutions/036/037/038/040/041/042/053`.
* `mkPowPos a b` uses chunk 042's identity
  `b * log a = b * (1/a + log a) − b/a`. Both `1/a + log a > 0`
  and `b > 0` make `mkMulPosH` applicable; `b/a` uses `mkDivH`
  (only divisor needs to be positive).
* `mkSqrtPos a := mkPowPos a mkHalfClosed`. The "half" closed term
  plays the role of chunk 039's `pow_term`-substitution trick: instead
  of materialising a one-variable `proj` map, we substitute by
  passing the closed `1/2`-witness directly as the second argument to
  `mkPowPos`.
* `mkHypotPos a b := mkSqrtPos (mkAddH (mkSqH a) (mkSqH b))`.
* `mkLogbPos a b := mkDivH (mkLog b) (mkLog a)`. The dividend
  `log b` may be negative (for `0 < b < 1`), so we cannot use the
  simpler `mkSubPos`-based division; chunk 053's `mkDiv` (only divisor
  needs positivity) is required.
-/

namespace EML

namespace EMLTerm

/-! ## Generic helper positivity facts -/

private lemma exp_sub_self_pos (x : ℝ) : 0 < Real.exp x - x := by
  linarith [Real.add_one_le_exp x]

private lemma sub_log_pos {x : ℝ} (hx : 0 < x) : 0 < x - Real.log x := by
  linarith [Real.log_le_sub_one_of_pos hx]

private lemma e_sub_one_pos : (0 : ℝ) < Real.exp 1 - 1 := by
  linarith [Real.add_one_le_exp (1 : ℝ)]

private lemma log_two_le_one : Real.log 2 ≤ 1 := by
  rw [show (1 : ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
  exact Real.log_le_log (by norm_num)
    (by linarith [Real.add_one_le_exp (1 : ℝ)])

private lemma e_sub_log_two_pos : (0 : ℝ) < Real.exp 1 - Real.log 2 := by
  linarith [e_sub_one_pos, log_two_le_one]

/-- `2 ≤ a + exp(1 - a)` for any real `a`; useful for chunk 053's mkDiv. -/
private lemma add_exp_one_sub_ge_two (a : ℝ) : 2 ≤ a + Real.exp (1 - a) := by
  linarith [Real.add_one_le_exp (1 - a)]

/-- `0 < a + exp(1 - a)` for any real `a`. -/
private lemma add_exp_one_sub_pos (a : ℝ) : 0 < a + Real.exp (1 - a) := by
  linarith [add_exp_one_sub_ge_two a]

/-- `0 < log(a + exp(1 - a))` for any real `a`. -/
private lemma log_add_exp_one_sub_pos (a : ℝ) :
    0 < Real.log (a + Real.exp (1 - a)) := by
  apply Real.log_pos
  linarith [add_exp_one_sub_ge_two a]

/-- `0 < a⁻¹ + log a` for `a > 0` (chunk 042's key positivity). -/
private lemma inv_add_log_pos {a : ℝ} (ha : 0 < a) :
    0 < a⁻¹ + Real.log a := by
  nlinarith [inv_pos.2 ha, mul_inv_cancel₀ ha.ne',
    Real.log_inv a ▸ Real.log_le_sub_one_of_pos (inv_pos.2 ha)]

/-! ## `mkAddH a b` — `a + b`, unconditional (port of chunk 040) -/

private def mkAddH (a b : EMLTerm) : EMLTerm :=
  let lhs : EMLTerm :=
    .eml .one (.eml (.eml .one (.eml a .one)) .one)
  let rhs : EMLTerm :=
    .eml
      (.eml (.eml .one (.eml (.eml .one (.eml a (.eml a .one))) .one))
            (.eml b .one))
      .one
  .eml lhs rhs

private lemma mkAddH_eval? (env : Nat → ℝ) (a b : EMLTerm) {va vb : ℝ}
    (ha : a.eval? env = some va) (hb : b.eval? env = some vb) :
    (mkAddH a b).eval? env = some (va + vb) := by
  unfold mkAddH
  have h1 : (EMLTerm.one).eval? env = some 1 := by simp
  have h_expA : (EMLTerm.eml a .one).eval? env = some (Real.exp va) := by
    rw [eval?_eml_of_pos ha h1 zero_lt_one, Real.log_one, sub_zero]
  have h_eml_one_expA :
      (EMLTerm.eml .one (.eml a .one)).eval? env =
      some (Real.exp 1 - va) := by
    rw [eval?_eml_of_pos h1 h_expA (Real.exp_pos _), Real.log_exp]
  have h_eml_eml_one_expA_one :
      (EMLTerm.eml (.eml .one (.eml a .one)) .one).eval? env =
      some (Real.exp (Real.exp 1 - va)) := by
    rw [eval?_eml_of_pos h_eml_one_expA h1 zero_lt_one, Real.log_one, sub_zero]
  have h_lhs :
      (EMLTerm.eml .one (.eml (.eml .one (.eml a .one)) .one)).eval? env =
      some va := by
    rw [eval?_eml_of_pos h1 h_eml_eml_one_expA_one (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  have h_w : (EMLTerm.eml a (.eml a .one)).eval? env =
      some (Real.exp va - va) := by
    rw [eval?_eml_of_pos ha h_expA (Real.exp_pos _), Real.log_exp]
  have h_w_pos : 0 < Real.exp va - va := exp_sub_self_pos va
  have h_eml_one_w :
      (EMLTerm.eml .one (.eml a (.eml a .one))).eval? env =
      some (Real.exp 1 - Real.log (Real.exp va - va)) :=
    eval?_eml_of_pos h1 h_w h_w_pos
  have h_eml_eml_one_w_one :
      (EMLTerm.eml (.eml .one (.eml a (.eml a .one))) .one).eval? env =
      some (Real.exp (Real.exp 1 - Real.log (Real.exp va - va))) := by
    rw [eval?_eml_of_pos h_eml_one_w h1 zero_lt_one, Real.log_one, sub_zero]
  have h_pos_inner : 0 < Real.exp (Real.exp 1 - Real.log (Real.exp va - va)) :=
    Real.exp_pos _
  have h_logW :
      (EMLTerm.eml .one (.eml (.eml .one (.eml a (.eml a .one))) .one)).eval? env =
      some (Real.log (Real.exp va - va)) := by
    rw [eval?_eml_of_pos h1 h_eml_eml_one_w_one h_pos_inner, Real.log_exp]
    congr 1
    ring
  have h_expB : (EMLTerm.eml b .one).eval? env = some (Real.exp vb) := by
    rw [eval?_eml_of_pos hb h1 zero_lt_one, Real.log_one, sub_zero]
  have h_mid :
      (EMLTerm.eml
        (.eml .one (.eml (.eml .one (.eml a (.eml a .one))) .one))
        (.eml b .one)).eval? env =
      some ((Real.exp va - va) - vb) := by
    rw [eval?_eml_of_pos h_logW h_expB (Real.exp_pos _),
        Real.exp_log h_w_pos, Real.log_exp]
  have h_wrap :
      (EMLTerm.eml
        (.eml (.eml .one (.eml (.eml .one (.eml a (.eml a .one))) .one))
              (.eml b .one))
        .one).eval? env =
      some (Real.exp ((Real.exp va - va) - vb)) := by
    rw [eval?_eml_of_pos h_mid h1 zero_lt_one, Real.log_one, sub_zero]
  rw [eval?_eml_of_pos h_lhs h_wrap (Real.exp_pos _), Real.log_exp]
  congr 1
  ring

/-! ## `mkNegH a` — `-a`, unconditional (port of chunk 036) -/

private def mkNegH (a : EMLTerm) : EMLTerm :=
  let w    : EMLTerm := .eml a (.eml a .one)
  let expA : EMLTerm := .eml a .one
  let logW : EMLTerm := .eml .one (.eml (.eml .one w) .one)
  .eml logW (.eml expA .one)

private lemma mkNegH_eval? (env : Nat → ℝ) (a : EMLTerm) {va : ℝ}
    (ha : a.eval? env = some va) :
    (mkNegH a).eval? env = some (-va) := by
  unfold mkNegH
  have h1 : (EMLTerm.one).eval? env = some 1 := by simp
  have h_expA : (EMLTerm.eml a .one).eval? env = some (Real.exp va) := by
    rw [eval?_eml_of_pos ha h1 zero_lt_one, Real.log_one, sub_zero]
  have h_w : (EMLTerm.eml a (.eml a .one)).eval? env =
      some (Real.exp va - va) := by
    rw [eval?_eml_of_pos ha h_expA (Real.exp_pos _), Real.log_exp]
  have h_w_pos : 0 < Real.exp va - va := exp_sub_self_pos va
  have h_eml_one_w : (EMLTerm.eml .one (.eml a (.eml a .one))).eval? env =
      some (Real.exp 1 - Real.log (Real.exp va - va)) :=
    eval?_eml_of_pos h1 h_w h_w_pos
  have h_eml_eml_one_w_one :
      (EMLTerm.eml (.eml .one (.eml a (.eml a .one))) .one).eval? env =
      some (Real.exp (Real.exp 1 - Real.log (Real.exp va - va))) := by
    rw [eval?_eml_of_pos h_eml_one_w h1 zero_lt_one, Real.log_one, sub_zero]
  have h_pos_inner : 0 < Real.exp (Real.exp 1 - Real.log (Real.exp va - va)) :=
    Real.exp_pos _
  have h_logW :
      (EMLTerm.eml .one (.eml (.eml .one (.eml a (.eml a .one))) .one)).eval? env =
      some (Real.log (Real.exp va - va)) := by
    rw [eval?_eml_of_pos h1 h_eml_eml_one_w_one h_pos_inner, Real.log_exp]
    congr 1
    ring
  have h_eml_expA_one : (EMLTerm.eml (.eml a .one) .one).eval? env =
      some (Real.exp (Real.exp va)) := by
    rw [eval?_eml_of_pos h_expA h1 zero_lt_one, Real.log_one, sub_zero]
  rw [eval?_eml_of_pos h_logW h_eml_expA_one (Real.exp_pos _),
      Real.exp_log h_w_pos, Real.log_exp]
  congr 1
  ring

/-! ## `mkSubH a b` — `a - b`, unconditional (defined as add + neg) -/

private def mkSubH (a b : EMLTerm) : EMLTerm := mkAddH a (mkNegH b)

private lemma mkSubH_eval? (env : Nat → ℝ) (a b : EMLTerm) {va vb : ℝ}
    (ha : a.eval? env = some va) (hb : b.eval? env = some vb) :
    (mkSubH a b).eval? env = some (va - vb) := by
  unfold mkSubH
  have h_neg : (mkNegH b).eval? env = some (-vb) := mkNegH_eval? env b hb
  have h := mkAddH_eval? env a (mkNegH b) ha h_neg
  simpa [sub_eq_add_neg] using h

/-! ## `mkInvH a` — `1/a` for `a > 0` (port of chunk 037) -/

private def mkInvH (a : EMLTerm) : EMLTerm :=
  let logT     : EMLTerm := mkLog a
  let xML      : EMLTerm := .eml logT a
  let logXML   : EMLTerm := mkLog xML
  let negLog   : EMLTerm := .eml logXML (.eml a .one)
  .eml negLog .one

private lemma mkInvH_eval? (env : Nat → ℝ) (a : EMLTerm) {va : ℝ}
    (ha : a.eval? env = some va) (hpos : 0 < va) :
    (mkInvH a).eval? env = some (1 / va) := by
  unfold mkInvH
  have h1 : (EMLTerm.one).eval? env = some 1 := by simp
  have h_logT : (mkLog a).eval? env = some (Real.log va) :=
    mkLog_eval? env a ha hpos
  have h_xML : (EMLTerm.eml (mkLog a) a).eval? env = some (va - Real.log va) := by
    rw [eval?_eml_of_pos h_logT ha hpos, Real.exp_log hpos]
  have h_xML_pos : 0 < va - Real.log va := sub_log_pos hpos
  have h_logXML : (mkLog (.eml (mkLog a) a)).eval? env =
      some (Real.log (va - Real.log va)) :=
    mkLog_eval? env (.eml (mkLog a) a) h_xML h_xML_pos
  have h_expA : (EMLTerm.eml a .one).eval? env = some (Real.exp va) := by
    rw [eval?_eml_of_pos ha h1 zero_lt_one, Real.log_one, sub_zero]
  have h_negLog :
      (EMLTerm.eml (mkLog (.eml (mkLog a) a)) (.eml a .one)).eval? env =
      some (-Real.log va) := by
    rw [eval?_eml_of_pos h_logXML h_expA (Real.exp_pos _),
        Real.exp_log h_xML_pos, Real.log_exp]
    congr 1
    ring
  rw [eval?_eml_of_pos h_negLog h1 zero_lt_one, Real.log_one, sub_zero,
      Real.exp_neg, Real.exp_log hpos, one_div]

/-! ## `mkSqH a` — `a^2` for `a > 0` (port of chunk 038) -/

private def mkSqH (a : EMLTerm) : EMLTerm :=
  let logT   : EMLTerm := mkLog a
  let xML    : EMLTerm := .eml logT a
  let logXML : EMLTerm := mkLog xML
  let xM2L   : EMLTerm := .eml logXML (.eml logT .one)
  let twoLog : EMLTerm := .eml logT (.eml xM2L .one)
  .eml twoLog .one

private lemma mkSqH_eval? (env : Nat → ℝ) (a : EMLTerm) {va : ℝ}
    (ha : a.eval? env = some va) (hpos : 0 < va) :
    (mkSqH a).eval? env = some (va ^ 2) := by
  unfold mkSqH
  have h1 : (EMLTerm.one).eval? env = some 1 := by simp
  have h_logT : (mkLog a).eval? env = some (Real.log va) :=
    mkLog_eval? env a ha hpos
  have h_xML : (EMLTerm.eml (mkLog a) a).eval? env = some (va - Real.log va) := by
    rw [eval?_eml_of_pos h_logT ha hpos, Real.exp_log hpos]
  have h_xML_pos : 0 < va - Real.log va := sub_log_pos hpos
  have h_logXML : (mkLog (.eml (mkLog a) a)).eval? env =
      some (Real.log (va - Real.log va)) :=
    mkLog_eval? env (.eml (mkLog a) a) h_xML h_xML_pos
  have h_eml_logT_one : (EMLTerm.eml (mkLog a) .one).eval? env = some va := by
    rw [eval?_eml_of_pos h_logT h1 zero_lt_one, Real.log_one, sub_zero,
        Real.exp_log hpos]
  have h_xM2L :
      (EMLTerm.eml (mkLog (.eml (mkLog a) a)) (.eml (mkLog a) .one)).eval? env =
      some (va - 2 * Real.log va) := by
    rw [eval?_eml_of_pos h_logXML h_eml_logT_one hpos,
        Real.exp_log h_xML_pos]
    congr 1
    ring
  have h_eml_xM2L_one :
      (EMLTerm.eml (.eml (mkLog (.eml (mkLog a) a)) (.eml (mkLog a) .one)) .one).eval? env =
      some (Real.exp (va - 2 * Real.log va)) := by
    rw [eval?_eml_of_pos h_xM2L h1 zero_lt_one, Real.log_one, sub_zero]
  have h_twoLog :
      (EMLTerm.eml (mkLog a)
        (.eml (.eml (mkLog (.eml (mkLog a) a)) (.eml (mkLog a) .one)) .one)).eval? env =
      some (2 * Real.log va) := by
    rw [eval?_eml_of_pos h_logT h_eml_xM2L_one (Real.exp_pos _),
        Real.exp_log hpos, Real.log_exp]
    congr 1
    ring
  rw [eval?_eml_of_pos h_twoLog h1 zero_lt_one, Real.log_one, sub_zero]
  congr 1
  rw [show (2 : ℝ) * Real.log va = Real.log va + Real.log va from by ring,
      Real.exp_add, Real.exp_log hpos, sq]

/-! ## `mkMulPosH a b` — `a * b` for `a, b > 0` (port of chunk 041) -/

private def mkMulPosH (a b : EMLTerm) : EMLTerm :=
  let logA   : EMLTerm := mkLog a
  let xML    : EMLTerm := .eml logA a
  let logXML : EMLTerm := mkLog xML
  let mid    : EMLTerm := .eml logXML b
  let wrap   : EMLTerm := .eml mid .one
  let outer  : EMLTerm := .eml logA wrap
  .eml outer .one

private lemma mkMulPosH_eval? (env : Nat → ℝ) (a b : EMLTerm) {va vb : ℝ}
    (ha : a.eval? env = some va) (hb : b.eval? env = some vb)
    (hap : 0 < va) (hbp : 0 < vb) :
    (mkMulPosH a b).eval? env = some (va * vb) := by
  unfold mkMulPosH
  have h1 : (EMLTerm.one).eval? env = some 1 := by simp
  have h_logA : (mkLog a).eval? env = some (Real.log va) :=
    mkLog_eval? env a ha hap
  have h_xML : (EMLTerm.eml (mkLog a) a).eval? env = some (va - Real.log va) := by
    rw [eval?_eml_of_pos h_logA ha hap, Real.exp_log hap]
  have h_xML_pos : 0 < va - Real.log va := sub_log_pos hap
  have h_logXML : (mkLog (.eml (mkLog a) a)).eval? env =
      some (Real.log (va - Real.log va)) :=
    mkLog_eval? env (.eml (mkLog a) a) h_xML h_xML_pos
  have h_mid :
      (EMLTerm.eml (mkLog (.eml (mkLog a) a)) b).eval? env =
      some ((va - Real.log va) - Real.log vb) := by
    rw [eval?_eml_of_pos h_logXML hb hbp, Real.exp_log h_xML_pos]
  have h_wrap :
      (EMLTerm.eml (.eml (mkLog (.eml (mkLog a) a)) b) .one).eval? env =
      some (Real.exp ((va - Real.log va) - Real.log vb)) := by
    rw [eval?_eml_of_pos h_mid h1 zero_lt_one, Real.log_one, sub_zero]
  have h_outer :
      (EMLTerm.eml (mkLog a)
        (.eml (.eml (mkLog (.eml (mkLog a) a)) b) .one)).eval? env =
      some (Real.log va + Real.log vb) := by
    rw [eval?_eml_of_pos h_logA h_wrap (Real.exp_pos _),
        Real.exp_log hap, Real.log_exp]
    congr 1
    ring
  rw [eval?_eml_of_pos h_outer h1 zero_lt_one, Real.log_one, sub_zero,
      Real.exp_add, Real.exp_log hap, Real.exp_log hbp]

/-! ## `mkDivH a c` — `a / c` for `c > 0` (chunk 053 style)

Algebra:
  `a / c = (a + e^(1-a)) / c − e^(1-a) / c`
  with `a + e^(1-a) > 0`. We materialise this as:
    `f := exp(log(log(a + e^(1-a))) − log(exp(log c)))`
       = `(a + e^(1-a)) / c` (when `log(a + e^(1-a)) > 0`),
    `g := mkSubH (mkOneMinusH a) (mkLog c) = (1 − a) − log c`,
    and the final `eml f (mkExp (mkExp g))`
       = `(a + e^(1-a))/c − exp((1-a)/c · ?)` ... see chunk 053 for the
    full derivation. Result is `a / c`.

This division only requires the divisor `c > 0`. The dividend `a` may
be any real (positive, zero, or negative). This is the asymmetric
division needed for `mkLogbPos` (where `log b` may be negative for
`0 < b < 1`).
-/

/-- `mkOneMinusH a` evaluates to `1 - a`, unconditionally. Built as
`eml mkZero (mkExp a)` analogue. -/
private def mkOneMinusH (a : EMLTerm) : EMLTerm :=
  -- `mkZero` is `eml(1, eml(eml(1,1), 1))` — its value is `0`.
  let mkZero : EMLTerm := .eml .one (.eml (.eml .one .one) .one)
  .eml mkZero (.eml a .one)

private lemma mkZero_inline_eval? (env : Nat → ℝ) :
    (EMLTerm.eml .one (.eml (.eml .one .one) .one)).eval? env = some 0 := by
  have h1 : (EMLTerm.one).eval? env = some 1 := by simp
  have h_e : (EMLTerm.eml .one .one).eval? env = some (Real.exp 1) := by
    have := eval?_eml_of_pos h1 h1 zero_lt_one
    simpa [Real.log_one] using this
  have h_expe :
      (EMLTerm.eml (.eml .one .one) .one).eval? env =
        some (Real.exp (Real.exp 1)) := by
    have := eval?_eml_of_pos h_e h1 zero_lt_one
    simpa [Real.log_one] using this
  have := eval?_eml_of_pos h1 h_expe (Real.exp_pos _)
  simpa [Real.log_exp] using this

private lemma mkOneMinusH_eval? (env : Nat → ℝ) (a : EMLTerm) {va : ℝ}
    (ha : a.eval? env = some va) :
    (mkOneMinusH a).eval? env = some (1 - va) := by
  unfold mkOneMinusH
  simp only []
  have h1 : (EMLTerm.one).eval? env = some 1 := by simp
  have h_zero : (EMLTerm.eml .one (.eml (.eml .one .one) .one)).eval? env =
      some 0 := mkZero_inline_eval? env
  have h_expA : (EMLTerm.eml a .one).eval? env = some (Real.exp va) := by
    rw [eval?_eml_of_pos ha h1 zero_lt_one, Real.log_one, sub_zero]
  have := eval?_eml_of_pos h_zero h_expA (Real.exp_pos _)
  rw [Real.exp_zero, Real.log_exp] at this
  exact this

/-- Chunk 053's `mkDiv` adapted: `a / c` for `c > 0`. -/
private def mkDivH (a c : EMLTerm) : EMLTerm :=
  let oma := mkOneMinusH a
  let apk := EMLTerm.eml oma (.eml (mkNegH a) .one)
       -- = exp(1-a) - log(exp(-a)) = exp(1-a) - (-a) = exp(1-a) + a
  let logApk := mkLog apk
  let logC := mkLog c
  let f := EMLTerm.eml (mkLog logApk) (.eml logC .one)
       -- = exp(log(log apk)) - log(exp(log c)) = log apk - log c (when log apk > 0)
  let g := mkSubH oma logC
       -- = (1 - a) - log c
  EMLTerm.eml f (.eml (.eml g .one) .one)
       -- = exp(log apk - log c) - log(exp(exp((1-a) - log c))) = apk/c - exp((1-a)-log c)
       -- = (a + e^(1-a))/c - e^(1-a)/c = a/c

private lemma mkDivH_eval? (env : Nat → ℝ) (a c : EMLTerm) {va vc : ℝ}
    (ha : a.eval? env = some va) (hc : c.eval? env = some vc)
    (hcp : 0 < vc) :
    (mkDivH a c).eval? env = some (va / vc) := by
  unfold mkDivH
  simp only []
  have h1 : (EMLTerm.one).eval? env = some 1 := by simp
  -- oma = 1 - va
  have h_oma : (mkOneMinusH a).eval? env = some (1 - va) :=
    mkOneMinusH_eval? env a ha
  -- mkNegH a = -va
  have h_neg : (mkNegH a).eval? env = some (-va) := mkNegH_eval? env a ha
  -- eml (mkNegH a) one = exp(-va)
  have h_exp_neg : (EMLTerm.eml (mkNegH a) .one).eval? env =
      some (Real.exp (-va)) := by
    rw [eval?_eml_of_pos h_neg h1 zero_lt_one, Real.log_one, sub_zero]
  -- apk = eml oma (eml (mkNegH a) one)
  --     = exp(1-va) - log(exp(-va)) = exp(1-va) - (-va) = exp(1-va) + va
  have h_apk_val_eq : Real.exp (1 - va) - Real.log (Real.exp (-va)) =
      va + Real.exp (1 - va) := by
    rw [Real.log_exp]; ring
  have h_apk : (EMLTerm.eml (mkOneMinusH a) (.eml (mkNegH a) .one)).eval? env =
      some (va + Real.exp (1 - va)) := by
    have := eval?_eml_of_pos h_oma h_exp_neg (Real.exp_pos _)
    rw [h_apk_val_eq] at this
    exact this
  have h_apk_pos : 0 < va + Real.exp (1 - va) := add_exp_one_sub_pos va
  -- logApk = log(va + exp(1 - va))
  have h_logApk : (mkLog (.eml (mkOneMinusH a) (.eml (mkNegH a) .one))).eval? env =
      some (Real.log (va + Real.exp (1 - va))) :=
    mkLog_eval? env _ h_apk h_apk_pos
  have h_logApk_pos : 0 < Real.log (va + Real.exp (1 - va)) :=
    log_add_exp_one_sub_pos va
  -- logC = log vc
  have h_logC : (mkLog c).eval? env = some (Real.log vc) :=
    mkLog_eval? env c hc hcp
  -- mkLog logApk = log(log(va + exp(1-va)))
  have h_log_logApk : (mkLog (mkLog
      (.eml (mkOneMinusH a) (.eml (mkNegH a) .one)))).eval? env =
      some (Real.log (Real.log (va + Real.exp (1 - va)))) :=
    mkLog_eval? env _ h_logApk h_logApk_pos
  -- eml logC one = exp(log vc) = vc
  have h_eml_logC_one : (EMLTerm.eml (mkLog c) .one).eval? env = some vc := by
    rw [eval?_eml_of_pos h_logC h1 zero_lt_one, Real.log_one, sub_zero,
        Real.exp_log hcp]
  -- f = eml (mkLog logApk) (eml logC one)
  --   = exp(log(log apk)) - log(vc) = log apk - log vc
  have h_f :
      (EMLTerm.eml (mkLog (mkLog (.eml (mkOneMinusH a) (.eml (mkNegH a) .one))))
        (.eml (mkLog c) .one)).eval? env =
      some (Real.log (va + Real.exp (1 - va)) - Real.log vc) := by
    rw [eval?_eml_of_pos h_log_logApk h_eml_logC_one hcp,
        Real.exp_log h_logApk_pos]
  -- g = mkSubH oma logC = (1 - va) - log vc
  have h_g : (mkSubH (mkOneMinusH a) (mkLog c)).eval? env =
      some ((1 - va) - Real.log vc) :=
    mkSubH_eval? env _ _ h_oma h_logC
  -- eml g one = exp((1-va) - log vc)
  have h_exp_g : (EMLTerm.eml (mkSubH (mkOneMinusH a) (mkLog c)) .one).eval? env =
      some (Real.exp ((1 - va) - Real.log vc)) := by
    rw [eval?_eml_of_pos h_g h1 zero_lt_one, Real.log_one, sub_zero]
  -- eml (eml g one) one = exp(exp((1-va) - log vc))
  have h_exp_exp_g :
      (EMLTerm.eml (.eml (mkSubH (mkOneMinusH a) (mkLog c)) .one) .one).eval? env =
      some (Real.exp (Real.exp ((1 - va) - Real.log vc))) := by
    rw [eval?_eml_of_pos h_exp_g h1 zero_lt_one, Real.log_one, sub_zero]
  -- final: eml f (eml (eml g one) one)
  --   = exp(log apk - log vc) - log(exp(exp((1-va) - log vc)))
  --   = (a + e^(1-a))/vc - exp((1-va) - log vc)
  --   = (a + e^(1-a))/vc - e^(1-va)/vc
  --   = a/vc
  have h_pos_exp_exp_g : 0 < Real.exp (Real.exp ((1 - va) - Real.log vc)) :=
    Real.exp_pos _
  have hfinal := eval?_eml_of_pos h_f h_exp_exp_g h_pos_exp_exp_g
  -- Simplify the resulting RHS.
  have hrew :
      Real.exp (Real.log (va + Real.exp (1 - va)) - Real.log vc) -
        Real.log (Real.exp (Real.exp ((1 - va) - Real.log vc))) =
        va / vc := by
    rw [Real.log_exp]
    rw [Real.exp_sub, Real.exp_log h_apk_pos]
    rw [show (1 - va) - Real.log vc = (1 - va) + (-Real.log vc) from by ring,
        Real.exp_add, Real.exp_neg, Real.exp_log hcp]
    field_simp
    ring
  rw [hrew] at hfinal
  exact hfinal

/-! ## Closed `mkTwo` (= 2) and `mkHalfClosed` (= 1/2)

These are private to this file; the public API is in
`EML/Framework/Builders/Constants.lean` (`Constants.mkTwo`,
`Constants.mkHalf`). Localising them here avoids a cross-file
dependency in this file. -/

/-- Closed EML term whose partial evaluation is `2`. Port of chunk 032. -/
private def mkTwo : EMLTerm :=
  let t₂ : EMLTerm := .eml .one .one
  let t₃ : EMLTerm := .eml .one t₂
  let t₄ : EMLTerm := .eml .one t₃
  let t₅ : EMLTerm := .eml t₄ .one
  let t₆ : EMLTerm := .eml .one t₅
  let t₇ : EMLTerm := .eml t₆ t₂
  let t₈ : EMLTerm := .eml t₇ .one
  .eml .one t₈

/-- `mkTwo` partial-eval spec: always `some 2`. -/
private lemma mkTwo_eval? (env : Nat → ℝ) : mkTwo.eval? env = some 2 := by
  unfold mkTwo
  simp only []
  have h1 : (EMLTerm.one).eval? env = some 1 := by simp
  have h_t2 : (EMLTerm.eml .one .one).eval? env = some (Real.exp 1) := by
    have := eval?_eml_of_pos h1 h1 zero_lt_one
    simpa [Real.log_one] using this
  have h_t3 : (EMLTerm.eml .one (.eml .one .one)).eval? env =
      some (Real.exp 1 - 1) := by
    have := eval?_eml_of_pos h1 h_t2 (Real.exp_pos 1)
    simpa [Real.log_exp] using this
  have h_t4 :
      (EMLTerm.eml .one (.eml .one (.eml .one .one))).eval? env =
        some (Real.exp 1 - Real.log (Real.exp 1 - 1)) :=
    eval?_eml_of_pos h1 h_t3 e_sub_one_pos
  have h_t5 :
      (EMLTerm.eml (.eml .one (.eml .one (.eml .one .one))) .one).eval? env =
        some (Real.exp (Real.exp 1 - Real.log (Real.exp 1 - 1))) := by
    have := eval?_eml_of_pos h_t4 h1 zero_lt_one
    simpa [Real.log_one] using this
  have h_pos_t5 :
      0 < Real.exp (Real.exp 1 - Real.log (Real.exp 1 - 1)) := Real.exp_pos _
  have h_t6 :
      (EMLTerm.eml .one
        (.eml (.eml .one (.eml .one (.eml .one .one))) .one)).eval? env =
        some (Real.log (Real.exp 1 - 1)) := by
    have := eval?_eml_of_pos h1 h_t5 h_pos_t5
    have hrewrite : Real.exp 1 -
        Real.log (Real.exp (Real.exp 1 - Real.log (Real.exp 1 - 1))) =
        Real.log (Real.exp 1 - 1) := by
      rw [Real.log_exp]; ring
    rw [hrewrite] at this
    exact this
  have h_t7 :
      (EMLTerm.eml
          (.eml .one (.eml (.eml .one (.eml .one (.eml .one .one))) .one))
          (.eml .one .one)).eval? env =
        some (Real.exp 1 - 2) := by
    have := eval?_eml_of_pos h_t6 h_t2 (Real.exp_pos 1)
    have hrewrite :
        Real.exp (Real.log (Real.exp 1 - 1)) - Real.log (Real.exp 1) =
        Real.exp 1 - 2 := by
      rw [Real.exp_log e_sub_one_pos, Real.log_exp]
      ring
    rw [hrewrite] at this
    exact this
  have h_t8 :
      (EMLTerm.eml
          (.eml
            (.eml .one (.eml (.eml .one (.eml .one (.eml .one .one))) .one))
            (.eml .one .one))
          .one).eval? env =
        some (Real.exp (Real.exp 1 - 2)) := by
    have := eval?_eml_of_pos h_t7 h1 zero_lt_one
    simpa [Real.log_one] using this
  have h_pos_t8 : 0 < Real.exp (Real.exp 1 - 2) := Real.exp_pos _
  have hfinal := eval?_eml_of_pos h1 h_t8 h_pos_t8
  have hrewrite : Real.exp 1 - Real.log (Real.exp (Real.exp 1 - 2)) = 2 := by
    rw [Real.log_exp]; ring
  rw [hrewrite] at hfinal
  exact hfinal

/-- Closed EML term whose partial evaluation is `1/2`. Port of chunk 033. -/
private def mkHalfClosed : EMLTerm :=
  let Z : EMLTerm := .eml .one (.eml (.eml .one .one) .one)
  let Lg : EMLTerm → EMLTerm := fun t => .eml Z (.eml (.eml Z t) .one)
  let e1 : EMLTerm := .eml .one (.eml .one .one)
  let log_e1 : EMLTerm := Lg e1
  let e2 : EMLTerm := .eml log_e1 (.eml .one .one)
  let exp_e2 : EMLTerm := .eml e2 .one
  let two_ : EMLTerm := .eml .one exp_e2
  let eml2 : EMLTerm := .eml .one two_
  let log_eml2 : EMLTerm := Lg eml2
  let neg_log2 : EMLTerm :=
    .eml log_eml2 (.eml (.eml .one .one) .one)
  .eml neg_log2 .one

private lemma mkHalfClosed_eval? (env : Nat → ℝ) :
    mkHalfClosed.eval? env = some (1 / 2) := by
  unfold mkHalfClosed
  simp only []
  have h1 : (EMLTerm.one).eval? env = some 1 := by simp
  have h_Z : (EMLTerm.eml (EMLTerm.one)
      (.eml (.eml .one .one) .one)).eval? env = some 0 :=
    mkZero_inline_eval? env
  have h_e_const : (EMLTerm.eml .one .one).eval? env = some (Real.exp 1) := by
    have := eval?_eml_of_pos h1 h1 zero_lt_one
    simpa [Real.log_one] using this
  have h_e1 : (EMLTerm.eml .one (.eml .one .one)).eval? env =
      some (Real.exp 1 - 1) := by
    have := eval?_eml_of_pos h1 h_e_const (Real.exp_pos _)
    simpa [Real.log_exp] using this
  have h_eml_Z_e1 :
      (EMLTerm.eml (.eml .one (.eml (.eml .one .one) .one))
        (.eml .one (.eml .one .one))).eval? env =
        some (1 - Real.log (Real.exp 1 - 1)) := by
    have := eval?_eml_of_pos h_Z h_e1 e_sub_one_pos
    simpa [Real.exp_zero] using this
  have h_mid_e1 :
      (EMLTerm.eml
          (.eml (.eml .one (.eml (.eml .one .one) .one))
            (.eml .one (.eml .one .one)))
          .one).eval? env =
        some (Real.exp (1 - Real.log (Real.exp 1 - 1))) := by
    have := eval?_eml_of_pos h_eml_Z_e1 h1 zero_lt_one
    simpa [Real.log_one] using this
  have h_pos_mid_e1 : 0 < Real.exp (1 - Real.log (Real.exp 1 - 1)) :=
    Real.exp_pos _
  have h_log_e1 :
      (EMLTerm.eml (.eml .one (.eml (.eml .one .one) .one))
        (.eml
          (.eml (.eml .one (.eml (.eml .one .one) .one))
            (.eml .one (.eml .one .one)))
          .one)).eval? env =
        some (Real.log (Real.exp 1 - 1)) := by
    have := eval?_eml_of_pos h_Z h_mid_e1 h_pos_mid_e1
    have hrew :
        Real.exp 0 - Real.log (Real.exp (1 - Real.log (Real.exp 1 - 1))) =
          Real.log (Real.exp 1 - 1) := by
      rw [Real.exp_zero, Real.log_exp]; ring
    rw [hrew] at this
    exact this
  have h_e2 :
      (EMLTerm.eml
          (.eml (.eml .one (.eml (.eml .one .one) .one))
            (.eml
              (.eml (.eml .one (.eml (.eml .one .one) .one))
                (.eml .one (.eml .one .one)))
              .one))
          (.eml .one .one)).eval? env =
        some (Real.exp 1 - 2) := by
    have := eval?_eml_of_pos h_log_e1 h_e_const (Real.exp_pos _)
    have hrew :
        Real.exp (Real.log (Real.exp 1 - 1)) - Real.log (Real.exp 1) =
        Real.exp 1 - 2 := by
      rw [Real.exp_log e_sub_one_pos, Real.log_exp]; ring
    rw [hrew] at this
    exact this
  have h_exp_e2 :
      (EMLTerm.eml
          (.eml
            (.eml (.eml .one (.eml (.eml .one .one) .one))
              (.eml
                (.eml (.eml .one (.eml (.eml .one .one) .one))
                  (.eml .one (.eml .one .one)))
                .one))
            (.eml .one .one))
          .one).eval? env =
        some (Real.exp (Real.exp 1 - 2)) := by
    have := eval?_eml_of_pos h_e2 h1 zero_lt_one
    simpa [Real.log_one] using this
  have h_pos_exp_e2 : 0 < Real.exp (Real.exp 1 - 2) := Real.exp_pos _
  have h_two :
      (EMLTerm.eml .one
        (.eml
          (.eml
            (.eml (.eml .one (.eml (.eml .one .one) .one))
              (.eml
                (.eml (.eml .one (.eml (.eml .one .one) .one))
                  (.eml .one (.eml .one .one)))
                .one))
            (.eml .one .one))
          .one)).eval? env = some 2 := by
    have := eval?_eml_of_pos h1 h_exp_e2 h_pos_exp_e2
    have hrew : Real.exp 1 - Real.log (Real.exp (Real.exp 1 - 2)) = 2 := by
      rw [Real.log_exp]; ring
    rw [hrew] at this
    exact this
  have h_eml2 :
      (EMLTerm.eml .one
        (.eml .one
          (.eml
            (.eml
              (.eml (.eml .one (.eml (.eml .one .one) .one))
                (.eml
                  (.eml (.eml .one (.eml (.eml .one .one) .one))
                    (.eml .one (.eml .one .one)))
                  .one))
              (.eml .one .one))
            .one))).eval? env = some (Real.exp 1 - Real.log 2) :=
    eval?_eml_of_pos h1 h_two (by norm_num)
  have h_eml_Z_eml2 :
      (EMLTerm.eml (.eml .one (.eml (.eml .one .one) .one))
        (.eml .one
          (.eml .one
            (.eml
              (.eml
                (.eml (.eml .one (.eml (.eml .one .one) .one))
                  (.eml
                    (.eml (.eml .one (.eml (.eml .one .one) .one))
                      (.eml .one (.eml .one .one)))
                    .one))
                (.eml .one .one))
              .one)))).eval? env =
        some (1 - Real.log (Real.exp 1 - Real.log 2)) := by
    have := eval?_eml_of_pos h_Z h_eml2 e_sub_log_two_pos
    simpa [Real.exp_zero] using this
  have h_mid_eml2 :
      (EMLTerm.eml
          (.eml (.eml .one (.eml (.eml .one .one) .one))
            (.eml .one
              (.eml .one
                (.eml
                  (.eml
                    (.eml (.eml .one (.eml (.eml .one .one) .one))
                      (.eml
                        (.eml (.eml .one (.eml (.eml .one .one) .one))
                          (.eml .one (.eml .one .one)))
                        .one))
                    (.eml .one .one))
                  .one))))
          .one).eval? env =
        some (Real.exp (1 - Real.log (Real.exp 1 - Real.log 2))) := by
    have := eval?_eml_of_pos h_eml_Z_eml2 h1 zero_lt_one
    simpa [Real.log_one] using this
  have h_pos_mid_eml2 :
      0 < Real.exp (1 - Real.log (Real.exp 1 - Real.log 2)) := Real.exp_pos _
  have h_log_eml2 :
      (EMLTerm.eml (.eml .one (.eml (.eml .one .one) .one))
        (.eml
          (.eml (.eml .one (.eml (.eml .one .one) .one))
            (.eml .one
              (.eml .one
                (.eml
                  (.eml
                    (.eml (.eml .one (.eml (.eml .one .one) .one))
                      (.eml
                        (.eml (.eml .one (.eml (.eml .one .one) .one))
                          (.eml .one (.eml .one .one)))
                        .one))
                    (.eml .one .one))
                  .one))))
          .one)).eval? env = some (Real.log (Real.exp 1 - Real.log 2)) := by
    have := eval?_eml_of_pos h_Z h_mid_eml2 h_pos_mid_eml2
    have hrew :
        Real.exp 0 -
            Real.log (Real.exp (1 - Real.log (Real.exp 1 - Real.log 2))) =
          Real.log (Real.exp 1 - Real.log 2) := by
      rw [Real.exp_zero, Real.log_exp]; ring
    rw [hrew] at this
    exact this
  have h_exp_exp1 :
      (EMLTerm.eml (.eml .one .one) .one).eval? env =
        some (Real.exp (Real.exp 1)) := by
    have := eval?_eml_of_pos h_e_const h1 zero_lt_one
    simpa [Real.log_one] using this
  have h_pos_exp_exp1 : 0 < Real.exp (Real.exp 1) := Real.exp_pos _
  have h_neg_log2 :
      (EMLTerm.eml
          (.eml (.eml .one (.eml (.eml .one .one) .one))
            (.eml
              (.eml (.eml .one (.eml (.eml .one .one) .one))
                (.eml .one
                  (.eml .one
                    (.eml
                      (.eml
                        (.eml (.eml .one (.eml (.eml .one .one) .one))
                          (.eml
                            (.eml (.eml .one (.eml (.eml .one .one) .one))
                              (.eml .one (.eml .one .one)))
                            .one))
                        (.eml .one .one))
                      .one))))
              .one))
          (.eml (.eml .one .one) .one)).eval? env = some (-Real.log 2) := by
    have := eval?_eml_of_pos h_log_eml2 h_exp_exp1 h_pos_exp_exp1
    have hrew :
        Real.exp (Real.log (Real.exp 1 - Real.log 2)) -
            Real.log (Real.exp (Real.exp 1)) =
          -Real.log 2 := by
      rw [Real.exp_log e_sub_log_two_pos, Real.log_exp]; ring
    rw [hrew] at this
    exact this
  have hfinal := eval?_eml_of_pos h_neg_log2 h1 zero_lt_one
  have hrew : Real.exp (-Real.log 2) - Real.log 1 = 1 / 2 := by
    rw [Real.log_one, sub_zero, Real.exp_neg,
        Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [hrew] at hfinal
  exact hfinal

/-! ## Public builder: `mkPowPos a b` — `a^b` for `a, b > 0`

Identity (chunk 042): `b * log a = b * (1/a + log a) - b/a`.
Both factors are positive: `b > 0` and `1/a + log a > 0` (for `a > 0`).
Then `mkExp` lifts to `a^b`. -/

/-- `mkPowPos a b` evaluates to `Real.rpow a.eval b.eval` when both
`a.eval > 0` and `b.eval > 0`. -/
def mkPowPos (a b : EMLTerm) : EMLTerm :=
  -- inv_a_plus_log_a := mkAddH (mkInvH a) (mkLog a)   (positive when a > 0)
  -- prod              := mkMulPosH b inv_a_plus_log_a (positive when b > 0)
  -- div               := mkDivH b a                   (b/a; only divisor > 0 needed)
  -- exponent          := mkSubH prod div              (= b * log a)
  -- result            := mkExp exponent
  mkExp (mkSubH (mkMulPosH b (mkAddH (mkInvH a) (mkLog a))) (mkDivH b a))

/-- `mkPowPos` partial-eval spec: requires `0 < va` and `0 < vb`. -/
lemma mkPowPos_eval? (env : Nat → ℝ) (a b : EMLTerm) {va vb : ℝ}
    (ha : a.eval? env = some va) (hb : b.eval? env = some vb)
    (hap : 0 < va) (hbp : 0 < vb) :
    (mkPowPos a b).eval? env = some (Real.rpow va vb) := by
  unfold mkPowPos
  -- 1/a
  have h_inv : (mkInvH a).eval? env = some (1 / va) := mkInvH_eval? env a ha hap
  -- log a
  have h_log : (mkLog a).eval? env = some (Real.log va) :=
    mkLog_eval? env a ha hap
  -- 1/a + log a
  have h_inv_plus_log : (mkAddH (mkInvH a) (mkLog a)).eval? env =
      some (1 / va + Real.log va) := mkAddH_eval? env _ _ h_inv h_log
  have h_inv_plus_log_pos : 0 < 1 / va + Real.log va := by
    have := inv_add_log_pos hap
    rwa [show va⁻¹ = 1 / va from (one_div va).symm] at this
  -- b * (1/a + log a)
  have h_prod : (mkMulPosH b (mkAddH (mkInvH a) (mkLog a))).eval? env =
      some (vb * (1 / va + Real.log va)) :=
    mkMulPosH_eval? env _ _ hb h_inv_plus_log hbp h_inv_plus_log_pos
  -- b / a
  have h_div : (mkDivH b a).eval? env = some (vb / va) :=
    mkDivH_eval? env b a hb ha hap
  -- prod - div
  have h_sub : (mkSubH (mkMulPosH b (mkAddH (mkInvH a) (mkLog a))) (mkDivH b a)).eval? env
      = some (vb * (1 / va + Real.log va) - vb / va) :=
    mkSubH_eval? env _ _ h_prod h_div
  -- Simplify: vb * (1/va + log va) - vb/va = vb/va + vb * log va - vb/va = vb * log va
  have h_alg : vb * (1 / va + Real.log va) - vb / va = vb * Real.log va := by
    have hva_ne : va ≠ 0 := ne_of_gt hap
    field_simp
    ring
  rw [h_alg] at h_sub
  -- mkExp on the result
  have hres : (mkExp _).eval? env = some (Real.exp (vb * Real.log va)) :=
    mkExp_eval? env _ h_sub
  -- Now relate exp(vb * log va) to Real.rpow va vb
  rw [hres]
  congr 1
  show Real.exp (vb * Real.log va) = Real.rpow va vb
  rw [show Real.rpow va vb = va ^ vb from rfl, Real.rpow_def_of_pos hap,
      mul_comm vb (Real.log va)]

/-! ## Public builder: `mkSqrtPos a` — `√a` for `a > 0`

Uses the chunk-039 substitution trick: `√a = a^(1/2)`, where `1/2` is
materialised as the closed term `mkHalfClosed`. -/

/-- `mkSqrtPos a` evaluates to `Real.sqrt a.eval` when `a.eval > 0`. -/
def mkSqrtPos (a : EMLTerm) : EMLTerm := mkPowPos a mkHalfClosed

/-- `mkSqrtPos` partial-eval spec: requires `0 < va`. -/
lemma mkSqrtPos_eval? (env : Nat → ℝ) (a : EMLTerm) {va : ℝ}
    (ha : a.eval? env = some va) (hpos : 0 < va) :
    (mkSqrtPos a).eval? env = some (Real.sqrt va) := by
  unfold mkSqrtPos
  have h_half : mkHalfClosed.eval? env = some (1 / 2) := mkHalfClosed_eval? env
  have h := mkPowPos_eval? env a mkHalfClosed ha h_half hpos (by norm_num : (0:ℝ) < 1/2)
  rw [h]
  congr 1
  rw [Real.sqrt_eq_rpow]
  rfl

/-! ## Public builder: `mkDivPos a b` — `a / b` for `a, b > 0` -/

/-- `mkDivPos a b` evaluates to `a.eval / b.eval` when `a.eval, b.eval > 0`. -/
def mkDivPos (a b : EMLTerm) : EMLTerm := mkDivH a b

/-- `mkDivPos` partial-eval spec: requires `0 < va` and `0 < vb`. -/
lemma mkDivPos_eval? (env : Nat → ℝ) (a b : EMLTerm) {va vb : ℝ}
    (ha : a.eval? env = some va) (hb : b.eval? env = some vb)
    (_hap : 0 < va) (hbp : 0 < vb) :
    (mkDivPos a b).eval? env = some (va / vb) := by
  unfold mkDivPos
  exact mkDivH_eval? env a b ha hb hbp

/-! ## Public builder: `mkHalvePos a` — `a / 2` for `a > 0` -/

/-- `mkHalvePos a` evaluates to `a.eval / 2` when `a.eval > 0`. -/
def mkHalvePos (a : EMLTerm) : EMLTerm := mkDivH a mkTwo

/-- `mkHalvePos` partial-eval spec: requires `0 < va`. -/
lemma mkHalvePos_eval? (env : Nat → ℝ) (a : EMLTerm) {va : ℝ}
    (ha : a.eval? env = some va) (_hpos : 0 < va) :
    (mkHalvePos a).eval? env = some (va / 2) := by
  unfold mkHalvePos
  have h_two : mkTwo.eval? env = some 2 := mkTwo_eval? env
  exact mkDivH_eval? env a mkTwo ha h_two (by norm_num)

/-! ## Public builder: `mkAvgPos a b` — `(a + b) / 2` for `a, b > 0` -/

/-- `mkAvgPos a b` evaluates to `(a.eval + b.eval) / 2`. -/
def mkAvgPos (a b : EMLTerm) : EMLTerm := mkHalvePos (mkAddH a b)

/-- `mkAvgPos` partial-eval spec: requires `0 < va` and `0 < vb`. -/
lemma mkAvgPos_eval? (env : Nat → ℝ) (a b : EMLTerm) {va vb : ℝ}
    (ha : a.eval? env = some va) (hb : b.eval? env = some vb)
    (hap : 0 < va) (hbp : 0 < vb) :
    (mkAvgPos a b).eval? env = some ((va + vb) / 2) := by
  unfold mkAvgPos
  have h_sum : (mkAddH a b).eval? env = some (va + vb) :=
    mkAddH_eval? env a b ha hb
  have h_sum_pos : 0 < va + vb := by linarith
  exact mkHalvePos_eval? env (mkAddH a b) h_sum h_sum_pos

/-! ## Public builder: `mkLogbPos a b` — `log_a b` for `1 < a, 0 < b`

`log_a b = log b / log a`. Since `log a > 0` (from `1 < a`), the
asymmetric `mkDivH` (only divisor must be positive) handles the
possibly-negative dividend `log b`. -/

/-- `mkLogbPos a b` evaluates to `Real.log b.eval / Real.log a.eval`
when `1 < a.eval` and `0 < b.eval`. -/
def mkLogbPos (a b : EMLTerm) : EMLTerm := mkDivH (mkLog b) (mkLog a)

/-- `mkLogbPos` partial-eval spec: requires `1 < va` and `0 < vb`. -/
lemma mkLogbPos_eval? (env : Nat → ℝ) (a b : EMLTerm) {va vb : ℝ}
    (ha : a.eval? env = some va) (hb : b.eval? env = some vb)
    (hap : 1 < va) (hbp : 0 < vb) :
    (mkLogbPos a b).eval? env = some (Real.log vb / Real.log va) := by
  unfold mkLogbPos
  have ha_pos : 0 < va := lt_trans zero_lt_one hap
  have h_loga : (mkLog a).eval? env = some (Real.log va) :=
    mkLog_eval? env a ha ha_pos
  have h_logb : (mkLog b).eval? env = some (Real.log vb) :=
    mkLog_eval? env b hb hbp
  have h_loga_pos : 0 < Real.log va := Real.log_pos hap
  exact mkDivH_eval? env (mkLog b) (mkLog a) h_logb h_loga h_loga_pos

/-! ## Public builder: `mkHypotPos a b` — `√(a² + b²)` for `a, b > 0` -/

/-- `mkHypotPos a b` evaluates to `Real.sqrt (a.eval² + b.eval²)`. -/
def mkHypotPos (a b : EMLTerm) : EMLTerm := mkSqrtPos (mkAddH (mkSqH a) (mkSqH b))

/-- `mkHypotPos` partial-eval spec: requires `0 < va` and `0 < vb`. -/
lemma mkHypotPos_eval? (env : Nat → ℝ) (a b : EMLTerm) {va vb : ℝ}
    (ha : a.eval? env = some va) (hb : b.eval? env = some vb)
    (hap : 0 < va) (hbp : 0 < vb) :
    (mkHypotPos a b).eval? env = some (Real.sqrt (va ^ 2 + vb ^ 2)) := by
  unfold mkHypotPos
  have h_sqa : (mkSqH a).eval? env = some (va ^ 2) := mkSqH_eval? env a ha hap
  have h_sqb : (mkSqH b).eval? env = some (vb ^ 2) := mkSqH_eval? env b hb hbp
  have h_sum : (mkAddH (mkSqH a) (mkSqH b)).eval? env =
      some (va ^ 2 + vb ^ 2) := mkAddH_eval? env _ _ h_sqa h_sqb
  have h_sum_pos : 0 < va ^ 2 + vb ^ 2 := by positivity
  exact mkSqrtPos_eval? env (mkAddH (mkSqH a) (mkSqH b)) h_sum h_sum_pos

end EMLTerm

end EML
