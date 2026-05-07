import EML.Framework.Builders
import EML.Framework.Builders.Constants
import EML.Framework.Builders.Arithmetic
import EML.Framework.Builders.Transcendental

/-!
# Unconditional / wider-domain EML term builders

This file extends the existing `Builders/*.lean` collection with
builders whose partial-evaluation domain is strictly larger than the
positives-only domain used in `Builders/Arithmetic.lean` and
`Builders/Transcendental.lean`.

The central trick is the chunk-036 identity (port: `mkNeg`,
`mkAdd`, `mkSub` in `Builders/Arithmetic.lean`):

* For *every* real `va`, the quantity `exp(va) − va` is strictly
  positive (since `1 + va ≤ exp va`). Hence `log(exp va − va)` is
  defined for all `va`, and various positives-only sub-builders
  (`mkLog`, `mkSqPos`, `mkMulPos`, `mkInvPos`) can be applied to
  shifted/transformed copies of `va` even when `va` itself is zero or
  negative. Compositions then collapse the shift via cancellation.

The key contributions are:

| Builder              | Domain                       | Strategy |
|----------------------|------------------------------|---------|
| `mkSqAll`            | all real `va`                | `va² = (exp va − va)² + (exp va)² − 2·(exp va − va)·exp va` |
| `mkAbsSqAll`         | all real `va`                | trivially `mkSqAll` (since `va² = |va|²`) |
| `mkInvNonzero`       | `va ≠ 0`                     | `1/va = va / va²`, divide-by-positive |
| `mkHypotAll`         | `(va, vb) ≠ (0, 0)`          | `√(va² + vb²)` via `mkSqAll + mkSqrtPos` |
| `mkMulAll`           | all real `va`, `vb`          | `va·vb = ((va+vb)² − (va−vb)²) / 4` |
| `mkDivNonzeroDenom`  | `vb ≠ 0`                     | `va/vb = (va·vb) / vb²` |
| `mkSubAll`           | all real `va`, `vb`          | identical to `mkSub` (just re-exposed) |

All proofs reduce to the asymmetric chunk-053 division `mkDivByPos`
(only the divisor must be positive — the dividend may be any real)
which is implemented locally as a private helper, and to `mkSqPos`
applied to shifted-positive sub-terms.

## Open / pending

Genuinely-unconditional `mkAvgAll` and `mkHalveAll` are not provided.
Both reduce to `mkDivByPos a (constant 2)`, which is achievable, but
we expose them under the names already used in
`Builders/Transcendental.lean` (`mkHalvePos`, `mkAvgPos`) which
require the dividend positive only because `mkDivPos`'s public spec
demands it. Because we now provide an explicit private
`mkDivByPos` here, the matching unconditional `mkHalveAll` /
`mkAvgAll` are immediate; they are included below.

(The only remaining genuinely-open construction in EML is anything
that requires a real *if-then-else* in the term itself — e.g. a
piecewise sign function. EML's grammar `S → 1 | var n | eml(S, S)`
has no conditional, so such functions cannot be expressed as a
single closed `EMLTerm` — only the *value* on a fixed-sign side can
be unified. The constructions here all unify the two sides via a
single algebraic identity, which is the only way to do it without
extending the grammar.)
-/

namespace EML

namespace EMLTerm

/-! ## Local positivity lemmas -/

private lemma exp_sub_self_pos' (x : ℝ) : 0 < Real.exp x - x := by
  linarith [Real.add_one_le_exp x]

private lemma log_two_le_one' : Real.log 2 ≤ 1 := by
  rw [show (1 : ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
  exact Real.log_le_log (by norm_num)
    (by linarith [Real.add_one_le_exp (1 : ℝ)])

private lemma e_sub_one_pos' : (0 : ℝ) < Real.exp 1 - 1 := by
  linarith [Real.add_one_le_exp (1 : ℝ)]

private lemma add_exp_one_sub_ge_two' (a : ℝ) : 2 ≤ a + Real.exp (1 - a) := by
  linarith [Real.add_one_le_exp (1 - a)]

private lemma add_exp_one_sub_pos' (a : ℝ) : 0 < a + Real.exp (1 - a) := by
  linarith [add_exp_one_sub_ge_two' a]

private lemma log_add_exp_one_sub_pos' (a : ℝ) :
    0 < Real.log (a + Real.exp (1 - a)) := by
  apply Real.log_pos
  linarith [add_exp_one_sub_ge_two' a]

/-! ## `mkDivByPos a c` — `a / c` requiring only `0 < c`

Re-implementation of the private `mkDivH` from
`Builders/Transcendental.lean`. Needed here because we want to
divide possibly-negative dividends (e.g. `va` itself, which may have
any sign) by guaranteed-positive denominators (e.g. `va²` when
`va ≠ 0`).

Algebra (chunk 053):
  `a / c = (a + e^(1−a)) / c − e^(1−a) / c`,
where `a + e^(1−a) > 0` and (since `a + e^(1−a) ≥ 2`)
`log(a + e^(1−a)) > 0`.
-/

/-- Closed sub-term whose partial eval is `0`. Used inside
`mkOneMinusAll`. -/
private def mkZeroLocal : EMLTerm := .eml .one (.eml (.eml .one .one) .one)

private lemma mkZeroLocal_eval? (env : Nat → ℝ) :
    mkZeroLocal.eval? env = some 0 := by
  unfold mkZeroLocal
  have h1 : (EMLTerm.one).eval? env = some 1 := by simp
  have h_e : (EMLTerm.eml .one .one).eval? env = some (Real.exp 1) := by
    have := eval?_eml_of_pos h1 h1 zero_lt_one
    simpa [Real.log_one] using this
  have h_expe : (EMLTerm.eml (.eml .one .one) .one).eval? env =
      some (Real.exp (Real.exp 1)) := by
    have := eval?_eml_of_pos h_e h1 zero_lt_one
    simpa [Real.log_one] using this
  have := eval?_eml_of_pos h1 h_expe (Real.exp_pos _)
  simpa [Real.log_exp] using this

/-- `mkOneMinusAll a` evaluates to `1 − a.eval` for all real `va`. -/
private def mkOneMinusAll (a : EMLTerm) : EMLTerm :=
  .eml mkZeroLocal (.eml a .one)

private lemma mkOneMinusAll_eval? (env : Nat → ℝ) (a : EMLTerm) {va : ℝ}
    (ha : a.eval? env = some va) :
    (mkOneMinusAll a).eval? env = some (1 - va) := by
  unfold mkOneMinusAll
  have h1 : (EMLTerm.one).eval? env = some 1 := by simp
  have h_zero : mkZeroLocal.eval? env = some 0 := mkZeroLocal_eval? env
  have h_expA : (EMLTerm.eml a .one).eval? env = some (Real.exp va) := by
    rw [eval?_eml_of_pos ha h1 zero_lt_one, Real.log_one, sub_zero]
  have := eval?_eml_of_pos h_zero h_expA (Real.exp_pos _)
  rw [Real.exp_zero, Real.log_exp] at this
  exact this

/-- `mkDivByPos a c` evaluates to `a.eval / c.eval` whenever
`c.eval > 0`. The dividend `a` may be *any* real. -/
def mkDivByPos (a c : EMLTerm) : EMLTerm :=
  let oma := mkOneMinusAll a
  let apk := EMLTerm.eml oma (.eml (mkNeg a) .one)
  let logApk := mkLog apk
  let logC := mkLog c
  let f := EMLTerm.eml (mkLog logApk) (.eml logC .one)
  let g := mkSub oma logC
  EMLTerm.eml f (.eml (.eml g .one) .one)

/-- `mkDivByPos` partial-eval spec: requires only `0 < vc`. -/
lemma mkDivByPos_eval? (env : Nat → ℝ) (a c : EMLTerm) {va vc : ℝ}
    (ha : a.eval? env = some va) (hc : c.eval? env = some vc)
    (hcp : 0 < vc) :
    (mkDivByPos a c).eval? env = some (va / vc) := by
  unfold mkDivByPos
  have h1 : (EMLTerm.one).eval? env = some 1 := by simp
  have h_oma : (mkOneMinusAll a).eval? env = some (1 - va) :=
    mkOneMinusAll_eval? env a ha
  have h_neg : (mkNeg a).eval? env = some (-va) := mkNeg_eval? env a ha
  have h_exp_neg : (EMLTerm.eml (mkNeg a) .one).eval? env =
      some (Real.exp (-va)) := by
    rw [eval?_eml_of_pos h_neg h1 zero_lt_one, Real.log_one, sub_zero]
  have h_apk_val_eq : Real.exp (1 - va) - Real.log (Real.exp (-va)) =
      va + Real.exp (1 - va) := by
    rw [Real.log_exp]; ring
  have h_apk : (EMLTerm.eml (mkOneMinusAll a) (.eml (mkNeg a) .one)).eval? env =
      some (va + Real.exp (1 - va)) := by
    have := eval?_eml_of_pos h_oma h_exp_neg (Real.exp_pos _)
    rw [h_apk_val_eq] at this
    exact this
  have h_apk_pos : 0 < va + Real.exp (1 - va) := add_exp_one_sub_pos' va
  have h_logApk : (mkLog (.eml (mkOneMinusAll a) (.eml (mkNeg a) .one))).eval? env =
      some (Real.log (va + Real.exp (1 - va))) :=
    mkLog_eval? env _ h_apk h_apk_pos
  have h_logApk_pos : 0 < Real.log (va + Real.exp (1 - va)) :=
    log_add_exp_one_sub_pos' va
  have h_logC : (mkLog c).eval? env = some (Real.log vc) :=
    mkLog_eval? env c hc hcp
  have h_log_logApk :
      (mkLog (mkLog (.eml (mkOneMinusAll a) (.eml (mkNeg a) .one)))).eval? env =
      some (Real.log (Real.log (va + Real.exp (1 - va)))) :=
    mkLog_eval? env _ h_logApk h_logApk_pos
  have h_eml_logC_one : (EMLTerm.eml (mkLog c) .one).eval? env = some vc := by
    rw [eval?_eml_of_pos h_logC h1 zero_lt_one, Real.log_one, sub_zero,
        Real.exp_log hcp]
  have h_f :
      (EMLTerm.eml (mkLog (mkLog (.eml (mkOneMinusAll a) (.eml (mkNeg a) .one))))
        (.eml (mkLog c) .one)).eval? env =
      some (Real.log (va + Real.exp (1 - va)) - Real.log vc) := by
    rw [eval?_eml_of_pos h_log_logApk h_eml_logC_one hcp,
        Real.exp_log h_logApk_pos]
  have h_g : (mkSub (mkOneMinusAll a) (mkLog c)).eval? env =
      some ((1 - va) - Real.log vc) :=
    mkSub_eval? env _ _ h_oma h_logC
  have h_exp_g : (EMLTerm.eml (mkSub (mkOneMinusAll a) (mkLog c)) .one).eval? env =
      some (Real.exp ((1 - va) - Real.log vc)) := by
    rw [eval?_eml_of_pos h_g h1 zero_lt_one, Real.log_one, sub_zero]
  have h_exp_exp_g :
      (EMLTerm.eml (.eml (mkSub (mkOneMinusAll a) (mkLog c)) .one) .one).eval? env =
      some (Real.exp (Real.exp ((1 - va) - Real.log vc))) := by
    rw [eval?_eml_of_pos h_exp_g h1 zero_lt_one, Real.log_one, sub_zero]
  have h_pos_exp_exp_g : 0 < Real.exp (Real.exp ((1 - va) - Real.log vc)) :=
    Real.exp_pos _
  have hfinal := eval?_eml_of_pos h_f h_exp_exp_g h_pos_exp_exp_g
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

/-! ## `mkSqAll a` — `a²`, defined for all real `va`

Algebraic identity used:
  `(A − E)² = A² + E² − 2·A·E`.

With `A := exp(va) − va` (always positive) and `E := exp(va)`
(always positive), `A − E = −va`, so `(A − E)² = va²`.

Concretely:
  `va² = mkSqPos(A) + mkSqPos(E) − 2 · mkMulPos(A, E)`
       = `mkSub (mkAdd (mkSqPos A) (mkSqPos E))
                (mkAdd (mkMulPos A E) (mkMulPos A E))`.

Each `mkSqPos` / `mkMulPos` argument is strictly positive, so the
positives-only specs apply. The outer `mkAdd`/`mkSub` are
unconditional (chunk-036 trick).
-/

/-- `mkSqAll a` evaluates to `a.eval ^ 2` for every real `va`. -/
def mkSqAll (a : EMLTerm) : EMLTerm :=
  let A : EMLTerm := mkSub (mkExp a) a   -- value: exp va − va, always > 0
  let E : EMLTerm := mkExp a              -- value: exp va, always > 0
  mkSub
    (mkAdd (mkSqPos A) (mkSqPos E))
    (mkAdd (mkMulPos A E) (mkMulPos A E))

/-- `mkSqAll` partial-eval spec: works for all real `va`. -/
lemma mkSqAll_eval? (env : Nat → ℝ) (a : EMLTerm) {va : ℝ}
    (ha : a.eval? env = some va) :
    (mkSqAll a).eval? env = some (va ^ 2) := by
  unfold mkSqAll
  -- E = exp va, positive.
  have h_E : (mkExp a).eval? env = some (Real.exp va) := mkExp_eval? env a ha
  have h_E_pos : 0 < Real.exp va := Real.exp_pos _
  -- A = exp va − va, positive (by exp_sub_self_pos).
  have h_A : (mkSub (mkExp a) a).eval? env = some (Real.exp va - va) :=
    mkSub_eval? env (mkExp a) a h_E ha
  have h_A_pos : 0 < Real.exp va - va := exp_sub_self_pos' va
  -- Squares of A and E.
  have h_sqA : (mkSqPos (mkSub (mkExp a) a)).eval? env =
      some ((Real.exp va - va) ^ 2) := mkSqPos_eval? env _ h_A h_A_pos
  have h_sqE : (mkSqPos (mkExp a)).eval? env = some ((Real.exp va) ^ 2) :=
    mkSqPos_eval? env _ h_E h_E_pos
  -- Sum of squares.
  have h_sumSq :
      (mkAdd (mkSqPos (mkSub (mkExp a) a)) (mkSqPos (mkExp a))).eval? env =
      some ((Real.exp va - va) ^ 2 + (Real.exp va) ^ 2) :=
    mkAdd_eval? env _ _ h_sqA h_sqE
  -- A · E.
  have h_AE : (mkMulPos (mkSub (mkExp a) a) (mkExp a)).eval? env =
      some ((Real.exp va - va) * Real.exp va) :=
    mkMulPos_eval? env _ _ h_A h_E h_A_pos h_E_pos
  -- 2 · (A · E) = (A · E) + (A · E).
  have h_2AE :
      (mkAdd (mkMulPos (mkSub (mkExp a) a) (mkExp a))
             (mkMulPos (mkSub (mkExp a) a) (mkExp a))).eval? env =
      some ((Real.exp va - va) * Real.exp va +
            (Real.exp va - va) * Real.exp va) :=
    mkAdd_eval? env _ _ h_AE h_AE
  -- Final: sumSq − 2AE = (exp va − va)² + (exp va)² − 2·(exp va − va)·exp va
  --                   = ((exp va − va) − exp va)² = (−va)² = va².
  have h_sub :=
    mkSub_eval? env _ _ h_sumSq h_2AE
  -- Rewrite the resulting RHS to va².
  have hrew :
      ((Real.exp va - va) ^ 2 + (Real.exp va) ^ 2)
        - ((Real.exp va - va) * Real.exp va +
           (Real.exp va - va) * Real.exp va) = va ^ 2 := by
    ring
  rw [hrew] at h_sub
  exact h_sub

/-! ## `mkAbsSqAll` — `|a|²` (= `a²`)

A trivial alias to highlight that `|va|² = va²` for all real `va`.
-/

/-- `mkAbsSqAll a` evaluates to `(|a.eval|)^2 = a.eval^2`. -/
def mkAbsSqAll (a : EMLTerm) : EMLTerm := mkSqAll a

/-- `mkAbsSqAll` partial-eval spec: works for all real `va`. -/
lemma mkAbsSqAll_eval? (env : Nat → ℝ) (a : EMLTerm) {va : ℝ}
    (ha : a.eval? env = some va) :
    (mkAbsSqAll a).eval? env = some (|va| ^ 2) := by
  unfold mkAbsSqAll
  have h := mkSqAll_eval? env a ha
  rw [h]
  congr 1
  rw [sq_abs]

/-! ## `mkInvNonzero a` — `1/a` for `a ≠ 0`

`1/va = va / va²`. The numerator is any real; the denominator is
positive (since `va ≠ 0` ⟹ `va² > 0`). Use `mkDivByPos`.
-/

/-- `mkInvNonzero a` evaluates to `1 / a.eval` whenever
`a.eval ≠ 0`. -/
def mkInvNonzero (a : EMLTerm) : EMLTerm := mkDivByPos a (mkSqAll a)

/-- `mkInvNonzero` partial-eval spec: requires only `va ≠ 0`. -/
lemma mkInvNonzero_eval? (env : Nat → ℝ) (a : EMLTerm) {va : ℝ}
    (ha : a.eval? env = some va) (hne : va ≠ 0) :
    (mkInvNonzero a).eval? env = some (1 / va) := by
  unfold mkInvNonzero
  have h_sq : (mkSqAll a).eval? env = some (va ^ 2) := mkSqAll_eval? env a ha
  have h_sq_pos : 0 < va ^ 2 := by positivity
  have h := mkDivByPos_eval? env a (mkSqAll a) ha h_sq h_sq_pos
  rw [h]
  congr 1
  -- va / va² = 1/va.
  field_simp

/-! ## `mkMulAll a b` — `a · b`, all reals

Polarisation identity:
  `4·va·vb = (va + vb)² − (va − vb)²`,
hence `va·vb = ((va+vb)² − (va−vb)²) / 4`.

Both squared sub-terms use `mkSqAll` (works for all reals). The
constant `4` is built closed as `mkAdd mkTwo mkTwo`. The final
division uses `mkDivByPos` since `4 > 0` (and the dividend has any
sign).
-/

/-- Closed EML term whose value is `4`. -/
private def mkFourClosed : EMLTerm := mkAdd mkTwo mkTwo

private lemma mkFourClosed_eval? (env : Nat → ℝ) :
    mkFourClosed.eval? env = some 4 := by
  unfold mkFourClosed
  have h_two : mkTwo.eval? env = some 2 := mkTwo_eval? env
  have h := mkAdd_eval? env mkTwo mkTwo h_two h_two
  rw [h]
  norm_num

/-- `mkMulAll a b` evaluates to `a.eval * b.eval` for all real `va`,
`vb`. -/
def mkMulAll (a b : EMLTerm) : EMLTerm :=
  let sumSq : EMLTerm := mkSqAll (mkAdd a b)
  let diffSq : EMLTerm := mkSqAll (mkSub a b)
  mkDivByPos (mkSub sumSq diffSq) mkFourClosed

/-- `mkMulAll` partial-eval spec: works for all real `va`, `vb`. -/
lemma mkMulAll_eval? (env : Nat → ℝ) (a b : EMLTerm) {va vb : ℝ}
    (ha : a.eval? env = some va) (hb : b.eval? env = some vb) :
    (mkMulAll a b).eval? env = some (va * vb) := by
  unfold mkMulAll
  have h_sum : (mkAdd a b).eval? env = some (va + vb) :=
    mkAdd_eval? env a b ha hb
  have h_diff : (mkSub a b).eval? env = some (va - vb) :=
    mkSub_eval? env a b ha hb
  have h_sumSq : (mkSqAll (mkAdd a b)).eval? env = some ((va + vb) ^ 2) :=
    mkSqAll_eval? env _ h_sum
  have h_diffSq : (mkSqAll (mkSub a b)).eval? env = some ((va - vb) ^ 2) :=
    mkSqAll_eval? env _ h_diff
  have h_diff_squares :
      (mkSub (mkSqAll (mkAdd a b)) (mkSqAll (mkSub a b))).eval? env =
      some ((va + vb) ^ 2 - (va - vb) ^ 2) :=
    mkSub_eval? env _ _ h_sumSq h_diffSq
  have h_four : mkFourClosed.eval? env = some 4 := mkFourClosed_eval? env
  have h_four_pos : (0 : ℝ) < 4 := by norm_num
  have h := mkDivByPos_eval? env _ mkFourClosed h_diff_squares h_four h_four_pos
  rw [h]
  congr 1
  -- ((va+vb)² − (va−vb)²) / 4 = va·vb.
  ring

/-! ## `mkDivNonzeroDenom a b` — `a / b` for `b ≠ 0`

`va / vb = (va · vb) / vb²`. Since `vb ≠ 0`, `vb² > 0` and the
divide-by-positive helper applies. The dividend `va · vb` may be any
real (handled by `mkMulAll`).
-/

/-- `mkDivNonzeroDenom a b` evaluates to `a.eval / b.eval` whenever
`b.eval ≠ 0`. -/
def mkDivNonzeroDenom (a b : EMLTerm) : EMLTerm :=
  mkDivByPos (mkMulAll a b) (mkSqAll b)

/-- `mkDivNonzeroDenom` partial-eval spec: requires only `vb ≠ 0`. -/
lemma mkDivNonzeroDenom_eval? (env : Nat → ℝ) (a b : EMLTerm) {va vb : ℝ}
    (ha : a.eval? env = some va) (hb : b.eval? env = some vb)
    (hne : vb ≠ 0) :
    (mkDivNonzeroDenom a b).eval? env = some (va / vb) := by
  unfold mkDivNonzeroDenom
  have h_prod : (mkMulAll a b).eval? env = some (va * vb) :=
    mkMulAll_eval? env a b ha hb
  have h_sq : (mkSqAll b).eval? env = some (vb ^ 2) := mkSqAll_eval? env b hb
  have h_sq_pos : 0 < vb ^ 2 := by positivity
  have h := mkDivByPos_eval? env _ _ h_prod h_sq h_sq_pos
  rw [h]
  congr 1
  -- (va · vb) / vb² = va / vb.
  have hvb_ne : vb ≠ 0 := hne
  field_simp

/-! ## `mkHalveAll a` — `a / 2`, all reals

Direct application of `mkDivByPos` with the closed witness for
`2`. The dividend has any sign.
-/

/-- `mkHalveAll a` evaluates to `a.eval / 2` for all real `va`. -/
def mkHalveAll (a : EMLTerm) : EMLTerm := mkDivByPos a mkTwo

/-- `mkHalveAll` partial-eval spec: works for all real `va`. -/
lemma mkHalveAll_eval? (env : Nat → ℝ) (a : EMLTerm) {va : ℝ}
    (ha : a.eval? env = some va) :
    (mkHalveAll a).eval? env = some (va / 2) := by
  unfold mkHalveAll
  have h_two : mkTwo.eval? env = some 2 := mkTwo_eval? env
  exact mkDivByPos_eval? env a mkTwo ha h_two (by norm_num)

/-! ## `mkAvgAll a b` — `(a + b) / 2`, all reals -/

/-- `mkAvgAll a b` evaluates to `(a.eval + b.eval) / 2` for all real
`va`, `vb`. -/
def mkAvgAll (a b : EMLTerm) : EMLTerm := mkHalveAll (mkAdd a b)

/-- `mkAvgAll` partial-eval spec: works for all real `va`, `vb`. -/
lemma mkAvgAll_eval? (env : Nat → ℝ) (a b : EMLTerm) {va vb : ℝ}
    (ha : a.eval? env = some va) (hb : b.eval? env = some vb) :
    (mkAvgAll a b).eval? env = some ((va + vb) / 2) := by
  unfold mkAvgAll
  have h_sum : (mkAdd a b).eval? env = some (va + vb) :=
    mkAdd_eval? env a b ha hb
  exact mkHalveAll_eval? env _ h_sum

/-! ## `mkHypotAll a b` — `√(a² + b²)`, defined for `(va, vb) ≠ (0, 0)`

Since `mkSqAll` is unconditional, `va² + vb²` is computable for all
real inputs. `mkSqrtPos` requires positivity of its argument; this
holds iff `(va, vb) ≠ (0, 0)`. The combined builder thus widens
`mkHypotPos`'s domain from `(va > 0 ∧ vb > 0)` to
`(va, vb) ≠ (0, 0)`.
-/

/-- `mkHypotAll a b` evaluates to `√(a.eval² + b.eval²)` whenever
`(va, vb) ≠ (0, 0)`. -/
def mkHypotAll (a b : EMLTerm) : EMLTerm :=
  mkSqrtPos (mkAdd (mkSqAll a) (mkSqAll b))

/-- `mkHypotAll` partial-eval spec. Domain: `(va, vb) ≠ (0, 0)`. -/
lemma mkHypotAll_eval? (env : Nat → ℝ) (a b : EMLTerm) {va vb : ℝ}
    (ha : a.eval? env = some va) (hb : b.eval? env = some vb)
    (hne : ¬(va = 0 ∧ vb = 0)) :
    (mkHypotAll a b).eval? env = some (Real.sqrt (va ^ 2 + vb ^ 2)) := by
  unfold mkHypotAll
  have h_sqa : (mkSqAll a).eval? env = some (va ^ 2) := mkSqAll_eval? env a ha
  have h_sqb : (mkSqAll b).eval? env = some (vb ^ 2) := mkSqAll_eval? env b hb
  have h_sum : (mkAdd (mkSqAll a) (mkSqAll b)).eval? env =
      some (va ^ 2 + vb ^ 2) := mkAdd_eval? env _ _ h_sqa h_sqb
  have h_sum_pos : 0 < va ^ 2 + vb ^ 2 := by
    rcases (not_and_or.mp hne) with hva | hvb
    · have hva_sq : 0 < va ^ 2 := by positivity
      nlinarith [sq_nonneg vb]
    · have hvb_sq : 0 < vb ^ 2 := by positivity
      nlinarith [sq_nonneg va]
  exact mkSqrtPos_eval? env _ h_sum h_sum_pos

/-! ## `mkSubAll` — re-expose the unconditional `mkSub`

Already provided unconditionally in `Builders/Arithmetic.lean`; we
re-expose under an `*All` name for naming consistency with the rest
of this file. -/

/-- Alias of `mkSub`; subtraction is already unconditional. -/
def mkSubAll (a b : EMLTerm) : EMLTerm := mkSub a b

lemma mkSubAll_eval? (env : Nat → ℝ) (a b : EMLTerm) {va vb : ℝ}
    (ha : a.eval? env = some va) (hb : b.eval? env = some vb) :
    (mkSubAll a b).eval? env = some (va - vb) := by
  unfold mkSubAll
  exact mkSub_eval? env a b ha hb

/-! ## `mkPowAll a b` — `a^b` for `0 < va`, any `vb`

For `0 < va`, `Real.rpow va vb = Real.exp (vb · Real.log va)`. Since
`vb · Real.log va` is a real number with arbitrary sign, we use
`mkMulAll` (unconditional multiplication) to compute it, then `mkExp`
(unconditional). This widens `mkPowPos`'s domain by removing the
`0 < vb` constraint. -/

/-- `mkPowAll a b` evaluates to `Real.rpow a.eval b.eval` whenever
`0 < a.eval`. The exponent `b.eval` may have any sign. -/
def mkPowAll (a b : EMLTerm) : EMLTerm :=
  mkExp (mkMulAll b (mkLog a))

/-- `mkPowAll` partial-eval spec: requires only `0 < va`. -/
lemma mkPowAll_eval? (env : Nat → ℝ) (a b : EMLTerm) {va vb : ℝ}
    (ha : a.eval? env = some va) (hb : b.eval? env = some vb)
    (hap : 0 < va) :
    (mkPowAll a b).eval? env = some (Real.rpow va vb) := by
  unfold mkPowAll
  have h_log : (mkLog a).eval? env = some (Real.log va) :=
    mkLog_eval? env a ha hap
  have h_prod : (mkMulAll b (mkLog a)).eval? env =
      some (vb * Real.log va) :=
    mkMulAll_eval? env b (mkLog a) hb h_log
  have h_exp : (mkExp (mkMulAll b (mkLog a))).eval? env =
      some (Real.exp (vb * Real.log va)) :=
    mkExp_eval? env _ h_prod
  rw [h_exp]
  congr 1
  rw [show Real.rpow va vb = va ^ vb from rfl, Real.rpow_def_of_pos hap,
      mul_comm vb (Real.log va)]

/-! ## `mkLogbAll a b` — `log_a b` for `0 < va, va ≠ 1, 0 < vb`

`log_va vb = log vb / log va`. We need `log va ≠ 0`, which is
equivalent to `va ≠ 1` (given `0 < va`). The dividend `log vb` may
have any sign, and the divisor `log va` may also be negative
(when `0 < va < 1`), so we use `mkDivNonzeroDenom` (denominator
non-zero only). -/

/-- `mkLogbAll a b` evaluates to `Real.log b.eval / Real.log a.eval`
whenever `0 < a.eval`, `a.eval ≠ 1`, and `0 < b.eval`. -/
def mkLogbAll (a b : EMLTerm) : EMLTerm :=
  mkDivNonzeroDenom (mkLog b) (mkLog a)

/-- `mkLogbAll` partial-eval spec. -/
lemma mkLogbAll_eval? (env : Nat → ℝ) (a b : EMLTerm) {va vb : ℝ}
    (ha : a.eval? env = some va) (hb : b.eval? env = some vb)
    (hap : 0 < va) (hane : va ≠ 1) (hbp : 0 < vb) :
    (mkLogbAll a b).eval? env = some (Real.log vb / Real.log va) := by
  unfold mkLogbAll
  have h_loga : (mkLog a).eval? env = some (Real.log va) :=
    mkLog_eval? env a ha hap
  have h_logb : (mkLog b).eval? env = some (Real.log vb) :=
    mkLog_eval? env b hb hbp
  have h_loga_ne : Real.log va ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hap hane
  exact mkDivNonzeroDenom_eval? env (mkLog b) (mkLog a) h_logb h_loga h_loga_ne

end EMLTerm

end EML
