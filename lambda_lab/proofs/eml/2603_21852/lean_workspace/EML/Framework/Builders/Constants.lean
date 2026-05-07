import EML.Framework.EMLPartial
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# EML term builders for closed constants

Closed `EMLTerm` witnesses (no `var`) for the five constants `0`, `-1`,
`2`, `1/2`, and `e` that the EL → EML compiler dispatches to when it
encounters a constant literal in EL. Each builder comes with a
partial-evaluation spec lemma proving its `eval?` value.

The closed terms are copied verbatim from the chunk solutions
`030_emlterm_for_zero`, `031_emlterm_for_neg_one`,
`032_emlterm_for_two`, `033_emlterm_for_half`,
`022_emlterm_e_witness` (those chunks define their own local
`EMLTerm` without `var`; the witnesses use only `.one` and `.eml` so
they port directly to the framework's `EMLTerm`).

The proofs adapt the chunk reasoning to the partial-eval semantics by
chaining `eval?_eml_of_pos` and discharging the `0 < _` obligation
that each `eml(a, b)` step incurs on its second argument.
-/

namespace EML

namespace EMLTerm

/-! ## Constant `0`

Witness: `eml(1, eml(eml(1, 1), 1))`
  = exp(1) - log(exp(exp(1) - log(1)))
  = exp(1) - log(exp(exp(1)))
  = exp(1) - exp(1)
  = 0
-/

/-- Closed EML term whose partial evaluation is `0`. -/
def mkZero : EMLTerm := .eml .one (.eml (.eml .one .one) .one)

/-- `mkZero` partial-eval spec. -/
lemma mkZero_eval? (env : Nat → ℝ) : mkZero.eval? env = some 0 := by
  unfold mkZero
  -- Step 1: `eml(1, 1)` → `exp 1 - log 1 = exp 1`.
  have h1 : EMLTerm.one.eval? env = some 1 := eval?_one env
  have h_e : (EMLTerm.eml .one .one).eval? env = some (Real.exp 1) := by
    have := eval?_eml_of_pos h1 h1 zero_lt_one
    simpa [Real.log_one] using this
  -- Step 2: `eml(eml(1,1), 1)` → `exp(exp 1) - log 1 = exp(exp 1)`.
  have h_exp_e : (EMLTerm.eml (.eml .one .one) .one).eval? env =
      some (Real.exp (Real.exp 1)) := by
    have := eval?_eml_of_pos h_e h1 zero_lt_one
    simpa [Real.log_one] using this
  -- Step 3 (outer): `eml(1, exp(exp 1))` → `exp 1 - log(exp(exp 1)) = exp 1 - exp 1 = 0`.
  have h_pos : 0 < Real.exp (Real.exp 1) := Real.exp_pos _
  have := eval?_eml_of_pos h1 h_exp_e h_pos
  simpa [Real.log_exp, sub_self] using this

/-! ## Constant `e`

Witness: `eml(1, 1)` = exp(1) - log(1) = e - 0 = e.
-/

/-- Closed EML term whose partial evaluation is `Real.exp 1` (i.e. `e`). -/
def mkE : EMLTerm := .eml .one .one

/-- `mkE` partial-eval spec. -/
lemma mkE_eval? (env : Nat → ℝ) : mkE.eval? env = some (Real.exp 1) := by
  unfold mkE
  have h1 : EMLTerm.one.eval? env = some 1 := eval?_one env
  have := eval?_eml_of_pos h1 h1 zero_lt_one
  simpa [Real.log_one] using this

/-! ## Constant `-1`

Witness from chunk 031:
  `eml( eml(1, eml(eml(1, eml(1, eml(1,1))) , 1)), eml(eml(1,1), 1) )`

Reading inside-out:
  a₁ := eml(1, 1)            → e
  a₂ := eml(1, a₁)           → e - log e = e - 1
  a₃ := eml(1, a₂)           → e - log(e - 1)
  a₄ := eml(a₃, 1)           → exp(e - log(e - 1)) - 0 = exp(e - log(e - 1))
                               = exp e / (e - 1)
  a₅ := eml(1, a₄)           → e - log(a₄) = e - (e - log(e - 1)) = log(e - 1)
  rhs := eml(a₁, 1)          → exp e - 0 = exp e
  outer := eml(a₅, rhs)      → exp(log(e-1)) - log(exp e)
                               = (e - 1) - e = -1.
-/

/-- `e - 1 > 0`. -/
private lemma e_sub_one_pos : (0 : ℝ) < Real.exp 1 - 1 := by
  linarith [Real.add_one_le_exp (1 : ℝ)]

/-- Closed EML term whose partial evaluation is `-1`. -/
def mkNegOne : EMLTerm :=
  .eml
    (.eml .one (.eml (.eml .one (.eml .one (.eml .one .one))) .one))
    (.eml (.eml .one .one) .one)

/-- `mkNegOne` partial-eval spec. -/
lemma mkNegOne_eval? (env : Nat → ℝ) : mkNegOne.eval? env = some (-1) := by
  unfold mkNegOne
  have h1 : EMLTerm.one.eval? env = some 1 := eval?_one env
  -- a₁ = eml(1, 1) → e
  have h_a1 : (EMLTerm.eml .one .one).eval? env = some (Real.exp 1) := by
    have := eval?_eml_of_pos h1 h1 zero_lt_one
    simpa [Real.log_one] using this
  -- a₂ = eml(1, a₁) → e - 1, requires a₁ > 0 i.e. exp 1 > 0
  have h_a2 : (EMLTerm.eml .one (.eml .one .one)).eval? env =
      some (Real.exp 1 - 1) := by
    have := eval?_eml_of_pos h1 h_a1 (Real.exp_pos 1)
    simpa [Real.log_exp] using this
  -- a₃ = eml(1, a₂) → e - log(e-1), requires a₂ > 0 i.e. e - 1 > 0
  have h_a3 :
      (EMLTerm.eml .one (.eml .one (.eml .one .one))).eval? env =
        some (Real.exp 1 - Real.log (Real.exp 1 - 1)) := by
    exact eval?_eml_of_pos h1 h_a2 e_sub_one_pos
  -- a₄ = eml(a₃, 1) → exp(e - log(e-1))
  have h_a4 :
      (EMLTerm.eml (.eml .one (.eml .one (.eml .one .one))) .one).eval? env =
        some (Real.exp (Real.exp 1 - Real.log (Real.exp 1 - 1))) := by
    have := eval?_eml_of_pos h_a3 h1 zero_lt_one
    simpa [Real.log_one] using this
  -- a₅ = eml(1, a₄) → e - (e - log(e-1)) = log(e-1)
  have h_pos_a4 :
      0 < Real.exp (Real.exp 1 - Real.log (Real.exp 1 - 1)) := Real.exp_pos _
  have h_a5 :
      (EMLTerm.eml .one
        (.eml (.eml .one (.eml .one (.eml .one .one))) .one)).eval? env =
        some (Real.log (Real.exp 1 - 1)) := by
    have := eval?_eml_of_pos h1 h_a4 h_pos_a4
    -- Resulting RHS is `exp 1 - log(exp(exp 1 - log(e-1))) = exp 1 - (exp 1 - log(e-1))`
    -- which equals `log(e-1)`.
    have hrewrite : Real.exp 1 -
        Real.log (Real.exp (Real.exp 1 - Real.log (Real.exp 1 - 1))) =
        Real.log (Real.exp 1 - 1) := by
      rw [Real.log_exp]; ring
    rw [hrewrite] at this
    exact this
  -- rhs = eml(a₁, 1) → exp(exp 1) - 0 = exp(exp 1)
  have h_rhs :
      (EMLTerm.eml (.eml .one .one) .one).eval? env =
        some (Real.exp (Real.exp 1)) := by
    have := eval?_eml_of_pos h_a1 h1 zero_lt_one
    simpa [Real.log_one] using this
  -- outer: eml(a₅, rhs) → exp(log(e-1)) - log(exp(exp 1)) = (e-1) - exp 1 = -1
  have h_pos_rhs : 0 < Real.exp (Real.exp 1) := Real.exp_pos _
  have hfinal := eval?_eml_of_pos h_a5 h_rhs h_pos_rhs
  -- Simplify the RHS: exp(log(e-1)) - log(exp(exp 1)) = (e-1) - exp 1 = -1
  have hrewrite :
      Real.exp (Real.log (Real.exp 1 - 1)) -
        Real.log (Real.exp (Real.exp 1)) = -1 := by
    rw [Real.exp_log e_sub_one_pos, Real.log_exp]
    ring
  rw [hrewrite] at hfinal
  exact hfinal

/-! ## Constant `2`

Witness from chunk 032 (built bottom-up):
  t₂ := eml(1, 1)              → e
  t₃ := eml(1, t₂)             → e - 1
  t₄ := eml(1, t₃)             → e - log(e-1)
  t₅ := eml(t₄, 1)             → exp(e - log(e-1))
  t₆ := eml(1, t₅)             → log(e-1)
  t₇ := eml(t₆, t₂)            → exp(log(e-1)) - log(exp 1) = (e-1) - 1 = e - 2
  t₈ := eml(t₇, 1)             → exp(e - 2)
  witness := eml(1, t₈)        → e - log(exp(e-2)) = e - (e-2) = 2.
-/

/-- Closed EML term whose partial evaluation is `2`. -/
def mkTwo : EMLTerm :=
  let t₂ : EMLTerm := .eml .one .one
  let t₃ : EMLTerm := .eml .one t₂
  let t₄ : EMLTerm := .eml .one t₃
  let t₅ : EMLTerm := .eml t₄ .one
  let t₆ : EMLTerm := .eml .one t₅
  let t₇ : EMLTerm := .eml t₆ t₂
  let t₈ : EMLTerm := .eml t₇ .one
  .eml .one t₈

/-- `mkTwo` partial-eval spec. -/
lemma mkTwo_eval? (env : Nat → ℝ) : mkTwo.eval? env = some 2 := by
  unfold mkTwo
  simp only []
  have h1 : EMLTerm.one.eval? env = some 1 := eval?_one env
  -- t₂ = eml(1, 1) → e
  have h_t2 : (EMLTerm.eml .one .one).eval? env = some (Real.exp 1) := by
    have := eval?_eml_of_pos h1 h1 zero_lt_one
    simpa [Real.log_one] using this
  -- t₃ = eml(1, t₂) → e - 1, requires t₂ > 0 i.e. exp 1 > 0
  have h_t3 : (EMLTerm.eml .one (.eml .one .one)).eval? env =
      some (Real.exp 1 - 1) := by
    have := eval?_eml_of_pos h1 h_t2 (Real.exp_pos 1)
    simpa [Real.log_exp] using this
  -- t₄ = eml(1, t₃) → e - log(e-1), requires t₃ > 0 i.e. e - 1 > 0
  have h_t4 :
      (EMLTerm.eml .one (.eml .one (.eml .one .one))).eval? env =
        some (Real.exp 1 - Real.log (Real.exp 1 - 1)) :=
    eval?_eml_of_pos h1 h_t3 e_sub_one_pos
  -- t₅ = eml(t₄, 1) → exp(e - log(e-1))
  have h_t5 :
      (EMLTerm.eml (.eml .one (.eml .one (.eml .one .one))) .one).eval? env =
        some (Real.exp (Real.exp 1 - Real.log (Real.exp 1 - 1))) := by
    have := eval?_eml_of_pos h_t4 h1 zero_lt_one
    simpa [Real.log_one] using this
  -- t₆ = eml(1, t₅) → log(e-1)
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
  -- t₇ = eml(t₆, t₂) → e - 2
  -- needs t₂ > 0 i.e. exp 1 > 0
  have h_t7 :
      (EMLTerm.eml
          (.eml .one (.eml (.eml .one (.eml .one (.eml .one .one))) .one))
          (.eml .one .one)).eval? env =
        some (Real.exp 1 - 2) := by
    have := eval?_eml_of_pos h_t6 h_t2 (Real.exp_pos 1)
    -- Result: exp(log(e-1)) - log(exp 1) = (e-1) - 1 = e - 2
    have hrewrite :
        Real.exp (Real.log (Real.exp 1 - 1)) - Real.log (Real.exp 1) =
        Real.exp 1 - 2 := by
      rw [Real.exp_log e_sub_one_pos, Real.log_exp]
      ring
    rw [hrewrite] at this
    exact this
  -- t₈ = eml(t₇, 1) → exp(e - 2)
  have h_t8 :
      (EMLTerm.eml
          (.eml
            (.eml .one (.eml (.eml .one (.eml .one (.eml .one .one))) .one))
            (.eml .one .one))
          .one).eval? env =
        some (Real.exp (Real.exp 1 - 2)) := by
    have := eval?_eml_of_pos h_t7 h1 zero_lt_one
    simpa [Real.log_one] using this
  -- witness = eml(1, t₈) → e - log(exp(e-2)) = e - (e-2) = 2
  have h_pos_t8 : 0 < Real.exp (Real.exp 1 - 2) := Real.exp_pos _
  have hfinal := eval?_eml_of_pos h1 h_t8 h_pos_t8
  have hrewrite : Real.exp 1 - Real.log (Real.exp (Real.exp 1 - 2)) = 2 := by
    rw [Real.log_exp]; ring
  rw [hrewrite] at hfinal
  exact hfinal

/-! ## Constant `1/2`

Witness from chunk 033, built bottom-up using `Z` (= 0) and `Lg` (= log)
sub-terms. We inline the construction.

Sub-lemmas: `log 2 ≤ 1`, hence `e - log 2 > 0`.
-/

/-- `Real.log 2 ≤ 1`. -/
private lemma log_two_le_one : Real.log 2 ≤ 1 := by
  rw [show (1 : ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
  exact Real.log_le_log (by norm_num)
    (by linarith [Real.add_one_le_exp (1 : ℝ)])

/-- `0 < e - log 2`. -/
private lemma e_sub_log_two_pos : (0 : ℝ) < Real.exp 1 - Real.log 2 := by
  linarith [e_sub_one_pos, log_two_le_one]

/-- Closed EML term whose partial evaluation is `1/2`. -/
def mkHalf : EMLTerm :=
  -- Z := mkZero (as a sub-term).
  let Z : EMLTerm := .eml .one (.eml (.eml .one .one) .one)
  -- Lg t := eml(Z, eml(eml(Z, t), 1))  (eval = log t when t > 0).
  let Lg : EMLTerm → EMLTerm := fun t => .eml Z (.eml (.eml Z t) .one)
  -- Building blocks.
  let e1 : EMLTerm := .eml .one (.eml .one .one)            -- e - 1
  let log_e1 : EMLTerm := Lg e1                              -- log(e-1)
  let e2 : EMLTerm := .eml log_e1 (.eml .one .one)           -- e - 2
  let exp_e2 : EMLTerm := .eml e2 .one                       -- exp(e-2)
  let two_ : EMLTerm := .eml .one exp_e2                     -- 2
  let eml2 : EMLTerm := .eml .one two_                       -- e - log 2
  let log_eml2 : EMLTerm := Lg eml2                          -- log(e - log 2)
  let neg_log2 : EMLTerm := .eml log_eml2 (.eml (.eml .one .one) .one)
                                                              -- -log 2
  .eml neg_log2 .one                                          -- exp(-log 2) = 1/2

/-- `mkHalf` partial-eval spec. -/
lemma mkHalf_eval? (env : Nat → ℝ) : mkHalf.eval? env = some (1 / 2) := by
  unfold mkHalf
  simp only []
  have h1 : EMLTerm.one.eval? env = some 1 := eval?_one env
  -- Z evaluates to 0.
  have h_Z : (EMLTerm.eml .one (.eml (.eml .one .one) .one)).eval? env =
      some 0 := mkZero_eval? env
  -- Step 1: e1 = eml(1, eml(1, 1)) → e - 1.
  have h_e_const : (EMLTerm.eml .one .one).eval? env = some (Real.exp 1) := by
    have := eval?_eml_of_pos h1 h1 zero_lt_one
    simpa [Real.log_one] using this
  have h_e1 : (EMLTerm.eml .one (.eml .one .one)).eval? env =
      some (Real.exp 1 - 1) := by
    have := eval?_eml_of_pos h1 h_e_const (Real.exp_pos 1)
    simpa [Real.log_exp] using this
  -- Step 2: log_e1 = Lg e1 → log(e - 1).
  -- Lg t = eml(Z, eml(eml(Z, t), 1)).
  -- First inner: eml(Z, e1) → exp 0 - log(e-1) = 1 - log(e-1)
  have h_eml_Z_e1 :
      (EMLTerm.eml (.eml .one (.eml (.eml .one .one) .one))
        (.eml .one (.eml .one .one))).eval? env =
        some (1 - Real.log (Real.exp 1 - 1)) := by
    have := eval?_eml_of_pos h_Z h_e1 e_sub_one_pos
    simpa [Real.exp_zero] using this
  -- Middle: eml(inner, 1) → exp(1 - log(e-1)) - log 1 = exp(1 - log(e-1))
  have h_mid_e1 :
      (EMLTerm.eml
          (.eml (.eml .one (.eml (.eml .one .one) .one))
            (.eml .one (.eml .one .one)))
          .one).eval? env =
        some (Real.exp (1 - Real.log (Real.exp 1 - 1))) := by
    have := eval?_eml_of_pos h_eml_Z_e1 h1 zero_lt_one
    simpa [Real.log_one] using this
  -- Outer: eml(Z, mid) → exp 0 - log(mid) = 1 - (1 - log(e-1)) = log(e-1).
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
    have hrewrite :
        Real.exp 0 - Real.log (Real.exp (1 - Real.log (Real.exp 1 - 1))) =
        Real.log (Real.exp 1 - 1) := by
      rw [Real.exp_zero, Real.log_exp]; ring
    rw [hrewrite] at this
    exact this
  -- Step 3: e2 = eml(log_e1, eml(1, 1)) → exp(log(e-1)) - log(exp 1) = (e-1)-1 = e-2.
  have h_e2 :
      (EMLTerm.eml
          (.eml (.eml .one (.eml (.eml .one .one) .one))
            (.eml
              (.eml (.eml .one (.eml (.eml .one .one) .one))
                (.eml .one (.eml .one .one)))
              .one))
          (.eml .one .one)).eval? env =
        some (Real.exp 1 - 2) := by
    have := eval?_eml_of_pos h_log_e1 h_e_const (Real.exp_pos 1)
    have hrewrite :
        Real.exp (Real.log (Real.exp 1 - 1)) - Real.log (Real.exp 1) =
        Real.exp 1 - 2 := by
      rw [Real.exp_log e_sub_one_pos, Real.log_exp]; ring
    rw [hrewrite] at this
    exact this
  -- Step 4: exp_e2 = eml(e2, 1) → exp(e - 2).
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
  -- Step 5: two_ = eml(1, exp_e2) → e - log(exp(e-2)) = 2.
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
    have hrewrite : Real.exp 1 - Real.log (Real.exp (Real.exp 1 - 2)) = 2 := by
      rw [Real.log_exp]; ring
    rw [hrewrite] at this
    exact this
  -- Step 6: eml2 = eml(1, two_) → e - log 2. Needs 0 < 2.
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
  -- Step 7: log_eml2 = Lg eml2 → log(e - log 2). Pos: e - log 2 > 0.
  -- Inner: eml(Z, eml2) → exp 0 - log(e - log 2) = 1 - log(e - log 2)
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
  -- Middle: eml(inner, 1) → exp(1 - log(e - log 2))
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
  -- Outer: eml(Z, mid) → 1 - (1 - log(e - log 2)) = log(e - log 2)
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
    have hrewrite :
        Real.exp 0 -
            Real.log (Real.exp (1 - Real.log (Real.exp 1 - Real.log 2))) =
          Real.log (Real.exp 1 - Real.log 2) := by
      rw [Real.exp_zero, Real.log_exp]; ring
    rw [hrewrite] at this
    exact this
  -- Step 8: neg_log2 = eml(log_eml2, eml(eml(1,1), 1)) → -log 2.
  -- Inner subterm eml(eml(1,1), 1) → exp(exp 1) - log 1 = exp(exp 1).
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
    -- Result: exp(log(e - log 2)) - log(exp(exp 1)) = (e - log 2) - exp 1 = -log 2
    have hrewrite :
        Real.exp (Real.log (Real.exp 1 - Real.log 2)) -
            Real.log (Real.exp (Real.exp 1)) =
          -Real.log 2 := by
      rw [Real.exp_log e_sub_log_two_pos, Real.log_exp]; ring
    rw [hrewrite] at this
    exact this
  -- Final: half_term = eml(neg_log2, 1) → exp(-log 2) - log 1 = 1/2.
  have hfinal := eval?_eml_of_pos h_neg_log2 h1 zero_lt_one
  have hrewrite : Real.exp (-Real.log 2) - Real.log 1 = 1 / 2 := by
    rw [Real.log_one, sub_zero, Real.exp_neg,
        Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [hrewrite] at hfinal
  exact hfinal

end EMLTerm

end EML
