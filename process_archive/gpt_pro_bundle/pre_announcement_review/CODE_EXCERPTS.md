# Code excerpts — the six new frontier modules

All file paths are relative to
`lambda_lab/proofs/eml/2603_21852/lean_workspace/`. Line numbers
correspond to the `66a93ac` commit on `main`.

---

## 1. `EML/Framework/TransplantDepths.lean` (SI §1.5 #5 — Pro #1)

### Affirmative side

```lean
-- The depth-4 identity, the base case
def id4 : EMLTerm := mkLog (mkExp (.var 0))

theorem id4_depth : id4.depth = 4 := rfl

theorem id4_eval (env : Nat → ℝ) :
    id4.eval? env = some (env 0) := by
  unfold id4
  have h_exp : (mkExp (.var 0)).eval? env = some (Real.exp (env 0)) :=
    mkExp_eval? env _ (by simp)
  have h_exp_pos : 0 < Real.exp (env 0) := Real.exp_pos _
  rw [mkLog_eval? env _ h_exp h_exp_pos, Real.log_exp]

-- The transplant combinator
def transplant4 (t : EMLTerm) : EMLTerm := id4.subst0 t

theorem transplant4_depth (t : EMLTerm) :
    (transplant4 t).depth = t.depth + 4 := by ...

theorem transplant4_eval {t : EMLTerm} {env : Nat → ℝ} {v : ℝ}
    (ht : t.eval? env = some v) :
    (transplant4 t).eval? env = some v := by ...

-- The k-fold iterate
def idMulFour : Nat → EMLTerm
  | 0     => .var 0
  | k + 1 => mkLog (mkExp (idMulFour k))

theorem idMulFour_depth (k : Nat) : (idMulFour k).depth = 4 * k

theorem idMulFour_eval (k : Nat) (env : Nat → ℝ) :
    (idMulFour k).eval? env = some (env 0)

-- The headline existential
theorem identity_terms_at_depth_multiples_of_four (k : Nat) :
    ∃ t : EMLTerm, t.depth = 4 * k ∧
      ∀ env : Nat → ℝ, t.eval? env = some (env 0) :=
  ⟨idMulFour k, idMulFour_depth k, idMulFour_eval k⟩
```

### Negative side

```lean
theorem no_identity_at_depth_one :
    ¬ ∃ t : EMLTerm, t.depth = 1 ∧
      ∀ env : Nat → ℝ, t.eval? env = some (env 0) := by ...

theorem no_identity_at_depth_two :
    ¬ ∃ t : EMLTerm, t.depth = 2 ∧
      ∀ env : Nat → ℝ, t.eval? env = some (env 0) := by ...
```

(Both proved by case-splitting on the depth-1 / depth-2 tree shape
and showing that the value on the all-ones environment is `exp 1`
or one of `{exp(1)-1, exp(exp 1), exp(exp 1)-1}` — all ≠ 1.)

### Conjecture statement (paper-open)

```lean
/-- **Conjecture (SI §1.5 #5, paper-open).** Identity terms exist
at depth `d` if and only if `d` is a multiple of 4. -/
def OnlyMultiplesOfFourHaveIdentities : Prop :=
  ∀ d : Nat,
    (∃ t : EMLTerm, t.depth = d ∧ ∀ env : Nat → ℝ, t.eval? env = some (env 0))
    ↔ 4 ∣ d
```

### Depth-3 case (Aristotle-proved in simplified grammar; canonical port partial)

```lean
abbrev ones : Nat → ℝ := fun _ => 1

private lemma eval_ones_pos_of_depth_le_two {t : EMLTerm} (h : t.depth ≤ 2) :
    ∃ v, t.eval? ones = some v ∧ 0 < v := by ...

/-- The statement (full proof in our grammar deferred; Aristotle
chunk 090 has it in a simplified .atom-only grammar). -/
def NoIdentityAtDepthThree : Prop :=
  ¬ ∃ t : EMLTerm, t.depth = 3 ∧
    ∀ env : Nat → ℝ, t.eval? env = some (env 0)
```

---

## 2. `EML/Framework/StructuralLimitsEReal.lean` (Pro #2, part 1)

```lean
namespace EML

/-- The `√x` template, evaluated in extended-real arithmetic at `x = 0`,
gives `0` — the mathematically correct boundary value. -/
theorem sqrt_templateE_at_zero :
    EReal.exp (((1 / 2 : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal 0)) = 0 := by
  rw [ENNReal.ofReal_zero, ENNReal.log_zero]
  rw [EReal.coe_mul_bot_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  exact EReal.exp_bot

/-- `arcosh 1` evaluates to `0` in extended-real arithmetic
(matching `Real.arcosh 1 = 0`). -/
theorem arcosh_templateE_at_one :
    ENNReal.log (ENNReal.ofReal 1 + EReal.exp (((1 / 2 : ℝ) : EReal) *
      ENNReal.log (ENNReal.ofReal ((1:ℝ)^2 - 1)))) = 0 := by ...

/-- `hypot(0, 0)` evaluates to `0` in extended-real arithmetic. -/
theorem hypot_templateE_at_zero_zero :
    EReal.exp (((1 / 2 : ℝ) : EReal) *
      ENNReal.log (ENNReal.ofReal ((0:ℝ)^2 + (0:ℝ)^2))) = 0 := by ...

end EML
```

---

## 3. `EML/Framework/GFullFix.lean` (Pro #2, part 2)

```lean
import EML.Framework.PaperClaims
import EML.Framework.Builders.Constants

namespace EML
namespace EMLTerm

/-- **`√x` on the closed natural domain `[0, ∞)`** (witness family). -/
theorem paper_claim_sqrt_full :
    ∀ env : Nat → ℝ, 0 ≤ env 0 →
      ∃ t : EMLTerm, t.eval? env = some (Real.sqrt (env 0)) := by
  intro env h
  rcases eq_or_lt_of_le h with h0 | hpos
  · refine ⟨mkZero, ?_⟩
    rw [mkZero_eval? env, ← h0, Real.sqrt_zero]
  · obtain ⟨t, ht⟩ := paper_claim_sqrt_pos
    exact ⟨t, ht env hpos⟩

/-- **`arcosh x` on the closed natural domain `[1, ∞)`** (witness family). -/
theorem paper_claim_arcosh_full :
    ∀ env : Nat → ℝ, 1 ≤ env 0 →
      ∃ t : EMLTerm, t.eval? env = some (Real.arcosh (env 0)) := by
  intro env h
  rcases eq_or_lt_of_le h with h1 | hpos
  · refine ⟨mkZero, ?_⟩
    rw [mkZero_eval? env, ← h1, Real.arcosh_zero]
  · obtain ⟨t, ht⟩ := paper_claim_arcosh
    exact ⟨t, ht env hpos⟩

/-- **`hypot(x, y)` on full `ℝ²`** (witness family). -/
theorem paper_claim_hypot_full :
    ∀ env : Nat → ℝ,
      ∃ t : EMLTerm,
        t.eval? env = some (Real.sqrt (env 0 ^ 2 + env 1 ^ 2)) := by
  intro env
  by_cases h : env 0 = 0 ∧ env 1 = 0
  · obtain ⟨h0, h1⟩ := h
    refine ⟨mkZero, ?_⟩
    rw [mkZero_eval? env, h0, h1]
    simp [Real.sqrt_zero]
  · obtain ⟨t, ht⟩ := paper_claim_hypot
    exact ⟨t, ht env h⟩

end EMLTerm
end EML
```

For comparison, the original narrow witnesses live in
`PaperClaims.lean`:

```lean
theorem paper_claim_sqrt_pos :
    ∃ t : EMLTerm, ∀ env : Nat → ℝ, 0 < env 0 →
      t.eval? env = some (Real.sqrt (env 0)) := ...

theorem paper_claim_arcosh :
    ∃ t : EMLTerm, ∀ env : Nat → ℝ, 1 < env 0 →
      t.eval? env = some (Real.arcosh (env 0)) := ...

theorem paper_claim_hypot :
    ∃ t : EMLTerm, ∀ env : Nat → ℝ, ¬(env 0 = 0 ∧ env 1 = 0) →
      t.eval? env = some (Real.sqrt (env 0 ^ 2 + env 1 ^ 2)) := ...
```

Note the quantifier order in original vs `_full`:
- Original: `∃ t : EMLTerm, ∀ env : Nat → ℝ, [hyp] → t.eval? env = some <value>` (one witness for all envs)
- Full: `∀ env : Nat → ℝ, [hyp] → ∃ t : EMLTerm, t.eval? env = some <value>` (one witness per env)

---

## 4. `EML/Framework/EDLClosedVal.lean` (Pro #3)

```lean
namespace EML

/-- Inductive predicate for values reachable from closed EDL terms. -/
inductive EDLClosedVal : ℝ → Prop
  | one : EDLClosedVal 1
  | e_const : EDLClosedVal (Real.exp 1)
  | edl {a b : ℝ} :
      EDLClosedVal a →
      EDLClosedVal b →
      Real.log b ≠ 0 →
      EDLClosedVal (Real.exp a / Real.log b)

/-- An `EDLTerm` is closed when it has no `var n` leaves. -/
def EDLTerm.IsClosed : EDLTerm → Prop
  | .one     => True
  | .e_const => True
  | .var _   => False
  | .edl a b => a.IsClosed ∧ b.IsClosed

/-- **Closure theorem.** -/
theorem edl_closed_eval_in_closedVal :
    ∀ {t : EDLTerm}, t.IsClosed →
    ∀ (env : Nat → ℝ) {v : ℝ}, t.eval? env = some v → EDLClosedVal v
  | .one, _, env, v, he => ...
  | .var _, ht, env, v, he => absurd ht (by simp [EDLTerm.IsClosed])
  | .e_const, _, env, v, he => ...
  | .edl a b, ht, env, v, he => ...

/-- The three transcendence-style non-membership facts that close the
Plan D structural ceiling for `−1`, `2`, and `1/2`. **Conjectural**;
no instance is provided here. -/
class EDLTranscendenceBarrier : Prop where
  neg_one_not_closed : ¬ EDLClosedVal (-1)
  two_not_closed     : ¬ EDLClosedVal 2
  half_not_closed    : ¬ EDLClosedVal ((1 : ℝ) / 2)

variable [EDLTranscendenceBarrier]

theorem no_closed_edl_neg_one :
    ¬ ∃ t : EDLTerm, t.IsClosed ∧
      ∀ env : Nat → ℝ, t.eval? env = some (-1 : ℝ) := by
  rintro ⟨t, ht, h⟩
  exact EDLTranscendenceBarrier.neg_one_not_closed
    (edl_closed_eval_in_closedVal ht (fun _ => 0) (h _))

-- ... and analogously for two, half.

end EML
```

---

## 5. `EML/Framework/PolynomialBinary.lean` (Pro #4)

```lean
import Mathlib

inductive BTerm where
  | var   : Nat → BTerm
  | const : ℝ   → BTerm
  | app   : BTerm → BTerm → BTerm

namespace BTerm

noncomputable def eval (B : ℝ → ℝ → ℝ) (env : Nat → ℝ) : BTerm → ℝ
  | .var n   => env n
  | .const c => c
  | .app a b => B (a.eval B env) (b.eval B env)

end BTerm

def IsPolynomialBinary (B : ℝ → ℝ → ℝ) : Prop :=
  ∃ P : MvPolynomial (Fin 2) ℝ,
    ∀ x y : ℝ, B x y = MvPolynomial.eval ![x, y] P

theorem polynomial_binary_terms_are_polynomial
    {B : ℝ → ℝ → ℝ} (hB : IsPolynomialBinary B)
    (t : BTerm) :
    ∃ P : Polynomial ℝ, ∀ x : ℝ, t.eval B (fun _ => x) = P.eval x := by
  revert hB t
  intro hB t
  induction' t with n c a b ha hb generalizing B
  · exact ⟨ Polynomial.X, fun x => by simp +decide [ BTerm.eval ] ⟩
  · exact ⟨ Polynomial.C c, fun x => by simp +decide [ BTerm.eval ] ⟩
  · obtain ⟨ Q, hQ ⟩ := ha hB
    obtain ⟨ R, hR ⟩ := hb hB
    obtain ⟨ P, hP ⟩ := hB
    use (MvPolynomial.aeval (fun i => if i = 0 then Q else R)) P
    intro x; rw [ BTerm.eval ]; simp +decide [ hP, hQ, hR ]
    erw [ MvPolynomial.eval_eq', MvPolynomial.aeval_eq_eval₂Hom ]
    simp +decide [ Polynomial.eval_finset_sum, MvPolynomial.eval₂Hom,
                   MvPolynomial.eval₂_eq' ]

theorem no_polynomial_binary_generates_exp
    {B : ℝ → ℝ → ℝ} (hB : IsPolynomialBinary B) :
    ¬ ∃ t : BTerm, ∀ x : ℝ, t.eval B (fun _ => x) = Real.exp x := by
  rintro ⟨t, ht⟩
  obtain ⟨P, hP⟩ := polynomial_binary_terms_are_polynomial hB t
  have h_eq : ∀ x, P.eval x = Real.exp x := fun x => hP x ▸ ht x
  have h_lim : Filter.Tendsto (fun x => P.eval x / Real.exp x)
      Filter.atTop (nhds 0) := Polynomial.tendsto_div_exp_atTop P
  have h_const : (fun x => P.eval x / Real.exp x) = (fun _ => (1 : ℝ)) := by
    funext x
    rw [h_eq x, div_self (Real.exp_pos x).ne']
  rw [h_const] at h_lim
  have h_one : Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  exact absurd (tendsto_nhds_unique h_lim h_one) (by norm_num)
```

---

## 6. `EML/Framework/CompactWitnesses.lean` (alternative witnesses)

```lean
/-! ## Compact paper claims

The compact-witness K-counts are **identical** to the structural-
compile counterparts in `KCounting.lean`. This is not a bug: the
F36 → EL → EML compiler already uses the `mk*All` family internally,
so swapping `realize_via_compiler` for direct macro calls produces
the same tree.
-/

/-- **Compact witness — `x · y`.** -/
theorem paper_claim_mul_compact :
    ∃ t : EMLTerm, ∀ env : Nat → ℝ, t.eval? env = some (env 0 * env 1) :=
  ⟨mkMulAll (.var 0) (.var 1), fun env => mkMulAll_eval? env _ _ rfl rfl⟩

-- ... and 8 more for div, avg, pow, logb, hypot, inv, sq, halve.

/-- K(compact mul x y) = 839 743, same as `K_count_mul`. -/
theorem K_count_mul_compact :
    (mkMulAll (.var 0) (.var 1)).RPN_length = 839743 := rfl

-- ... and 8 more K-count theorems, all matching the structural-compile output.
```

---

## Public API check

The following should all `#check` cleanly after `import EML`:

```lean
-- Original (sample)
#check @paper_claim_one
#check @paper_claim_log
#check @paper_claim_mul
#check @paper_claim_pi
#check @paper_claim_cos
#check @paper_claim_sin_full
#check @paper_claim_arctan_full
#check @paper_claim_tan_full

-- Frontier (sample)
#check @paper_claim_sqrt_full       -- GFullFix
#check @paper_claim_arcosh_full     -- GFullFix
#check @paper_claim_hypot_full      -- GFullFix
#check @identity_terms_at_depth_multiples_of_four -- TransplantDepths
#check @no_identity_at_depth_one    -- TransplantDepths
#check @no_identity_at_depth_two    -- TransplantDepths
#check @NoIdentityAtDepthThree      -- TransplantDepths (Prop)
#check @OnlyMultiplesOfFourHaveIdentities -- TransplantDepths (Prop)
#check @sqrt_templateE_at_zero      -- StructuralLimitsEReal
#check @arcosh_templateE_at_one     -- StructuralLimitsEReal
#check @hypot_templateE_at_zero_zero -- StructuralLimitsEReal
#check @edl_closed_eval_in_closedVal -- EDLClosedVal
#check @no_closed_edl_neg_one       -- EDLClosedVal (uses [EDLTranscendenceBarrier])
#check @polynomial_binary_terms_are_polynomial -- PolynomialBinary
#check @no_polynomial_binary_generates_exp -- PolynomialBinary
#check @paper_claim_mul_compact     -- CompactWitnesses
```

All verified to typecheck on commit `66a93ac`.
