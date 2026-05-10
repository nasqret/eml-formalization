import EML.Framework.Sheffer

/-!
# EDLClosedVal — value-level closure for closed EDL terms

GPT Pro's #3-ranked frontier target (consultation 2026-05-10):
formalize the structural ceiling of Plan D (EDL per-primitive
completeness). The 8 sealed witnesses already cover atoms, exp x,
log x, x/y, exp(exp x), log(log x); the remaining 28 paper primitives
(arithmetic, trigonometric, hyperbolic, the constants −1, 2, ½, …)
are conjecturally unreachable from **closed** EDL terms — terms with
no free variables.

This module establishes the closure-theorem half of the structural
ceiling. The other half (the actual transcendence-barrier hypothesis)
is left as a named typeclass `EDLTranscendenceBarrier`, which a future
Mathlib-side Schanuel-style result would need to instantiate.

## What's here

- `EDLClosedVal : ℝ → Prop` — inductive predicate giving the exact
  set of values produced by closed `EDLTerm` evaluations. Generated
  by `1`, `Real.exp 1`, and the `edl(a, b) = exp(a) / log(b)`
  combinator on values where `log b ≠ 0`.
- `EDLTerm.IsClosed : EDLTerm → Prop` — terms with no `var n` leaves.
- `edl_closed_eval_in_closedVal` — the closure theorem: every value
  produced by a closed-term evaluation lies in `EDLClosedVal`. Proved
  by induction on the term.
- `EDLTranscendenceBarrier` — typeclass packaging the three
  non-membership facts `EDLClosedVal {-1, 2, 1/2}` we'd need from
  transcendence theory. Conjectural; not provided here.
- `no_closed_edl_*` — three concrete corollaries: assuming the
  barrier, no closed `EDLTerm` evaluates to `-1`, `2`, or `1/2`.

## Why this is **not** a Schanuel proof

Pro flagged that "the closed-EDL value set lives in a fixed
transcendence-degree extension of ℚ(e)" is probably false: iterates
like `e, exp e, exp(exp e), …` should generate unbounded transcendence
degree under Schanuel's conjecture. So the barrier is genuinely
unproven and we keep it as a typeclass hypothesis rather than
asserting it.

The chunks/085 commentary from Aristotle remains the source-of-record
informal argument; this module is the formal scaffolding around that
commentary.
-/

namespace EML

/-- Inductive predicate for the values reachable as evaluations of
**closed** `EDLTerm`s (terms with no `var` leaves). The constructors
mirror the EDL grammar: `1` and `Real.exp 1` are the two atomic
constants, and the `edl` combinator generates new values via
`exp(a) / log(b)` when `log b ≠ 0`. -/
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

@[simp] lemma EDLTerm.IsClosed_one : (EDLTerm.one).IsClosed := True.intro
@[simp] lemma EDLTerm.IsClosed_e_const : (EDLTerm.e_const).IsClosed := True.intro
@[simp] lemma EDLTerm.IsClosed_var (n : Nat) :
    ¬ (EDLTerm.var n).IsClosed := id
@[simp] lemma EDLTerm.IsClosed_edl (a b : EDLTerm) :
    (EDLTerm.edl a b).IsClosed ↔ a.IsClosed ∧ b.IsClosed := Iff.rfl

/-- **Closure theorem.** Every value produced by evaluating a closed
`EDLTerm` lies in the inductive class `EDLClosedVal`. -/
theorem edl_closed_eval_in_closedVal :
    ∀ {t : EDLTerm}, t.IsClosed →
    ∀ (env : Nat → ℝ) {v : ℝ}, t.eval? env = some v → EDLClosedVal v
  | .one,     _,  env, v, he => by
      simp [EDLTerm.eval?] at he; rw [← he]; exact .one
  | .var _,   ht, env, v, he => absurd ht (by simp [EDLTerm.IsClosed])
  | .e_const, _,  env, v, he => by
      simp [EDLTerm.eval?] at he; rw [← he]; exact .e_const
  | .edl a b, ht, env, v, he => by
      have ⟨ha, hb⟩ : a.IsClosed ∧ b.IsClosed := ht
      -- Step through the eval? definition manually using `show` + `rw`
      -- to expose each level of the bind chain.
      have he' : (a.eval? env).bind (fun va =>
                   (b.eval? env).bind (fun vb =>
                     if Real.log vb = 0 then none
                     else some (Real.exp va / Real.log vb))) = some v := he
      cases ha_eval : a.eval? env with
      | none => rw [ha_eval] at he'; cases he'
      | some va =>
        rw [ha_eval] at he'
        change (b.eval? env).bind _ = _ at he'
        cases hb_eval : b.eval? env with
        | none => rw [hb_eval] at he'; cases he'
        | some vb =>
          rw [hb_eval] at he'
          change (if Real.log vb = 0 then none
                  else some (Real.exp va / Real.log vb)) = some v at he'
          have iha : EDLClosedVal va :=
            edl_closed_eval_in_closedVal ha env ha_eval
          have ihb : EDLClosedVal vb :=
            edl_closed_eval_in_closedVal hb env hb_eval
          by_cases h0 : Real.log vb = 0
          · rw [if_pos h0] at he'; cases he'
          · rw [if_neg h0] at he'
            have : v = Real.exp va / Real.log vb := by
              injection he' with h_eq; exact h_eq.symm
            rw [this]
            exact .edl iha ihb h0

/-! ## The transcendence-barrier hypothesis

The values `-1`, `2`, and `1/2` are conjecturally not in
`EDLClosedVal`. Proving this in Mathlib would require a Schanuel-style
result connecting the transcendence degree of the EL-closure of
`{1, e}` to the integers — currently out of reach. We package the
three non-membership facts as a typeclass so that downstream theorems
can be stated cleanly.

A future Mathlib instance of `EDLTranscendenceBarrier` would close
the structural ceiling for the corresponding EDL paper claims; until
then, the typeclass is intentionally not provided.
-/

/-- The three transcendence-style non-membership facts that close the
Plan D structural ceiling for `−1`, `2`, and `1/2`. Conjectural;
no instance is provided here. -/
class EDLTranscendenceBarrier : Prop where
  neg_one_not_closed : ¬ EDLClosedVal (-1)
  two_not_closed     : ¬ EDLClosedVal 2
  half_not_closed    : ¬ EDLClosedVal ((1 : ℝ) / 2)

variable [EDLTranscendenceBarrier]

/-- **Plan D structural ceiling — `−1`.** Assuming the transcendence
barrier, no closed `EDLTerm` evaluates to `-1`. -/
theorem no_closed_edl_neg_one :
    ¬ ∃ t : EDLTerm, t.IsClosed ∧
      ∀ env : Nat → ℝ, t.eval? env = some (-1 : ℝ) := by
  rintro ⟨t, ht, h⟩
  exact EDLTranscendenceBarrier.neg_one_not_closed
    (edl_closed_eval_in_closedVal ht (fun _ => 0) (h _))

/-- **Plan D structural ceiling — `2`.** Assuming the transcendence
barrier, no closed `EDLTerm` evaluates to `2`. -/
theorem no_closed_edl_two :
    ¬ ∃ t : EDLTerm, t.IsClosed ∧
      ∀ env : Nat → ℝ, t.eval? env = some (2 : ℝ) := by
  rintro ⟨t, ht, h⟩
  exact EDLTranscendenceBarrier.two_not_closed
    (edl_closed_eval_in_closedVal ht (fun _ => 0) (h _))

/-- **Plan D structural ceiling — `1/2`.** Assuming the transcendence
barrier, no closed `EDLTerm` evaluates to `1/2`. -/
theorem no_closed_edl_half :
    ¬ ∃ t : EDLTerm, t.IsClosed ∧
      ∀ env : Nat → ℝ, t.eval? env = some ((1 : ℝ) / 2) := by
  rintro ⟨t, ht, h⟩
  exact EDLTranscendenceBarrier.half_not_closed
    (edl_closed_eval_in_closedVal ht (fun _ => 0) (h _))

end EML
