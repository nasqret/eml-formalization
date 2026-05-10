import Mathlib
import EML.Framework.EMLPartial
import EML.Framework.Builders
import EML.Framework.TransplantDepths

/-!
# SI §1.5 #5 — port of depth-3 nonexistence to the canonical grammar

Aristotle previously (chunk 090) proved this theorem in a simplified
EMLTerm grammar with a single `.atom` constructor. Here we port the
same result to the canonical artefact grammar which has TWO atom
constructors `.one` and `.var n`.

The mathematical argument is identical (case-split on `(a.depth, b.depth)`
with max=2; use `eval_one_of_depth_zero/one/two` helpers; rule out each
candidate value via `Real.add_one_le_exp`, `Real.exp_one_gt_d9`, etc.).
The only difference is that wherever Aristotle's proof said "atom" we
need to handle two sub-cases (`.one` and `.var n`) — both of which
evaluate to `1` on the all-ones environment.

The required helpers (`eval_one_of_depth_zero`, `eval_one_of_depth_one`,
`eval_one_of_depth_two`) already exist in `EML.Framework.TransplantDepths`.
A new helper `ones` (the all-ones environment) and
`eval_ones_pos_of_depth_le_two` (any depth ≤ 2 term evaluates to a
positive value on `ones`) need to be added.
-/

open EML EMLTerm

/-- The all-ones environment: every variable maps to 1. -/
abbrev ones : Nat → ℝ := fun _ => 1

/-- For any depth ≤ 2 term, the all-ones evaluation is some positive
real. -/
lemma eval_ones_pos_of_depth_le_two {t : EMLTerm} (h : t.depth ≤ 2) :
    ∃ v, t.eval? ones = some v ∧ 0 < v := by
  sorry

/-- **No identity term at depth 3 in the canonical EMLTerm grammar.** -/
theorem no_identity_at_depth_three :
    ¬ ∃ t : EMLTerm, t.depth = 3 ∧
      ∀ env : Nat → ℝ, t.eval? env = some (env 0) := by
  sorry
