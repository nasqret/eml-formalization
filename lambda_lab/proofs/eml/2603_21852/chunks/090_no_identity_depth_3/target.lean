import Mathlib
import EML.Framework.EMLPartial
import EML.Framework.Builders
import EML.Framework.TransplantDepths

/-!
# Target: no_identity_at_depth_three

SI §1.5 #5 follow-up. The depth-1 and depth-2 cases are already sealed
in `EML.Framework.TransplantDepths`. This file asks Aristotle to seal
the depth-3 case.

The proof pattern, demonstrated for depth 1 and 2 in
`TransplantDepths.lean`, is:
1. A depth-`d` term is `eml a b` with `max(a.depth, b.depth) = d-1`.
2. On the all-ones environment `env := fun _ => 1`, every atom
   evaluates to `some 1`. By induction the all-ones eval at depth
   `k ≥ 1` produces a specific value (or set of values) all
   strictly greater than 1.
3. The identity hypothesis demands `eval = some 1` (since `env 0 = 1`).
   Contradiction.

For depth 3, the case analysis is over `(a.depth, b.depth)` with
max = 2. Six subcases. The exp/log tower bounds needed are:
- `Real.exp 1 > 2` (from `Real.add_one_lt_exp one_ne_zero`)
- `Real.exp (Real.exp 1) > 3`
- `Real.exp (Real.exp 1 - 1) > 1`
- ...and similar.
-/

open EML EMLTerm

theorem no_identity_at_depth_three :
    ¬ ∃ t : EMLTerm, t.depth = 3 ∧
      ∀ env : Nat → ℝ, t.eval? env = some (env 0) := by
  sorry
