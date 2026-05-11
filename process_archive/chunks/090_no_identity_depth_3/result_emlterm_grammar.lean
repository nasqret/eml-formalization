import Mathlib

/-!
# EML Terms — core definitions

An **EML term** is a binary tree whose leaves are variable references (atoms)
and whose internal nodes represent the operation `(a, b) ↦ exp(a) − log(b)`.
`eval?` is partial: it returns `none` when the second child evaluates to a
non-positive number (so that `log` is meaningful).
-/

namespace EML

/-- An EML term: either an atom (variable reference) or a binary node
    representing `exp(left) − log(right)`. -/
inductive EMLTerm where
  | atom : Nat → EMLTerm
  | eml  : EMLTerm → EMLTerm → EMLTerm
  deriving DecidableEq, Repr

namespace EMLTerm

/-- Depth of an EML term. Atoms have depth 0; a node `eml a b` has depth
    `max(a.depth, b.depth) + 1`. -/
def depth : EMLTerm → Nat
  | .atom _ => 0
  | .eml a b => max a.depth b.depth + 1

/-- Partial evaluation under an environment `env : Nat → ℝ`.
    Returns `none` when the right child of an `eml` node evaluates to ≤ 0. -/
noncomputable def eval? : EMLTerm → (Nat → ℝ) → Option ℝ
  | .atom n, env => some (env n)
  | .eml a b, env =>
      match a.eval? env, b.eval? env with
      | some va, some vb =>
          if 0 < vb then some (Real.exp va - Real.log vb) else none
      | _, _ => none

/-- The constant-1 environment used for the all-ones trick. -/
abbrev ones : Nat → ℝ := fun _ => 1

-- ---------------------------------------------------------------
-- Basic simp lemmas
-- ---------------------------------------------------------------

@[simp] lemma depth_atom (n : Nat) : (atom n).depth = 0 := rfl
@[simp] lemma depth_eml (a b : EMLTerm) :
    (eml a b).depth = max a.depth b.depth + 1 := rfl

@[simp] lemma eval?_atom (n : Nat) (env : Nat → ℝ) :
    (atom n).eval? env = some (env n) := rfl

lemma eval?_eml (a b : EMLTerm) (env : Nat → ℝ) :
    (eml a b).eval? env =
      match a.eval? env, b.eval? env with
      | some va, some vb =>
          if 0 < vb then some (Real.exp va - Real.log vb) else none
      | _, _ => none := rfl

end EMLTerm
end EML
