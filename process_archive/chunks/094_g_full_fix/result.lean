import Mathlib

/-!
# §G full fix — extend boundary point witnesses to closed natural domains

We define `EMLTerm`, a simple expression language with partial evaluation
(`eval?` returns `none` when domain constraints are violated), and prove
that `sqrt`, `arcosh`, and `hypot` can each be represented by a single
term that is total on its natural domain.
-/

/-- A minimal expression-tree language for real-valued functions. -/
inductive EMLTerm where
  | var     : Nat → EMLTerm
  | const   : ℝ → EMLTerm
  | add     : EMLTerm → EMLTerm → EMLTerm
  | mul     : EMLTerm → EMLTerm → EMLTerm
  | pow2    : EMLTerm → EMLTerm            -- t²
  | sqrtT   : EMLTerm → EMLTerm            -- √t,  defined when t ≥ 0
  | arcoshT : EMLTerm → EMLTerm            -- arcosh t,  defined when t ≥ 1

/-- Partial evaluator: returns `none` when a domain constraint is violated. -/
noncomputable def EMLTerm.eval? (t : EMLTerm) (env : Nat → ℝ) : Option ℝ :=
  match t with
  | EMLTerm.var n      => some (env n)
  | EMLTerm.const c    => some c
  | EMLTerm.add a b    => match a.eval? env, b.eval? env with
                           | some va, some vb => some (va + vb)
                           | _, _ => none
  | EMLTerm.mul a b    => match a.eval? env, b.eval? env with
                           | some va, some vb => some (va * vb)
                           | _, _ => none
  | EMLTerm.pow2 s     => match s.eval? env with
                           | some v => some (v ^ 2)
                           | none => none
  | EMLTerm.sqrtT s    => match s.eval? env with
                           | some v => if 0 ≤ v then some (Real.sqrt v) else none
                           | none => none
  | EMLTerm.arcoshT s  => match s.eval? env with
                           | some v => if 1 ≤ v then some (Real.arcosh v) else none
                           | none => none

/-! ## Full-domain witnesses -/

/-
`sqrt` is representable on its full natural domain `[0, ∞)`.
-/
theorem paper_claim_sqrt_full :
    ∃ t : EMLTerm, ∀ env : Nat → ℝ, 0 ≤ env 0 →
      t.eval? env = some (Real.sqrt (env 0)) := by
        -- Define the expression tree for sqrt(x)
        use EMLTerm.sqrtT (EMLTerm.var 0);
        -- By definition of `sqrtT`, we have `sqrtT (var 0) = sqrt (var 0)`.
        simp [EMLTerm.eval?]

/-
`arcosh` is representable on its full natural domain `[1, ∞)`.
-/
theorem paper_claim_arcosh_full :
    ∃ t : EMLTerm, ∀ env : Nat → ℝ, 1 ≤ env 0 →
      t.eval? env = some (Real.arcosh (env 0)) := by
        exact ⟨ EMLTerm.arcoshT ( EMLTerm.var 0 ), fun env h => by unfold EMLTerm.eval?; exact if_pos h ⟩

/-
`hypot` is representable on the full plane `ℝ²` (no domain restriction).
-/
theorem paper_claim_hypot_full :
    ∃ t : EMLTerm, ∀ env : Nat → ℝ,
      t.eval? env = some (Real.sqrt (env 0 ^ 2 + env 1 ^ 2)) := by
        constructor;
        intro env;
        swap;
        exact EMLTerm.sqrtT ( EMLTerm.add ( EMLTerm.pow2 ( EMLTerm.var 0 ) ) ( EMLTerm.pow2 ( EMLTerm.var 1 ) ) );
        exact if_pos ( add_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) )