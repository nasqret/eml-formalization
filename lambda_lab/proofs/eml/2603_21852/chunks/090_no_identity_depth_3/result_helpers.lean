import EML.Framework.Builders

/-!
# Depth-transplant lemmas

For the all-ones environment `ones := fun _ => 1`, we establish:
- depth 0 ⟹ eval = some 1
- depth 1 ⟹ eval = some (exp 1)
- depth 2 ⟹ eval ∈ { some(exp 1 − 1), some(exp(exp 1)), some(exp(exp 1) − 1) }

These are used in `no_identity_at_depth_three`.
-/

open Real
namespace EML
namespace EMLTerm

/-
================================================================
Depth 0
================================================================
-/
lemma eval_one_of_depth_zero {t : EMLTerm} (h : t.depth = 0) :
    t.eval? ones = some 1 := by
  cases t <;> aesop

/-
================================================================
Depth 1
================================================================
-/
lemma eval_one_of_depth_one {t : EMLTerm} (h : t.depth = 1) :
    t.eval? ones = some (exp 1) := by
  cases t <;> simp_all +decide [ EMLTerm.eval? ];
  rw [ eval_one_of_depth_zero h.1, eval_one_of_depth_zero h.2 ] ; norm_num

/-
================================================================
Depth ≤ 2 : defined and positive
================================================================
-/
lemma eval_ones_pos_of_depth_le_two {t : EMLTerm} (h : t.depth ≤ 2) :
    ∃ v, t.eval? ones = some v ∧ 0 < v := by
  -- By definition of depth, if the depth of t is ≤ 2, then t must be either an atom, an eml node with both children having depth 0, or an eml node with one child having depth 0 and the other having depth 1.
  cases' h' : t.depth with h0 h1 h2;
  · exact ⟨ 1, eval_one_of_depth_zero h', by norm_num ⟩;
  · induction' h0 with h0 ih generalizing t <;> simp_all +decide [ Nat.succ_le_succ_iff ];
    · exact ⟨ _, eval_one_of_depth_one h', Real.exp_pos _ ⟩;
    · rcases t with ( _ | ⟨ a, b ⟩ ) <;> simp_all +arith +decide;
      cases max_choice a.depth b.depth <;> simp_all +decide;
      · interval_cases _ : b.depth <;> simp_all +decide [ EMLTerm.eval? ];
        · obtain ⟨ v, hv₁, hv₂ ⟩ := ih ( by linarith ) h';
          rw [ show b.eval? ones = some 1 from by exact? ] ; simp +decide [ hv₁, hv₂ ];
          positivity;
        · obtain ⟨ v, hv₁, hv₂ ⟩ := ih ( by linarith ) h'; obtain ⟨ w, hw₁, hw₂ ⟩ := ih ( by linarith ) ‹_›; simp_all +decide ;
          have := eval_one_of_depth_one ‹b.depth = 1›; aesop;
      · interval_cases _ : a.depth <;> simp_all +decide [ EMLTerm.eval? ];
        · rw [ eval_one_of_depth_zero ‹a.depth = 0›, eval_one_of_depth_one ‹b.depth = 1› ] ; norm_num [ Real.exp_pos ];
        · obtain ⟨ v, hv₁, hv₂ ⟩ := ih ( by linarith ) ‹_›; obtain ⟨ w, hw₁, hw₂ ⟩ := ih ( by linarith ) h'; simp_all +decide ;
          have := eval_one_of_depth_one h'; aesop;

/-
================================================================
Depth 2 : exact values
================================================================
-/
lemma eval_one_of_depth_two {t : EMLTerm} (h : t.depth = 2) :
    t.eval? ones = some (exp 1 - 1) ∨
    t.eval? ones = some (exp (exp 1)) ∨
    t.eval? ones = some (exp (exp 1) - 1) := by
  rcases t with ( _ | ⟨ a, b ⟩ ) <;> simp_all +decide;
  cases max_choice a.depth b.depth <;> simp_all +decide;
  · interval_cases _ : b.depth <;> simp_all +decide [ EMLTerm.eval?_eml ];
    · rw [ eval_one_of_depth_one h, eval_one_of_depth_zero ‹_› ] ; norm_num;
    · rw [ eval_one_of_depth_one h, eval_one_of_depth_one ‹_› ] ; norm_num;
      exact fun h => absurd h <| not_le_of_gt <| Real.exp_pos _;
  · interval_cases _ : a.depth <;> simp_all +decide [ EMLTerm.eval?_eml ];
    · rw [ eval_one_of_depth_zero ‹a.depth = 0›, eval_one_of_depth_one h ] ; norm_num;
      exact Or.inl fun h => absurd h <| not_le_of_gt <| Real.exp_pos _;
    · rw [ eval_one_of_depth_one ‹a.depth = 1›, eval_one_of_depth_one ‹b.depth = 1› ] ; norm_num [ Real.exp_pos ]

end EMLTerm
end EML