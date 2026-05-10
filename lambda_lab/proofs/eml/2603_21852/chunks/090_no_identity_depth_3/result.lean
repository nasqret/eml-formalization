import Mathlib
import EML.Framework.TransplantDepths

/-!
# Target: no_identity_at_depth_three

No EML term of depth exactly 3 evaluates to the identity function
on every real environment.
-/

open Real EML EMLTerm

/-
================================================================
Key helper: depth-3 eval on ones is never `some 1`
================================================================

For a depth-3 term, `eval? t ones ≠ some 1`.  The proof case-splits
    on the child depths and uses `eval_one_of_depth_zero/one/two` to
    determine the exact child values, then rules out each candidate.
-/
private lemma eval_ones_depth_three_ne_one {t : EMLTerm} (h : t.depth = 3) :
    t.eval? ones ≠ some 1 := by
  by_contra h_contra;
  rcases t with ( _ | ⟨ a, b ⟩ ) <;> simp_all +decide [ EMLTerm.eval? ];
  -- Since the maximum of their depths is 2, we have two cases: either `a.depth = 2` and `b.depth ≤ 2`, or `a.depth ≤ 2` and `b.depth = 2`.
  by_cases ha : a.depth = 2;
  · obtain ⟨va, hva⟩ : ∃ va, a.eval? ones = some va ∧ 0 < va := by
      exact eval_ones_pos_of_depth_le_two ( by linarith ) |> fun ⟨ va, hva₁, hva₂ ⟩ => ⟨ va, hva₁, hva₂ ⟩
    obtain ⟨vb, hvb⟩ : ∃ vb, b.eval? ones = some vb ∧ 0 < vb := by
      cases h : b.eval? ones <;> aesop;
    -- Since `a.depth = 2`, we have `va ∈ {exp 1 - 1, exp (exp 1), exp (exp 1) - 1}`.
    have hva_cases : va = Real.exp 1 - 1 ∨ va = Real.exp (Real.exp 1) ∨ va = Real.exp (Real.exp 1) - 1 := by
      have := eval_one_of_depth_two ha; aesop;
    rcases hva_cases with ( rfl | rfl | rfl ) <;> norm_num [ hva, hvb ] at h_contra;
    · -- Since `b.depth ≤ 2`, we have `vb ∈ {1, exp 1, exp 1 - 1, exp (exp 1), exp (exp 1) - 1}`.
      have hvb_cases : vb = 1 ∨ vb = Real.exp 1 ∨ vb = Real.exp 1 - 1 ∨ vb = Real.exp (Real.exp 1) ∨ vb = Real.exp (Real.exp 1) - 1 := by
        have hvb_cases : b.depth ≤ 2 := by
          exact h ▸ le_max_right _ _;
        interval_cases _ : b.depth <;> simp_all +decide;
        · have := eval_one_of_depth_zero ‹_›; aesop;
        · have := eval_one_of_depth_one ‹_›; aesop;
        · have := eval_one_of_depth_two ‹_›; aesop;
      rcases hvb_cases with ( rfl | rfl | rfl | rfl | rfl ) <;> norm_num at h_contra;
      · linarith;
      · linarith [ Real.add_one_lt_exp ( show Real.exp 1 - 1 ≠ 0 by linarith ), Real.add_one_lt_exp ( show 1 ≠ 0 by norm_num ) ];
      · have := Real.add_one_le_exp ( Real.exp 1 - 1 );
        linarith [ Real.add_one_le_exp 1, Real.log_le_sub_one_of_pos hvb.2 ];
      · rw [ show Real.exp ( Real.exp 1 - 1 ) = Real.exp 1 * Real.exp ( Real.exp 1 - 2 ) by rw [ ← Real.exp_add ] ; ring ] at h_contra;
        have := Real.exp_one_gt_d9.le;
        nlinarith [ Real.add_one_le_exp ( Real.exp 1 - 2 ), Real.exp_pos ( Real.exp 1 - 2 ) ];
      · -- We'll use that $e^{e-1} > e + 1$ to derive a contradiction.
        have h_exp_gt : Real.exp (Real.exp 1 - 1) > Real.exp 1 + 1 := by
          rw [ show Real.exp ( Real.exp 1 - 1 ) = Real.exp 1 * Real.exp ( Real.exp 1 - 2 ) by rw [ ← Real.exp_add ] ; ring ];
          have := Real.exp_one_gt_d9.le;
          nlinarith [ Real.add_one_le_exp ( Real.exp 1 - 2 ) ];
        have h_log_lt : Real.log (Real.exp (Real.exp 1) - 1) < Real.exp 1 := by
          rw [ Real.log_lt_iff_lt_exp ] <;> linarith [ Real.add_one_le_exp 1, Real.add_one_le_exp ( Real.exp 1 ) ];
        linarith;
    · -- Since `b.depth ≤ 2`, we have `vb ∈ {1, exp 1, exp 1 - 1, exp (exp 1), exp (exp 1) - 1}`.
      have hvb_cases : vb = 1 ∨ vb = Real.exp 1 ∨ vb = Real.exp 1 - 1 ∨ vb = Real.exp (Real.exp 1) ∨ vb = Real.exp (Real.exp 1) - 1 := by
        have hvb_cases : b.depth ≤ 2 := by
          exact h ▸ le_max_right _ _;
        interval_cases _ : b.depth <;> simp_all +decide;
        · have := eval_one_of_depth_zero ‹_›; aesop;
        · have := eval_one_of_depth_one ‹_›; aesop;
        · have := eval_one_of_depth_two ‹_›; aesop;
      rcases hvb_cases with ( rfl | rfl | rfl | rfl | rfl ) <;> norm_num at h_contra;
      · linarith [ Real.add_one_le_exp 1, Real.add_one_le_exp ( Real.exp 1 ), Real.add_one_le_exp ( Real.exp ( Real.exp 1 ) ) ];
      · linarith [ Real.add_one_le_exp 1, Real.add_one_le_exp ( Real.exp 1 ), Real.add_one_le_exp ( Real.exp ( Real.exp 1 ) ), Real.log_le_sub_one_of_pos hvb.2 ];
      · linarith [ Real.add_one_le_exp 1, Real.add_one_le_exp ( Real.exp 1 ), Real.add_one_le_exp ( Real.exp ( Real.exp 1 ) ) ];
      · linarith [ Real.add_one_le_exp ( Real.exp ( Real.exp 1 ) ), Real.log_le_sub_one_of_pos ( show 0 < Real.exp ( Real.exp 1 ) - 1 from hvb.2 ), Real.add_one_le_exp 1, Real.add_one_le_exp ( Real.exp 1 ) ];
    · -- Since `b.depth ≤ 2`, we have `vb ∈ {1, exp 1, exp 1 - 1, exp (exp 1), exp (exp 1) - 1}`.
      have hvb_cases : vb = 1 ∨ vb = Real.exp 1 ∨ vb = Real.exp 1 - 1 ∨ vb = Real.exp (Real.exp 1) ∨ vb = Real.exp (Real.exp 1) - 1 := by
        have hvb_cases : b.depth ≤ 2 := by
          exact h ▸ le_max_right _ _;
        interval_cases _ : b.depth <;> simp_all +decide;
        · have := eval_one_of_depth_zero ‹_›; aesop;
        · have := eval_one_of_depth_one ‹_›; aesop;
        · have := eval_one_of_depth_two ‹_›; aesop;
      rcases hvb_cases with ( rfl | rfl | rfl | rfl | rfl ) <;> norm_num at *;
      · linarith [ Real.add_one_le_exp ( Real.exp 1 ), Real.add_one_le_exp 1 ];
      · linarith [ Real.add_one_le_exp 1, Real.add_one_le_exp ( Real.exp 1 ), Real.add_one_le_exp ( Real.exp ( Real.exp 1 ) - 1 ) ];
      · have := Real.add_one_le_exp 1;
        linarith [ Real.add_one_le_exp ( Real.exp ( Real.exp 1 ) - 1 ), Real.log_le_sub_one_of_pos ( show 0 < Real.exp 1 - 1 by linarith ), Real.add_one_le_exp ( Real.exp 1 ) ];
      · have := Real.add_one_le_exp ( Real.exp ( Real.exp 1 ) - 1 - 1 );
        norm_num [ Real.exp_sub ] at *;
        rw [ div_add_one, le_div_iff₀ ] at this <;> nlinarith [ Real.add_one_le_exp 1, Real.add_one_le_exp ( Real.exp 1 ), Real.add_one_le_exp ( Real.exp ( Real.exp 1 ) ) ];
      · have := Real.add_one_le_exp ( Real.exp ( Real.exp 1 ) - 1 );
        linarith [ Real.add_one_le_exp 1, Real.log_le_sub_one_of_pos ( show 0 < Real.exp ( Real.exp 1 ) - 1 from by norm_num [ Real.exp_pos ] ) ];
  · -- Since `a.depth ≠ 2`, we must have `b.depth = 2`.
    have hb : b.depth = 2 := by
      bv_omega;
    rcases h : a.eval? ones with ( _ | va ) <;> rcases h' : b.eval? ones with ( _ | vb ) <;> simp_all +decide;
    interval_cases _ : a.depth <;> simp_all +decide;
    · have := eval_one_of_depth_zero ‹_›; simp_all +decide ;
      have := eval_one_of_depth_two hb; simp_all +decide ;
      rcases this with ( rfl | rfl | rfl ) <;> norm_num [ ← h ] at *;
      · have := Real.exp_one_gt_d9.le ; norm_num at * ; linarith [ Real.log_lt_sub_one_of_pos ( show 0 < Real.exp 1 - 1 by linarith [ Real.add_one_le_exp 1 ] ) ( by linarith [ Real.add_one_le_exp 1 ] ) ];
      · have := Real.exp_one_gt_d9.le ; norm_num1 at * ; rw [ show ( Real.exp ( Real.exp 1 ) - 1 : ℝ ) = ( Real.exp 1 ) * ( Real.exp ( Real.exp 1 - 1 ) - 1 / Real.exp 1 ) by rw [ mul_sub, mul_div_cancel₀ _ ( ne_of_gt ( Real.exp_pos 1 ) ) ] ; rw [ ← Real.exp_add ] ; ring ] at h_contra ; rw [ Real.log_mul ( by positivity ) ( by exact ne_of_gt ( sub_pos.mpr ( by rw [ div_lt_iff₀ ( by positivity ) ] ; nlinarith [ Real.add_one_le_exp 1, Real.add_one_le_exp ( Real.exp 1 - 1 ) ] ) ) ) ] at h_contra ; norm_num at h_contra;
        have := congr_arg Real.exp h_contra.2 ; norm_num [ Real.exp_sub, Real.exp_log ( show 0 < Real.exp ( Real.exp 1 - 1 ) - ( Real.exp 1 ) ⁻¹ from sub_pos.mpr <| by nlinarith [ Real.add_one_le_exp 1, Real.add_one_le_exp ( Real.exp 1 - 1 ), mul_inv_cancel₀ <| ne_of_gt <| Real.exp_pos 1 ] ) ] at this;
        rw [ Real.exp_add, Real.exp_log ( by nlinarith [ Real.add_one_le_exp 1, Real.add_one_le_exp ( Real.exp 1 ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos 1 ) ), div_mul_cancel₀ ( Real.exp ( Real.exp 1 ) ) ( ne_of_gt ( Real.exp_pos 1 ) ) ] ) ] at this ; ring_nf at this ; norm_num [ Real.exp_ne_zero ] at this;
        rw [ ← div_eq_mul_inv, div_eq_iff ] at this <;> nlinarith [ Real.add_one_le_exp 1, Real.add_one_le_exp ( Real.exp 1 ) ];
    · have := eval_one_of_depth_one ‹_›; simp_all +decide ;
      have := eval_one_of_depth_two hb; simp_all +decide ;
      rcases this with ( rfl | rfl | rfl ) <;> norm_num [ ← h ] at *;
      · have := Real.add_one_le_exp 1 ; norm_num at this ; linarith [ Real.add_one_le_exp ( Real.exp 1 ), Real.log_le_sub_one_of_pos ( show 0 < Real.exp 1 - 1 by linarith [ Real.add_one_le_exp 1 ] ) ];
      · have := Real.exp_one_gt_d9.le ; norm_num1 at * ; rw [ show Real.exp ( Real.exp 1 ) = Real.exp 1 * Real.exp ( Real.exp 1 - 1 ) by rw [ ← Real.exp_add ] ; ring ] at h_contra ; nlinarith [ Real.add_one_le_exp ( Real.exp 1 - 1 ) ];
      · have := Real.add_one_le_exp 1 ; norm_num at this ; linarith [ Real.add_one_le_exp ( Real.exp 1 ), Real.log_lt_sub_one_of_pos ( show 0 < Real.exp ( Real.exp 1 ) - 1 from by linarith [ Real.add_one_le_exp 1, Real.add_one_le_exp ( Real.exp 1 ) ] ) ( by linarith [ Real.add_one_le_exp 1, Real.add_one_le_exp ( Real.exp 1 ) ] ) ]

-- ================================================================
-- Main theorem
-- ================================================================

theorem no_identity_at_depth_three :
    ¬ ∃ t : EMLTerm, t.depth = 3 ∧
      ∀ env : Nat → ℝ, t.eval? env = some (env 0) := by
  intro ⟨t, hdepth, hid⟩
  have h1 := hid ones
  simp [ones] at h1
  exact eval_ones_depth_three_ne_one hdepth h1