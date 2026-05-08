import Mathlib

/-!
# `tan_full`: full-real-domain tan witness — Path C′ §4

Combines:
- The existing local Cayley `tan` witnesses `tanCoreTermℂ` (positive)
  and `tanCoreTermℂ_neg` (negative) on `(-π/2, π/2) ∖ {0}`
- The shift term `shiftByPiℂ k` evaluating to `((x - kπ : ℝ) : ℂ)`
- The period reduction `tan_period_reduction` (chunk 079) that gives
  the right `k : ℤ` for any `cos x ≠ 0`

Goal: assemble these into `tan_full`.
-/

-- Opaque framework declarations
-- EMLTermℂ defined as a def to provide Inhabited instance needed by subsequent opaques
def EMLTermℂ : Type := PUnit
deriving instance Inhabited for EMLTermℂ

opaque EMLTermℂ.one : EMLTermℂ
opaque EMLTermℂ.eval? : (Nat → ℂ) → EMLTermℂ → Option ℂ
opaque EMLTermℂ.subst0 : EMLTermℂ → EMLTermℂ → EMLTermℂ
opaque tanCoreTermℂ : EMLTermℂ
opaque tanCoreTermℂ_neg : EMLTermℂ
opaque shiftByPiℂ : ℤ → EMLTermℂ

axiom EMLTermℂ.eval?_one (env : Nat → ℂ) :
    EMLTermℂ.eval? env EMLTermℂ.one = some 1

axiom eval?_subst0 {env : Nat → ℂ} {s : EMLTermℂ} {s_val : ℂ}
    (hs : EMLTermℂ.eval? env s = some s_val) (t : EMLTermℂ) :
    EMLTermℂ.eval? env (EMLTermℂ.subst0 t s) =
      EMLTermℂ.eval? (fun n => if n = 0 then s_val else env n) t

axiom eval?_shiftByPiℂ (x : ℝ) (k : ℤ) (env : Nat → ℂ)
    (henv0 : env 0 = ((x : ℝ) : ℂ)) :
    EMLTermℂ.eval? env (shiftByPiℂ k) = some (((x - (k : ℝ) * Real.pi : ℝ) : ℂ))

-- Local positive tan witness: works for y ∈ (0, π/2)
axiom tanCoreTermℂ_correct (y : ℝ) (hy_lo : 0 < y) (hy_hi : y < Real.pi / 2)
    (env : Nat → ℂ) (henv0 : env 0 = ((y : ℝ) : ℂ)) :
    ∃ vc : ℂ,
      EMLTermℂ.eval? env tanCoreTermℂ = some vc ∧ vc.im = Real.tan y

-- Local negative tan witness: works for y ∈ (-π/2, 0)
axiom tanCoreTermℂ_neg_correct (y : ℝ) (hy_lo : -(Real.pi / 2) < y) (hy_hi : y < 0)
    (env : Nat → ℂ) (henv0 : env 0 = ((y : ℝ) : ℂ)) :
    ∃ vc : ℂ,
      EMLTermℂ.eval? env tanCoreTermℂ_neg = some vc ∧ vc.im = Real.tan y

theorem tan_period_reduction (x : ℝ) (hx : Real.cos x ≠ 0) :
    ∃ k : ℤ, x - (k : ℝ) * Real.pi ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) ∧
             Real.tan x = Real.tan (x - (k : ℝ) * Real.pi) := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, x - k * Real.pi ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2) := by
    use ⌊(x + Real.pi / 2) / Real.pi⌋
    refine ⟨?_, ?_⟩
    · contrapose! hx
      rw [Real.cos_eq_zero_iff]
      exact ⟨⌊(x + Real.pi / 2) / Real.pi⌋ - 1, by
        push_cast
        nlinarith [Int.floor_le ((x + Real.pi / 2) / Real.pi),
                   Int.lt_floor_add_one ((x + Real.pi / 2) / Real.pi),
                   Real.pi_pos,
                   mul_div_cancel₀ (x + Real.pi / 2) Real.pi_ne_zero]⟩
    · nlinarith [Int.lt_floor_add_one ((x + Real.pi / 2) / Real.pi),
                 Real.pi_pos,
                 mul_div_cancel₀ (x + Real.pi / 2) Real.pi_ne_zero]
  exact ⟨k, ⟨by linarith [hk.1], by linarith [hk.2]⟩,
         by simp +decide [Real.tan_sub_int_mul_pi]⟩

/-- **Goal:** `tan_full` covering ℝ ∖ {π/2 + kπ : k : ℤ} (i.e. wherever
`cos x ≠ 0`). -/
theorem tan_full (x : ℝ) (hx : Real.cos x ≠ 0) :
    ∃ t : EMLTermℂ, ∃ vc : ℂ,
      EMLTermℂ.eval? (fun n => if n = 0 then ((x : ℝ) : ℂ) else 0) t = some vc ∧
      vc.im = Real.tan x := by
  obtain ⟨k, hk_mem, htan⟩ := tan_period_reduction x hx
  set y := x - (k : ℝ) * Real.pi with hy_def
  set env := (fun n : Nat => if n = 0 then ((x : ℝ) : ℂ) else 0) with henv_def
  have henv0 : env 0 = ((x : ℝ) : ℂ) := by simp [env]
  have h_shift : EMLTermℂ.eval? env (shiftByPiℂ k) = some ((y : ℝ) : ℂ) :=
    eval?_shiftByPiℂ x k env henv0
  rw [Set.mem_Ioo] at hk_mem
  rcases lt_trichotomy y 0 with hy_neg | hy_zero | hy_pos
  · -- Case y < 0
    have h_sub := eval?_subst0 h_shift tanCoreTermℂ_neg
    set env' := (fun n : Nat => if n = 0 then ((y : ℝ) : ℂ) else env n) with henv'_def
    have henv'0 : env' 0 = ((y : ℝ) : ℂ) := by simp [env']
    obtain ⟨vc, hvc_eval, hvc_im⟩ := tanCoreTermℂ_neg_correct y hk_mem.1 hy_neg env' henv'0
    exact ⟨EMLTermℂ.subst0 tanCoreTermℂ_neg (shiftByPiℂ k), vc,
           by rw [h_sub]; exact hvc_eval,
           by rw [htan]; exact hvc_im⟩
  · -- Case y = 0
    refine ⟨EMLTermℂ.one, 1, EMLTermℂ.eval?_one env, ?_⟩
    simp [Complex.one_im, htan, hy_zero, Real.tan_zero]
  · -- Case y > 0
    have h_sub := eval?_subst0 h_shift tanCoreTermℂ
    set env' := (fun n : Nat => if n = 0 then ((y : ℝ) : ℂ) else env n) with henv'_def
    have henv'0 : env' 0 = ((y : ℝ) : ℂ) := by simp [env']
    obtain ⟨vc, hvc_eval, hvc_im⟩ := tanCoreTermℂ_correct y hy_pos hk_mem.2 env' henv'0
    exact ⟨EMLTermℂ.subst0 tanCoreTermℂ (shiftByPiℂ k), vc,
           by rw [h_sub]; exact hvc_eval,
           by rw [htan]; exact hvc_im⟩
