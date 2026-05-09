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
opaque EMLTermℂ : Type
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
  sorry
