import Mathlib

/-!
# `arctan` via `arcsin(x / √(1+x²))` substitution — Path C′ §3

We have a full-domain `arcsin` witness `arcsinTermℂ_full` (sealed on
`(-1, 1)`) and a real-fragment compiled term `atanArgℂ` evaluating to
`((x / √(1+x²) : ℝ) : ℂ)`. The substitution `arcsinTermℂ_full.subst0
atanArgℂ` evaluates correctly, and its `.im` is `Real.arcsin (x/√(1+x²))
= Real.arctan x` via Mathlib's `Real.arctan_eq_arcsin`.

Goal: prove the wrap-up theorem `arctan_via_arcsin_correct`.
-/

-- Opaque framework declarations
-- EMLTermℂ needs Nonempty/Inhabited for the opaque values below
structure EMLTermℂ where
  private mk ::
deriving instance Inhabited for EMLTermℂ

noncomputable opaque EMLTermℂ.eval? : (Nat → ℂ) → EMLTermℂ → Option ℂ
noncomputable opaque EMLTermℂ.subst0 : EMLTermℂ → EMLTermℂ → EMLTermℂ
noncomputable opaque arcsinTermℂ_full : EMLTermℂ
noncomputable opaque atanArgℂ : EMLTermℂ
noncomputable opaque arctanViaArcsinℂ : EMLTermℂ

axiom arctanViaArcsinℂ_def :
    arctanViaArcsinℂ = EMLTermℂ.subst0 arcsinTermℂ_full atanArgℂ

axiom eval?_subst0 {env : Nat → ℂ} {s : EMLTermℂ} {s_val : ℂ}
    (hs : EMLTermℂ.eval? env s = some s_val) (t : EMLTermℂ) :
    EMLTermℂ.eval? env (EMLTermℂ.subst0 t s) =
      EMLTermℂ.eval? (fun n => if n = 0 then s_val else env n) t

axiom eval?_atanArgℂ (x : ℝ) (env : Nat → ℂ)
    (henv0 : env 0 = ((x : ℝ) : ℂ)) :
    EMLTermℂ.eval? env atanArgℂ
      = some (((x / Real.sqrt (1 + x^2) : ℝ) : ℂ))

axiom arcsinTermℂ_full_correct (y : ℝ) (hy_lo : -1 < y) (hy_hi : y < 1)
    (env : Nat → ℂ) (henv0 : env 0 = ((y : ℝ) : ℂ)) :
    ∃ vc : ℂ,
      EMLTermℂ.eval? env arcsinTermℂ_full = some vc
      ∧ vc.im = Real.arcsin y

theorem atanArg_in_Ioo (x : ℝ) :
    x / Real.sqrt (1 + x^2) ∈ Set.Ioo (-1 : ℝ) 1 := by
  refine ⟨?_, ?_⟩
  · rw [lt_div_iff₀ (by positivity)]
    nlinarith [Real.sqrt_nonneg (1 + x ^ 2),
               Real.sq_sqrt (by positivity : 0 ≤ 1 + x ^ 2)]
  · rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.sqrt_nonneg (1 + x ^ 2),
               Real.sq_sqrt (by positivity : 0 ≤ 1 + x ^ 2)]

/-- **Goal:** `arctanViaArcsinℂ` correctness on all of ℝ. -/
theorem arctan_via_arcsin_correct (x : ℝ) :
    ∃ vc : ℂ,
      EMLTermℂ.eval? (fun n => if n = 0 then ((x : ℝ) : ℂ) else 0) arctanViaArcsinℂ
        = some vc ∧
      vc.im = Real.arctan x := by
  -- Step 1: unfold arctanViaArcsinℂ
  rw [arctanViaArcsinℂ_def]
  -- Step 2: apply substitution lemma
  set env := (fun n : ℕ => if n = 0 then ((x : ℝ) : ℂ) else 0) with env_def
  have henv0 : env 0 = ((x : ℝ) : ℂ) := by simp [env_def]
  have h_eval_arg := eval?_atanArgℂ x env henv0
  rw [eval?_subst0 h_eval_arg]
  -- Step 3: get bounds
  have hy := atanArg_in_Ioo x
  set y := x / Real.sqrt (1 + x ^ 2) with hy_def
  -- Step 4: apply arcsin correctness
  set env' := (fun n : ℕ => if n = 0 then ((y : ℝ) : ℂ) else env n) with env'_def
  have henv0' : env' 0 = ((y : ℝ) : ℂ) := by simp [env'_def]
  obtain ⟨vc, heval, him⟩ := arcsinTermℂ_full_correct y hy.1 hy.2 env' henv0'
  exact ⟨vc, heval, him.trans (Real.arctan_eq_arcsin x).symm⟩
