import Mathlib

/-!
# `sin` via `cos(π/2 − x)` substitution — Path C′ §2

We have an EML term grammar (declared opaquely below) with a known
full-real-domain `cos` witness `cosTermℂ_full` and a known shift term
`halfPiMinusXℂ` evaluating to `((π/2 - x : ℝ) : ℂ)`. The substitution
`cosTermℂ_full.subst0 halfPiMinusXℂ` evaluates correctly to a complex
value whose `.re` is `Real.cos (π/2 - x) = Real.sin x` (the Mathlib
identity `Real.cos_pi_div_two_sub`).

Goal: prove the wrap-up theorem `sin_via_cos_correct` using only the
declared framework axioms and Mathlib's `Real.cos_pi_div_two_sub`.

The framework is declared as opaque axioms here so the proof is
self-contained. The actual definitions live in
`EML.Framework.Complex.Periodicity`, but their structure is
abstracted — Aristotle only needs to glue them together.
-/

-- Opaque framework declarations
-- (Original used bare `opaque` without default values; fixed for Lean 4.28 compatibility
-- by providing a concrete backing type with an Inhabited instance.)
@[irreducible] def EMLTermℂ : Type := PUnit
deriving instance Inhabited for EMLTermℂ

noncomputable opaque EMLTermℂ.eval? : (Nat → ℂ) → EMLTermℂ → Option ℂ :=
  fun _ _ => none
noncomputable opaque EMLTermℂ.subst0 : EMLTermℂ → EMLTermℂ → EMLTermℂ :=
  fun _ _ => default
noncomputable opaque cosTermℂ_full : EMLTermℂ := default
noncomputable opaque halfPiMinusXℂ : EMLTermℂ := default
noncomputable opaque sinViaCosℂ : EMLTermℂ := default

-- Defining axiom for sinViaCosℂ
axiom sinViaCosℂ_def : sinViaCosℂ = EMLTermℂ.subst0 cosTermℂ_full halfPiMinusXℂ

-- Substitution-environment correspondence (eval?_subst0 from Subst.lean)
axiom eval?_subst0 {env : Nat → ℂ} {s : EMLTermℂ} {s_val : ℂ}
    (hs : EMLTermℂ.eval? env s = some s_val) (t : EMLTermℂ) :
    EMLTermℂ.eval? env (EMLTermℂ.subst0 t s) =
      EMLTermℂ.eval? (fun n => if n = 0 then s_val else env n) t

-- The shift evaluation (eval?_halfPiMinusXℂ from Periodicity.lean)
axiom eval?_halfPiMinusXℂ (x : ℝ) (env : Nat → ℂ)
    (henv0 : env 0 = ((x : ℝ) : ℂ)) :
    EMLTermℂ.eval? env halfPiMinusXℂ = some (((Real.pi / 2 - x : ℝ) : ℂ))

-- The full-domain cos witness correctness (paper_claim_cos / paper_claim_cos_neg
-- combined; covers all y ≠ 0)
axiom cosTermℂ_full_correct (y : ℝ) (hy : y ≠ 0) (env : Nat → ℂ)
    (henv0 : env 0 = ((y : ℝ) : ℂ)) :
    ∃ vc : ℂ,
      EMLTermℂ.eval? env cosTermℂ_full = some vc ∧ vc.re = Real.cos y

/-- **Goal:** `sinViaCosℂ` correctness on `ℝ ∖ {π/2}`. -/
theorem sin_via_cos_correct (x : ℝ) (hx : x ≠ Real.pi / 2) :
    ∃ vc : ℂ,
      EMLTermℂ.eval? (fun n => if n = 0 then ((x : ℝ) : ℂ) else 0) sinViaCosℂ
        = some vc ∧
      vc.re = Real.sin x := by
  rw [sinViaCosℂ_def]
  have henv0 : (fun n => if n = 0 then ((x : ℝ) : ℂ) else (0 : ℂ)) 0 = ((x : ℝ) : ℂ) := by simp
  rw [eval?_subst0 (eval?_halfPiMinusXℂ x _ henv0) cosTermℂ_full]
  have hy : Real.pi / 2 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  set env' := (fun n => if n = 0 then ((Real.pi / 2 - x : ℝ) : ℂ) else
    (fun n => if n = 0 then ((x : ℝ) : ℂ) else (0 : ℂ)) n) with henv'_def
  have henv0' : env' 0 = ((Real.pi / 2 - x : ℝ) : ℂ) := by simp [henv'_def]
  obtain ⟨vc, heval, hre⟩ := cosTermℂ_full_correct (Real.pi / 2 - x) hy env' henv0'
  exact ⟨vc, heval, by rw [hre, Real.cos_pi_div_two_sub]⟩
