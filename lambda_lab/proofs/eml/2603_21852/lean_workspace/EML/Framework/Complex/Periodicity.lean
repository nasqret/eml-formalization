import EML.Framework.Complex.Subst
import EML.Framework.Complex.Builders.Trig

/-!
# Periodicity infrastructure for trig witnesses (Plan C′)

Following GPT Pro's recommendation (`gpt_pro_bundle/trig_widening/RESPONSE.md`),
this file provides the **real-safe addition** layer that lets us build
period shifts via repeated `mkAddℂ` of fixed real constants — staying
entirely in the real fragment, so the `arg = π` boundary trap never
appears.

## What's here

- `ADDsafeℂ_ofReal_ofReal` — the foundational lemma: when both
  arguments are real-valued (i.e. `((aR : ℝ) : ℂ)`), the gnarly 11-field
  `ADDsafeℂ` bundle holds automatically.
- `eval?_mkAddℂ_ofReal` — packaged form: adding two real-valued
  `EMLTermℂ` evaluations gives the cast of their real sum.
- `twoPiPubℂ`, `piPubℂ`, `negPiPubℂ` — public period-constants used by
  shift constructions.

## What's not yet here (next session)

- Period shift terms (`shiftByPeriodℂ : ℤ → EMLTermℂ`) and their eval
  lemmas
- `sin x = cos(π/2 − x)` substitution witness (Path C′ §2)
- `arctan x = arcsin(x / √(1+x²))` substitution witness (Path C′ §3)
- `tan` periodic substitution (Path C′ §4)

See `Periodicity.md` for the full implementation roadmap.
-/

namespace EML

open Complex

/-! ## §C′.0 — Real-safe addition foundation -/

/-- The `ADDsafeℂ` bundle holds automatically when both arguments are
real-valued (i.e. `((aR : ℝ) : ℂ)` and `((bR : ℝ) : ℂ)` for some
`aR bR : ℝ`).

This is the foundational lemma of Path C′: it lets us build period-
shifts via repeated `mkAddℂ` of fixed real constants without ever
encountering the `arg = π` boundary. The 11 conditions in `ADDsafeℂ`
all reduce to `.im = 0` inequalities (trivially in `(−π, π]`) plus
the non-vanishing of `Real.exp aR − aR`, which holds since
`Real.exp aR ≥ aR + 1`. -/
lemma ADDsafeℂ_ofReal_ofReal (a b : ℝ) :
    ADDsafeℂ ((a : ℝ) : ℂ) ((b : ℝ) : ℂ) := by
  -- Foundational fact: Real.exp a - a > 0 (so its complex cast is nonzero).
  have h_exp_a_minus_a_pos : 0 < Real.exp a - a := by
    have h := Real.add_one_le_exp a; nlinarith
  have hpi : 0 < Real.pi := Real.pi_pos
  -- Identify the relevant complex expressions with their real casts.
  have h_exp_α : Complex.exp ((a : ℝ) : ℂ) = ((Real.exp a : ℝ) : ℂ) :=
    (Complex.ofReal_exp a).symm
  have h_exp_α_minus_α : Complex.exp ((a : ℝ) : ℂ) - ((a : ℝ) : ℂ) =
                          ((Real.exp a - a : ℝ) : ℂ) := by
    rw [h_exp_α]; push_cast; ring
  have h_log_eq :
      Complex.log (Complex.exp ((a : ℝ) : ℂ) - ((a : ℝ) : ℂ)) =
        ((Real.log (Real.exp a - a) : ℝ) : ℂ) := by
    rw [h_exp_α_minus_α]
    exact (Complex.ofReal_log h_exp_a_minus_a_pos.le).symm
  -- The .im = 0 facts for all the real-valued sub-expressions:
  have h_α_im : ((a : ℝ) : ℂ).im = 0 := Complex.ofReal_im a
  have h_β_im : ((b : ℝ) : ℂ).im = 0 := Complex.ofReal_im b
  have h_exp1_im : (Complex.exp 1).im = 0 := by simp [Complex.exp_im]
  have h_exp_a_minus_a_im : (((Real.exp a - a : ℝ) : ℂ)).im = 0 :=
    Complex.ofReal_im _
  have h_log_eaa_im : (((Real.log (Real.exp a - a) : ℝ) : ℂ)).im = 0 :=
    Complex.ofReal_im _
  exact {
    ha₁ := by rw [h_α_im]; linarith
    ha₂ := by rw [h_α_im]; linarith
    hema₁ := by rw [Complex.sub_im, h_exp1_im, h_α_im]; linarith
    hema₂ := by rw [Complex.sub_im, h_exp1_im, h_α_im]; linarith
    hexpa_a_ne := by
      rw [h_exp_α_minus_α]
      intro h
      apply h_exp_a_minus_a_pos.ne'
      exact_mod_cast h
    hb₁ := by rw [h_β_im]; linarith
    hb₂ := by rw [h_β_im]; linarith
    helogexpa₁ := by
      rw [h_log_eq, Complex.sub_im, h_exp1_im, h_log_eaa_im]; linarith
    helogexpa₂ := by
      rw [h_log_eq, Complex.sub_im, h_exp1_im, h_log_eaa_im]; linarith
    hexp_a_a_b₁ := by
      rw [h_exp_α_minus_α, Complex.sub_im, h_exp_a_minus_a_im, h_β_im]
      linarith
    hexp_a_a_b₂ := by
      rw [h_exp_α_minus_α, Complex.sub_im, h_exp_a_minus_a_im, h_β_im]
      linarith
  }

/-- Packaged form: adding two real-valued `EMLTermℂ` evaluations gives
the cast of their real sum, with no side conditions. -/
lemma eval?_mkAddℂ_ofReal
    {env : Nat → ℂ} {A B : EMLTermℂ} {a b : ℝ}
    (hA : A.eval? env = some ((a : ℝ) : ℂ))
    (hB : B.eval? env = some ((b : ℝ) : ℂ)) :
    (mkAddℂ A B).eval? env = some (((a + b : ℝ) : ℂ)) := by
  have h := eval?_mkAddℂ hA hB (ADDsafeℂ_ofReal_ofReal a b)
  rw [h]
  push_cast
  ring_nf

/-! ### Real-positive helpers — code-golf shortcuts

These helpers package the constraint chains for `mkMulℂ` / `mkSubℂ` /
`mkDivℂ` when both arguments are real-valued and (where required)
strictly positive. They cut every period-constant proof from ~30
lines to ~5. -/

/-- For `0 ≤ r`, `Complex.arg ((r : ℝ) : ℂ) < Real.pi`. -/
private lemma arg_ofReal_lt_pi {r : ℝ} (hr : 0 ≤ r) :
    Complex.arg ((r : ℝ) : ℂ) < Real.pi := by
  rw [Complex.arg_ofReal_of_nonneg hr]; exact Real.pi_pos

/-- For `r : ℝ`, the imag part of `((r : ℝ) : ℂ)` is in `(−π, π]`. -/
private lemma ofReal_im_in_strip (r : ℝ) :
    -Real.pi < (((r : ℝ) : ℂ)).im ∧ (((r : ℝ) : ℂ)).im ≤ Real.pi := by
  rw [Complex.ofReal_im]
  exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

/-- Real-safe subtraction: subtracting two real-valued `EMLTermℂ`
evaluations gives the cast of their real difference, provided the
minuend is **strictly positive** (so `mkSubℂ`'s `arg(va) < π` and
`va ≠ 0` constraints both hold for the real cast).

The asymmetry with `eval?_mkAddℂ_ofReal` (which has no side conditions)
reflects the asymmetry of `mkSubℂ` itself: `mkSubℂ A B = exp(log A) -
log(exp B) = A - B`, and `log A` is only well-defined under
`arg A < π` strictly. For a real `a`, `arg ((a : ℝ) : ℂ) = 0` if
`a > 0`, `= π` if `a < 0`, and the macro fails on the cut. -/
lemma eval?_mkSubℂ_ofReal
    {env : Nat → ℂ} {A B : EMLTermℂ} {a b : ℝ}
    (hA : A.eval? env = some ((a : ℝ) : ℂ))
    (hB : B.eval? env = some ((b : ℝ) : ℂ))
    (ha_pos : 0 < a) :
    (mkSubℂ A B).eval? env = some (((a - b : ℝ) : ℂ)) := by
  have ⟨hb_lo, hb_hi⟩ := ofReal_im_in_strip b
  have h := eval?_mkSubℂ hA hB
              (by exact_mod_cast ha_pos.ne')
              (arg_ofReal_lt_pi ha_pos.le)
              hb_lo hb_hi
  rw [h]; push_cast; ring_nf

/-- Real-positive multiplication: `mkMulℂ` of two strictly-positive
real-valued evaluations gives the cast of their product. -/
lemma eval?_mkMulℂ_realPos
    {env : Nat → ℂ} {A B : EMLTermℂ} {a b : ℝ}
    (hA : A.eval? env = some ((a : ℝ) : ℂ))
    (hB : B.eval? env = some ((b : ℝ) : ℂ))
    (ha_pos : 0 < a) (hb_pos : 0 < b) :
    (mkMulℂ A B).eval? env = some (((a * b : ℝ) : ℂ)) := by
  have h_log_a : Complex.log ((a : ℝ) : ℂ) = ((Real.log a : ℝ) : ℂ) :=
    (Complex.ofReal_log ha_pos.le).symm
  have h_log_b : Complex.log ((b : ℝ) : ℂ) = ((Real.log b : ℝ) : ℂ) :=
    (Complex.ofReal_log hb_pos.le).symm
  have h_addsafe :
      ADDsafeℂ (Complex.log ((a : ℝ) : ℂ)) (Complex.log ((b : ℝ) : ℂ)) := by
    rw [h_log_a, h_log_b]
    exact ADDsafeℂ_ofReal_ofReal (Real.log a) (Real.log b)
  have h := eval?_mkMulℂ hA hB
              (by exact_mod_cast ha_pos.ne')
              (by exact_mod_cast hb_pos.ne')
              (arg_ofReal_lt_pi ha_pos.le)
              (arg_ofReal_lt_pi hb_pos.le)
              h_addsafe
  rw [h]; push_cast; ring_nf

/-- Real-`> 1` division: `mkDivℂ` of `a / b` where `1 < a` and `0 < b`
both real-valued. The `1 < a` hypothesis ensures `log a > 0` (so
`log a ≠ 0` AND `arg(log a) = 0 < π`), discharging two of `mkDivℂ`'s
constraints in one shot. -/
lemma eval?_mkDivℂ_realGtOne_realPos
    {env : Nat → ℂ} {A B : EMLTermℂ} {a b : ℝ}
    (hA : A.eval? env = some ((a : ℝ) : ℂ))
    (hB : B.eval? env = some ((b : ℝ) : ℂ))
    (ha_gt : 1 < a) (hb_pos : 0 < b) :
    (mkDivℂ A B).eval? env = some (((a / b : ℝ) : ℂ)) := by
  have ha_pos : 0 < a := lt_trans zero_lt_one ha_gt
  have h_log_a : Complex.log ((a : ℝ) : ℂ) = ((Real.log a : ℝ) : ℂ) :=
    (Complex.ofReal_log ha_pos.le).symm
  have h_log_b : Complex.log ((b : ℝ) : ℂ) = ((Real.log b : ℝ) : ℂ) :=
    (Complex.ofReal_log hb_pos.le).symm
  have h_loga_pos : 0 < Real.log a := Real.log_pos ha_gt
  have h_logA_ne : Complex.log ((a : ℝ) : ℂ) ≠ 0 := by
    rw [h_log_a]; exact_mod_cast h_loga_pos.ne'
  have h_logA_arg : Complex.arg (Complex.log ((a : ℝ) : ℂ)) < Real.pi := by
    rw [h_log_a]; exact arg_ofReal_lt_pi h_loga_pos.le
  have ⟨h_logB_lo, h_logB_hi⟩ : -Real.pi < (Complex.log ((b : ℝ) : ℂ)).im
                                ∧ (Complex.log ((b : ℝ) : ℂ)).im ≤ Real.pi := by
    rw [h_log_b]; exact ofReal_im_in_strip _
  have h := eval?_mkDivℂ hA hB
              (by exact_mod_cast ha_pos.ne')
              (by exact_mod_cast hb_pos.ne')
              (arg_ofReal_lt_pi ha_pos.le)
              (arg_ofReal_lt_pi hb_pos.le)
              h_logA_ne h_logA_arg h_logB_lo h_logB_hi
  rw [h]; push_cast; ring_nf

/-! ## §C′.1 — Period constants -/

/-- The complex constant `2π` as an `EMLTermℂ`, built as `mkMulℂ` of
the public `2` and `π` terms. -/
noncomputable def twoPiPubℂ : EMLTermℂ := mkMulℂ twoPubℂ piPubℂ

/-- The complex constant `−π` as an `EMLTermℂ`, built via the identity
`−π = π − 2π`. Uses `mkSubℂ` (rather than building `−π` from scratch),
which only needs `arg(π) < π` (true: `π > 0`) and `(2π).im ∈ (−π, π]`
(true: real). Avoids the `mkMulℂ` constraint pile-up that an alternate
construction `mkMulℂ negOnePubℂ piPubℂ` would face. -/
noncomputable def negPiPubℂ : EMLTermℂ := mkSubℂ piPubℂ twoPiPubℂ

/-- The complex constant `π/2` as an `EMLTermℂ`, built via `mkDivℂ` of
`piPubℂ` and `twoPubℂ`. -/
noncomputable def halfPiPubℂ : EMLTermℂ := mkDivℂ piPubℂ twoPubℂ

/-! ## §C′.2 — Substitution input for sin via cos -/

/-- The "shifted argument" for sin via cos: a term that evaluates to
`((π/2 - x : ℝ) : ℂ)` when `env 0 = ((x : ℝ) : ℂ)`. Used as the
substitution input for `cosTermℂ.subst0 halfPiMinusXℂ` to produce
`sin x` via `Real.cos_pi_div_two_sub`. -/
noncomputable def halfPiMinusXℂ : EMLTermℂ := mkSubℂ halfPiPubℂ (.var 0)

/-- Eval lemma for `twoPiPubℂ`. Golfed via `eval?_mkMulℂ_realPos` —
~30 lines collapse to 5 once the `twoPubℂ` cast `(2 : ℂ) = ((2:ℝ):ℂ)`
is in scope. -/
lemma eval?_twoPiPubℂ (env : Nat → ℂ) :
    twoPiPubℂ.eval? env = some ((2 * Real.pi : ℝ) : ℂ) := by
  unfold twoPiPubℂ
  have hT : twoPubℂ.eval? env = some (((2 : ℝ) : ℂ)) := by
    rw [eval?_twoPubℂ env]; norm_cast
  have h := eval?_mkMulℂ_realPos hT (eval?_piPubℂ env)
              (by norm_num : (0:ℝ) < 2) Real.pi_pos
  rw [h]

/-- Eval lemma for `negPiPubℂ`: evaluates to `((-Real.pi : ℝ) : ℂ)`.
Golfed via `eval?_mkSubℂ_ofReal` (3 lines vs. 18). -/
lemma eval?_negPiPubℂ (env : Nat → ℂ) :
    negPiPubℂ.eval? env = some (((-Real.pi : ℝ) : ℂ)) := by
  unfold negPiPubℂ
  have h := eval?_mkSubℂ_ofReal (eval?_piPubℂ env) (eval?_twoPiPubℂ env) Real.pi_pos
  rw [h]; congr 1; push_cast; ring

/-- Eval lemma for `halfPiPubℂ`: evaluates to `((Real.pi / 2 : ℝ) : ℂ)`.
Golfed via `eval?_mkDivℂ_realGtOne_realPos` (Real.pi > 3 > 1). -/
lemma eval?_halfPiPubℂ (env : Nat → ℂ) :
    halfPiPubℂ.eval? env = some (((Real.pi / 2 : ℝ) : ℂ)) := by
  unfold halfPiPubℂ
  have hP := eval?_piPubℂ env
  have hT : twoPubℂ.eval? env = some (((2 : ℝ) : ℂ)) := by
    rw [eval?_twoPubℂ env]; norm_cast
  have hπ_gt_one : (1 : ℝ) < Real.pi := lt_trans (by norm_num) Real.pi_gt_three
  exact eval?_mkDivℂ_realGtOne_realPos hP hT hπ_gt_one (by norm_num : (0 : ℝ) < 2)

/-- Eval lemma for `halfPiMinusXℂ`: evaluates to `((π/2 - x : ℝ) : ℂ)`
when `env 0 = ((x : ℝ) : ℂ)`.

This uses `eval?_mkSubℂ_ofReal` since both `π/2` and `x` are
real-valued (with `π/2 > 0` discharging the positivity hypothesis). -/
lemma eval?_halfPiMinusXℂ (x : ℝ) (env : Nat → ℂ)
    (henv0 : env 0 = ((x : ℝ) : ℂ)) :
    halfPiMinusXℂ.eval? env = some (((Real.pi / 2 - x : ℝ) : ℂ)) := by
  unfold halfPiMinusXℂ
  have hHalf : halfPiPubℂ.eval? env = some (((Real.pi / 2 : ℝ) : ℂ)) :=
    eval?_halfPiPubℂ env
  have hVar : (EMLTermℂ.var 0).eval? env = some ((x : ℝ) : ℂ) := by
    show some (env 0) = _; rw [henv0]
  have hHalfPos : (0 : ℝ) < Real.pi / 2 := by
    have := Real.pi_pos; linarith
  exact eval?_mkSubℂ_ofReal hHalf hVar hHalfPos

/-! ## §C′.3 — Auxiliary real-analysis lemma for arctan via arcsin

**Provenance:** sealed 2026-05-08 by Aristotle (project
`2b0e3d5d-ed06-4d73-b2ac-2b42ea8844bc`, chunk `077_atan_arg_in_ioo`).
Path C′ uses the identity `Real.arctan x = Real.arcsin (x / √(1+x²))`
plus the existing `arcsinTermℂ_open` witness on `(−1, 1)`. This lemma
proves the substitution argument always lies in `(−1, 1)`. -/

theorem atanArg_in_Ioo (x : ℝ) :
    x / Real.sqrt (1 + x^2) ∈ Set.Ioo (-1 : ℝ) 1 := by
  refine ⟨?_, ?_⟩
  · rw [lt_div_iff₀ (by positivity)]
    nlinarith [Real.sqrt_nonneg (1 + x ^ 2),
               Real.sq_sqrt (by positivity : 0 ≤ 1 + x ^ 2)]
  · rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.sqrt_nonneg (1 + x ^ 2),
               Real.sq_sqrt (by positivity : 0 ≤ 1 + x ^ 2)]

/-! ## §C′.4a — Period shifts via repeated `mkAddℂ`

Per Pro's recommendation: build period shifts by repeated addition of
fixed real period constants. Each step uses `eval?_mkAddℂ_ofReal`,
which has no side conditions when both args are real-valued. The
shifted intermediate stays real, so no `arg = π` boundary appears. -/

/-- A `k`-iteration period shift: starting from `.var 0`, apply
`mkAddℂ T negPeriod` `k` times for `k ≥ 0`, or `mkAddℂ T period`
`|k|` times for `k < 0`. The eval semantics are designed so that
`shiftByPeriodℂ period negPeriod k` evaluates to `((x − k·p : ℝ) : ℂ)`
when `period` evaluates to `((p : ℝ) : ℂ)` and `env 0 = ((x : ℝ) : ℂ)`. -/
noncomputable def shiftByPeriodℂ (period negPeriod : EMLTermℂ) : ℤ → EMLTermℂ
  | Int.ofNat n   => Nat.iterate (fun T => mkAddℂ T negPeriod) n (.var 0)
  | Int.negSucc n => Nat.iterate (fun T => mkAddℂ T period) (n + 1) (.var 0)

/-- Helper: forward iteration of `mkAddℂ _ negPeriod` evaluates to
`x − n·p`. -/
private lemma eval?_iterate_addNeg
    {env : Nat → ℂ} {negPeriod : EMLTermℂ} {p x : ℝ}
    (hnp : negPeriod.eval? env = some (((-p : ℝ) : ℂ)))
    (henv0 : env 0 = ((x : ℝ) : ℂ)) (n : ℕ) :
    (Nat.iterate (fun T => mkAddℂ T negPeriod) n (.var 0)).eval? env =
      some (((x - (n : ℝ) * p : ℝ) : ℂ)) := by
  induction n with
  | zero =>
    show (EMLTermℂ.var 0).eval? env = some (((x - (0 : ℕ) * p : ℝ) : ℂ))
    rw [EMLTermℂ.eval?_var, henv0]
    push_cast; ring_nf
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have h := eval?_mkAddℂ_ofReal ih hnp
    rw [h]
    congr 1
    push_cast; ring

/-- Helper: forward iteration of `mkAddℂ _ period` evaluates to
`x + n·p` (used for negative `k`). -/
private lemma eval?_iterate_addPos
    {env : Nat → ℂ} {period : EMLTermℂ} {p x : ℝ}
    (hp : period.eval? env = some (((p : ℝ) : ℂ)))
    (henv0 : env 0 = ((x : ℝ) : ℂ)) (n : ℕ) :
    (Nat.iterate (fun T => mkAddℂ T period) n (.var 0)).eval? env =
      some (((x + (n : ℝ) * p : ℝ) : ℂ)) := by
  induction n with
  | zero =>
    show (EMLTermℂ.var 0).eval? env = some (((x + (0 : ℕ) * p : ℝ) : ℂ))
    rw [EMLTermℂ.eval?_var, henv0]
    push_cast; ring_nf
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have h := eval?_mkAddℂ_ofReal ih hp
    rw [h]
    congr 1
    push_cast; ring

/-- **Eval lemma for `shiftByPeriodℂ`.** Given period terms evaluating
to `±p` and `env 0 = ((x : ℝ) : ℂ)`, the `k`-shift evaluates to
`((x − k·p : ℝ) : ℂ)` for any `k : ℤ`. -/
lemma eval?_shiftByPeriodℂ
    {env : Nat → ℂ} {period negPeriod : EMLTermℂ} {p x : ℝ}
    (hp : period.eval? env = some (((p : ℝ) : ℂ)))
    (hnp : negPeriod.eval? env = some (((-p : ℝ) : ℂ)))
    (henv0 : env 0 = ((x : ℝ) : ℂ)) (k : ℤ) :
    (shiftByPeriodℂ period negPeriod k).eval? env =
      some (((x - (k : ℝ) * p : ℝ) : ℂ)) := by
  cases k with
  | ofNat n =>
    show (Nat.iterate (fun T => mkAddℂ T negPeriod) n (.var 0)).eval? env = _
    rw [eval?_iterate_addNeg hnp henv0 n]
    norm_cast
  | negSucc n =>
    show (Nat.iterate (fun T => mkAddℂ T period) (n + 1) (.var 0)).eval? env = _
    rw [eval?_iterate_addPos hp henv0 (n + 1)]
    congr 1
    push_cast
    ring

/-! ## §C′.4a-bis — Unified `cos` witness family on `ℝ ∖ {0}`

Combines `cos_re_bridge` (positive side) and `cos_re_bridge_neg`
(negative side) into a single existential statement. This is exactly
the form `sin_via_cos` needs from its substituted argument: given any
`y ≠ 0`, produce *some* witness `t` whose eval projects to `Real.cos y`. -/

theorem cos_full_witness_family (x : ℝ) (hx : x ≠ 0) :
    ∃ t : EMLTermℂ, ∃ vc : ℂ,
      t.eval? (fun n => if n = 0 then ((x : ℝ) : ℂ) else 0) = some vc ∧
      vc.re = Real.cos x := by
  set env : Nat → ℂ := fun n => if n = 0 then ((x : ℝ) : ℂ) else 0 with henv_def
  have henv0 : env 0 = ((x : ℝ) : ℂ) := by simp [henv_def]
  rcases lt_or_gt_of_ne hx with hx_neg | hx_pos
  · obtain ⟨vc, hv_eval, hv_re⟩ := cos_re_bridge_neg hx_neg
    exact ⟨cosTermℂ_neg, vc, hv_eval, hv_re⟩
  · obtain ⟨v, hv_eval, hv_re⟩ := cos_re_bridge (env := env) hx_pos henv0
    exact ⟨cosTermℂ, v, hv_eval, hv_re⟩

/-! ## §C′.4b — `shiftByPiℂ` and `shiftBy2Piℂ` specializations -/

/-- Period-π shift: `shiftByPiℂ k` evaluates to `((x − k·π : ℝ) : ℂ)`
when `env 0 = ((x : ℝ) : ℂ)`. Uses `piPubℂ` and `negPiPubℂ` as the
period constants. -/
noncomputable def shiftByPiℂ : ℤ → EMLTermℂ :=
  shiftByPeriodℂ piPubℂ negPiPubℂ

/-- Eval lemma for `shiftByPiℂ`. -/
lemma eval?_shiftByPiℂ (x : ℝ) (k : ℤ) (env : Nat → ℂ)
    (henv0 : env 0 = ((x : ℝ) : ℂ)) :
    (shiftByPiℂ k).eval? env = some (((x - (k : ℝ) * Real.pi : ℝ) : ℂ)) := by
  unfold shiftByPiℂ
  exact eval?_shiftByPeriodℂ (eval?_piPubℂ env) (eval?_negPiPubℂ env) henv0 k

/-! ## §C′.4 — Period-π reduction for tan

**Provenance:** sealed 2026-05-08 by Aristotle (project
`1030d31b-81b4-48ff-bb14-16d89d4d4bff`, chunk `079_tan_period_reduction`).
Path C′ §4 (per GPT Pro): for `tan_full`, range-reduce arbitrary `x`
(with `cos x ≠ 0`) to the fundamental strip `(−π/2, π/2)` via the
nearest-integer-multiple-of-π shift `k = ⌊(x + π/2) / π⌋`. Mathlib's
`Real.tan_sub_int_mul_pi` then gives the periodicity. -/

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

end EML
