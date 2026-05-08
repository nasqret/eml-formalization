# Plan C implementation spec — full-real-domain trig via periodicity

> Implementation companion for `Subst.lean`. Specifies the exact Lean
> constructions and proof obligations needed to extend `sinTermℂ`,
> `arctanTermℂ`, and `tanCoreTermℂ` to all of ℝ (modulo isolated
> singularities for `tan`).

## Status

- ✅ **Foundation:** `EMLTermℂ.subst0` + `eval?_subst0` (in `Subst.lean`)
- ⏳ **Pending:** shift terms, periodicity lemmas, witness families
- ⏳ **Gating:** [GPT Pro consult](../../../../../../../gpt_pro_bundle/trig_widening/) — Pro's recommendation between Path A (boundary lemmas) and Path C (this spec) sets the priority

## Architecture

For each narrow trig primitive, extend the witness from its current
domain `D ⊊ ℝ` to all of `ℝ ∖ S` (where `S` is the set of isolated
singularities, e.g. `S = πℤ ∖ {0}` for sin's zeros, or `S = π/2 + πℤ`
for tan's poles).

The witness becomes a **family** indexed by an integer `k(x)`:

```
∀ x ∈ ℝ ∖ S,  ∃ t : EMLTermℂ,  ∃ vc : ℂ,
    t.eval? env_x = some vc  ∧  vc.<projection> = Real.<f> x
```

For each `k : ℤ`, the witness `t_k = (base_witness).subst0 shift_kℂ`
where:
- `base_witness` is the existing narrow witness (works on the
  fundamental domain, e.g. `(−π, π) ∖ {0}` for `sin`)
- `shift_kℂ : EMLTermℂ` is a complex term whose evaluation at `x` is
  `((x − 2πk : ℝ) : ℂ)` for `sin`/`cos`/`arctan` (period `2π` for
  the first two, period `π` for the last two by halving), or
  `((x − πk : ℝ) : ℂ)` for `tan` (period `π`)

The choice of `k` for a given `x`: `k(x) := round(x / (2π))` for
`sin`/`cos`, `k(x) := round(x / π)` for `tan`.

## Concrete Lean: shift term

The 2π shift term has two variants depending on the sign of `k`:

```lean
import EML.Framework.Complex.Subst
import EML.Framework.Complex.Builders.Trig
import EML.Framework.Complex.Closures.Constants

namespace EML
open Complex

/-- The complex constant `2π` as an `EMLTermℂ`. K-count: ~510. -/
noncomputable def twoPiPubℂ : EMLTermℂ := mkMulℂ twoPubℂ piPubℂ

lemma eval?_twoPiPubℂ (env : Nat → ℂ) :
    twoPiPubℂ.eval? env = some ((2 * Real.pi : ℝ) : ℂ) := by
  -- arg(twoPubℂ) = 0, arg(piPubℂ) = 0; both positive reals.
  -- ADDsafeℂ on log(2) + log(π) is straightforward (both are real).
  unfold twoPiPubℂ
  have hT : twoPubℂ.eval? env = some (2 : ℂ) := eval?_twoPubℂ env
  have hP : piPubℂ.eval? env = some ((Real.pi : ℝ) : ℂ) := eval?_piPubℂ env
  apply eval?_mkMulℂ hT hP (by norm_num) ?_
    (?_ : Complex.arg (2 : ℂ) < Real.pi)
    (?_ : Complex.arg ((Real.pi : ℝ) : ℂ) < Real.pi)
    (?_ : ADDsafeℂ (Complex.log 2) (Complex.log ((Real.pi : ℝ) : ℂ)))
  · -- π ≠ 0
    exact_mod_cast Real.pi_ne_zero
  · -- arg(2) < π
    rw [show (2 : ℂ) = (((2 : ℝ)) : ℂ) from by push_cast; rfl,
        Complex.arg_ofReal_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.pi_pos
  · -- arg(π) < π
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
    exact Real.pi_pos
  · -- ADDsafeℂ on log(2), log(π) — both are positive reals so logs are real
    -- (im components are 0)
    refine { ha₁ := ?_, ha₂ := ?_, hema₁ := ?_, hema₂ := ?_,
             hexpa_a_ne := ?_, hb₁ := ?_, hb₂ := ?_,
             helogexpa₁ := ?_, helogexpa₂ := ?_,
             hexp_a_a_b₁ := ?_, hexp_a_a_b₂ := ?_ }
    -- All conditions reduce to im = 0 inequalities; discharge with linarith [Real.pi_pos]
    sorry  -- mechanical; ~30 lines of im-component computations
  -- Then convert (2 : ℂ) * ((Real.pi : ℝ) : ℂ) = ((2 * Real.pi : ℝ) : ℂ)
  -- via push_cast.

/-- Shift term for `+2π`: evaluates to `((x − 2π : ℝ) : ℂ)` when
`env 0 = ((x : ℝ) : ℂ)` AND `0 < x` (so `arg(var 0) < π`). -/
noncomputable def shiftSub2πℂ : EMLTermℂ :=
  mkSubℂ (.var 0) twoPiPubℂ

lemma eval?_shiftSub2πℂ {x : ℝ} (hx_pos : 0 < x) :
    shiftSub2πℂ.eval?
        (fun n => if n = 0 then ((x : ℝ) : ℂ) else 0) =
      some (((x - 2 * Real.pi : ℝ) : ℂ)) := by
  unfold shiftSub2πℂ
  set env := fun n : ℕ => if n = 0 then ((x : ℝ) : ℂ) else 0
  have hVar : (EMLTermℂ.var 0).eval? env = some ((x : ℝ) : ℂ) := by
    show some (env 0) = _; simp [env]
  have hTwoPi : twoPiPubℂ.eval? env = some ((2 * Real.pi : ℝ) : ℂ) :=
    eval?_twoPiPubℂ env
  -- mkSubℂ requires:
  --   var 0 ≠ 0 → x ≠ 0  (from hx_pos)
  --   arg(var 0) < π → x > 0  (from hx_pos: real positive has arg = 0)
  --   (2π : ℂ).im ∈ (−π, π]  → 0 ∈ (−π, π]
  have hX_ne : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx_pos.ne'
  have hX_arg : Complex.arg ((x : ℝ) : ℂ) < Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx_pos.le]; exact Real.pi_pos
  have h2πim_lo : -Real.pi < (((2 * Real.pi : ℝ) : ℂ)).im := by
    simp; linarith [Real.pi_pos]
  have h2πim_hi : (((2 * Real.pi : ℝ) : ℂ)).im ≤ Real.pi := by
    simp
  have h := eval?_mkSubℂ hVar hTwoPi hX_ne hX_arg h2πim_lo h2πim_hi
  rw [h]
  push_cast
  ring_nf

/-- Mirror shift for `−2π`: evaluates to `((x + 2π : ℝ) : ℂ)`. Used for
the negative-x extension. -/
noncomputable def shiftAdd2πℂ : EMLTermℂ :=
  mkAddℂ (.var 0) twoPiPubℂ

lemma eval?_shiftAdd2πℂ {x : ℝ} (hx_im_bound : ...) :
    shiftAdd2πℂ.eval?
        (fun n => if n = 0 then ((x : ℝ) : ℂ) else 0) =
      some (((x + 2 * Real.pi : ℝ) : ℂ)) := by
  -- mkAddℂ requires the full ADDsafeℂ bundle on (var 0).eval and twoPiPubℂ.eval.
  -- For real x: (var 0).eval = ((x : ℝ) : ℂ).im = 0, and similar for 2π.
  -- Most of ADDsafeℂ's conditions are about exp(...) computations whose im
  -- components are bounded by ±π. For real-valued inputs, these reduce to
  -- conditions on x's magnitude (we need exp(x) - x's im to be in bounds, etc.)
  sorry  -- mechanical but ~40 lines

end EML
```

## Witness family theorem (sin case)

```lean
/-- The fundamental-domain `sin` witness — already in `Closures/Trig.lean`. -/
-- existing: paper_claim_sin : ∃ t, ∀ x ∈ (0, π), ∃ vc, ...
-- existing: paper_claim_sin_neg : ∃ t, ∀ x ∈ (−π, 0), ∃ vc, ...
-- existing: paper_claim_sin_zero : ∀ env, sinAtZeroℂ.eval? env = some 0

/-- Period-shifted sin witness for shift `+2π` (i.e., x ∈ (π, 3π)).
Constructed by substituting `var 0` in the existing `sinTermℂ` (which
works on `(0, π)`) with the shift term `shiftSub2πℂ`. -/
noncomputable def sinTermℂ_shift_pos1 : EMLTermℂ :=
  sinTermℂ.subst0 shiftSub2πℂ

theorem sin_witness_shift_pos1 {x : ℝ} (hx_lo : Real.pi < x) (hx_hi : x < 3 * Real.pi)
    (hx_ne : x ≠ 2 * Real.pi) :
    ∃ vc : ℂ,
      sinTermℂ_shift_pos1.eval?
          (fun n => if n = 0 then ((x : ℝ) : ℂ) else 0) = some vc ∧
      vc.re = Real.sin x := by
  -- Step 1: x - 2π ∈ (−π, π) ∖ {0} (from hypotheses).
  have h_shift_lo : -Real.pi < x - 2 * Real.pi := by linarith
  have h_shift_hi : x - 2 * Real.pi < Real.pi := by linarith
  have h_shift_ne : x - 2 * Real.pi ≠ 0 := by linarith [hx_ne]
  -- Step 2: shiftSub2πℂ evaluates to (x - 2π : ℂ).
  have h_shift_eval := eval?_shiftSub2πℂ (by linarith : 0 < x)
  -- Step 3: by eval?_subst0, sinTermℂ_shift_pos1.eval? env = sinTermℂ.eval? env_shifted
  -- where env_shifted 0 = ((x - 2π : ℝ) : ℂ).
  rw [eval?_subst0_some_iff h_shift_eval]
  -- Step 4: apply existing sin witness for x - 2π ∈ (−π, π) ∖ {0}.
  -- This case-splits on whether x - 2π ∈ (0, π) (use sinTermℂ + paper_claim_sin)
  -- or x - 2π ∈ (−π, 0) (use sinTermℂ_neg + paper_claim_sin_neg).
  -- Then conclude vc.re = Real.sin (x - 2π) = Real.sin x via Real.sin_periodic.
  sorry  -- ~30 lines: case split + existing witness application + Real.sin_periodic

/-- General witness family covering all of ℝ ∖ (sin's zeros). -/
theorem sin_witness_family {x : ℝ} (hx_ne_zero : x ≠ 0)
    (hx_ne_period : ∀ k : ℤ, x ≠ 2 * Real.pi * k) :
    ∃ t : EMLTermℂ, ∃ vc : ℂ,
      t.eval? (fun n => if n = 0 then ((x : ℝ) : ℂ) else 0) = some vc ∧
      vc.re = Real.sin x := by
  -- Strategy: case-split on k = ⌊x / (2π) + 1/2⌋ : ℤ.
  -- For k = 0: x ∈ (−π, π) ∖ {0}; use existing sinTermℂ or sinTermℂ_neg.
  -- For k = 1: x ∈ (π, 3π) ∖ {2π}; use sinTermℂ_shift_pos1.
  -- For k = -1: x ∈ (−3π, −π) ∖ {−2π}; use sinTermℂ_shift_neg1 (similar construction
  --   with shiftAdd2πℂ).
  -- For |k| > 1: recurse / iterate the shift.
  sorry  -- ~80 lines: case analysis on k, individual witness applications
```

## Mathlib facts to use

| Lemma | Statement |
|---|---|
| `Real.sin_periodic` | `Function.Periodic Real.sin (2 * π)` — use as `Real.sin_periodic.sub_int_mul k x` for the shift step |
| `Real.cos_periodic` | `Function.Periodic Real.cos (2 * π)` |
| `Real.tan_periodic` | `Function.Periodic Real.tan π` |
| `Real.arctan_eq_arctan_add_pi_of_neg`? | for arctan domain handling — actually arctan has domain ℝ in Mathlib but our witness is narrowly `(−π, π) ∖ {0}` due to `arg` constraints, not arctan's intrinsic domain |
| `Int.floor_div`, `Int.fract` | for the `k = round(x / 2π)` index extraction |

## Implementation order (recommended)

1. **First lemma:** `eval?_twoPiPubℂ` — proves the basic `2π` constant.
   Estimated ~50 lines (the ADDsafeℂ bundle for `log 2 + log π` is the
   main work; both are real so the `.im = 0` lemmas should chain).
2. **Second lemma:** `eval?_shiftSub2πℂ` — assembling `mkSubℂ (var 0)
   twoPiPubℂ`. Estimated ~30 lines.
3. **Third lemma:** `eval?_shiftAdd2πℂ` — same for `+2π`. Estimated
   ~40 lines (mkAddℂ has the ADDsafeℂ bundle, which is gnarlier than
   mkSubℂ's preconditions).
4. **First witness family element:** `sin_witness_shift_pos1` — single
   shift, single primitive. Estimated ~30 lines (mostly application of
   existing lemmas + `Real.sin_periodic`).
5. **General case:** `sin_witness_family` quantifying over `k : ℤ`.
   Estimated ~80 lines for the case analysis. Recursive structure to
   handle `|k| > 1` cleanly.
6. **Companions for cos, arctan, tan:** ~30–50 lines each, mostly
   replays.

**Total estimate.** 5–7 days of focused proof work, assuming the
foundation (this file's `Subst.lean` + `Periodicity.lean` skeleton) is
in place.

## Open question

The `mkAddℂ` ADDsafeℂ bundle (8 conditions) for `var 0 + 2π` requires
showing things like `(exp(x) - x).im = 0` and `(exp(x) - x - 2π).im = 0`,
which are trivially zero for real `x` but we need to actually prove
each of the 8 inequalities. **Is there a shortcut for ADDsafeℂ when
both arguments are real-valued?** A predicate

```lean
def isReal (z : ℂ) : Prop := z.im = 0
```

with a lemma `ADDsafeℂ_of_real : isReal a → isReal b → ... → ADDsafeℂ a b`?
This would compress the boilerplate dramatically. **Worth investigating
in the next session.**
