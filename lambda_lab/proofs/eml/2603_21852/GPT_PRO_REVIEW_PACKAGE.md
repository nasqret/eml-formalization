# GPT Pro review package — EML §A push (chunks 064-067 literal trig witnesses)

**Context:** Lean 4.28 + Mathlib formalization of arXiv:2603.21852, Polish GhostDay 2026 talk on Saturday. Need to maximize literal-witness coverage of paper trig primitives (`tan`, `arctan`, `arcsin`, `arccos`) by Friday EOD.

**State (2026-05-06 03:00 UTC):**
- ✅ 30 of 36 paper primitives sealed via `EML/Framework/PaperClaims.lean` umbrella
- ✅ Just landed: `paper_claim_arctan_narrow` (literal `EMLTermℂ` witness for `arctan x` with `0 < x < π`) — net **31/36**
- ✅ New combinators public in `EML/Framework/Complex/Builders/Trig.lean`: `mkAddℂ`, `mkMulℂ`, `mkSubℂ`, `mkDivℂ`, `iTermPubℂ`
- ❌ Blocked on: getting `-Complex.I` as a public `EMLTermℂ` witness; this gates chunks 064/066/067

**Goal:** Land chunks 064 (tan), 066 (arcsin), 067 (arccos) as literal witnesses by Friday. Stretch: K-counting (paper Table 4).

---

## Architecture summary

```
F36Expr            -- 36-primitive paper source language
  ↓ translate?
ELExpr             -- intermediate language
  ↓ compile (real fragment)
EMLTerm            -- {1, x, eml(x,y) = exp(x) - log(y)}, partial eval Real

Complex bridge:
F36Expr.{pi,cos,sin,arctan} → EMLTermℂ via Euler-style witnesses
EMLTermℂ partial eval: ℂ, eml(a,b) defined when b ≠ 0
```

**Public combinators on `EMLTermℂ` (just added):**
- `mkExpℂ T` — `exp(T)`
- `mkLogℂ T` — `log(T)` when `T ≠ 0` and `arg(T) < π`
- `mkAddℂ A B` — `va + vb` under `ADDsafeℂ` bundle (11 fields)
- `mkSubℂ A B` — `va - vb` under conditions
- `mkMulℂ A B` — `va * vb` (composes mkAdd of logs + mkExp)
- `mkDivℂ A B` — `va / vb` (composes mkSub of logs + mkExp)
- `iTermPubℂ` — public re-export of `realizeℂ_i.term` (= I)

**`ADDsafeℂ` precondition bundle (11 fields):**

```lean
structure ADDsafeℂ (a b : ℂ) : Prop where
  ha₁ : -π < a.im                 -- log_exp strip lower for a
  ha₂ : a.im ≤ π                  -- log_exp strip upper for a
  hema₁ : -π < (exp 1 - a).im      -- log_exp strip for (e - a)
  hema₂ : (exp 1 - a).im ≤ π
  hexpa_a_ne : exp(a) - a ≠ 0     -- inner nonzero
  hb₁ : -π < b.im                 -- log_exp strip for b
  hb₂ : b.im ≤ π
  helogexpa₁ : -π < (exp 1 - log(exp(a) - a)).im
  helogexpa₂ : (exp 1 - log(exp(a) - a)).im ≤ π
  hexp_a_a_b₁ : -π < (exp(a) - a - b).im
  hexp_a_a_b₂ : (exp(a) - a - b).im ≤ π
```

The `helogexpa` field is the workhorse — every use of `mkAddℂ` requires showing the imaginary part of `exp(1) - log(exp(a) - a)` lies in the strip `(-π, π]`.

---

## Hardest parts (in priority order)

### Hard problem #1 — Public `-i` witness (BLOCKING)

**Want:** A `noncomputable def negIPubℂ : EMLTermℂ` with proven `negIPubℂ.eval? env = some (-Complex.I)`.

**Why blocked:**
- `EML.EMLRealizationℂ.realizeℂ_i` exists in `Closures/Constants.lean` — gives `i_term` for `i`.
- There is **no** corresponding `realizeℂ_negI` for `-i`.
- The closures file has `private def NegIℂ : EMLTermℂ := ExpTℂ Halveℂ` where `Halveℂ` evals to `-π/2 · I` and `ExpTℂ` is `eml(_, .one)` for exp. So `NegIℂ.eval = exp(-iπ/2) = -i`. But it's **private**.
- Direct combinator routes fail at the `arg = π` branch cut:
  - `i * i * i = -i` fails because middle value `i*i = -1` has `arg(-1) = π`, breaking `mkMulℂ`'s `arg < π` precondition.
  - `mkSubℂ ZtPub iTermPubℂ` (= `0 - i`) fails because `mkSubℂ` requires `va ≠ 0`.
  - `mkLogℂ NegOnePubℂ` fails (would give `iπ`) because `arg(-1) = π` blocks `mkLogℂ`.

**Question for GPT Pro:** What is the cleanest path to expose `-i` as a public `EMLTermℂ` witness?

Options I see:
- (A) **Edit `Closures/Constants.lean`** to add a `realizeℂ_negI` next to `realizeℂ_i`, leveraging the existing private `NegIℂ`. Risk: smallest, but touches a sealed file.
- (B) **Build `negIPubℂ` from scratch** using only public operators. Need a non-branch-cut path; perhaps via `mkExpℂ (mkSubℂ (mkLogℂ iTermPubℂ) (mkMulℂ piTerm iTermPubℂ))`? Need to verify the algebra: `exp(log i - π·i) = exp(iπ/2 - iπ) = exp(-iπ/2) = -i`. But `π·i` has arg = π/2 OK, so `mkLogℂ` of it is OK. Need to check ADDsafeℂ for the inner sub.
- (C) **Add a `mkNegℂ` combinator** with custom architecture that handles the negation specifically, perhaps via `mkSubℂ Zt-Workaround T` or via direct exponentiation.

Please rank (A)/(B)/(C) by line cost and diagnose any branch-cut traps in (B) before I commit.

### Hard problem #2 — Tan witness using `mkDivℂ`

**Recipe:** `Real.tan x = (sin x : ℂ).re / (cos x : ℂ).re` for `x ∈ (0, π/2)`.

**Witness candidate (uses `-i`):**
```lean
tanTermℂ := mkDivℂ
  (mkSubℂ (mkExpℂ Iz) (mkExpℂ negIz))                -- numerator: e^{ix} - e^{-ix} = 2i sin x
  (mkMulℂ iTermPubℂ                                    -- denominator: i(e^{ix} + e^{-ix}) = 2i cos x
    (mkAddℂ (mkExpℂ Iz) (mkExpℂ negIz)))
where
  Iz    := mkMulℂ iTermPubℂ (.var 0)
  negIz := mkMulℂ negIPubℂ (.var 0)
```

Both terms are purely imaginary for real `x`, so the ratio is real and equals `tan x`.

**Side conditions to discharge:**
- `iTermPubℂ.eval ≠ 0`, `arg(i) = π/2 < π` ✓
- `negIPubℂ.eval ≠ 0`, `arg(-i) = -π/2 < π` ✓
- For `mkMulℂ iTermPubℂ var` (giving `iz`): `var = (x:ℂ)` for `x > 0`, so `arg(x) = 0 < π`. `ADDsafeℂ(log i, log x)` ← already proven (`addsafe_logI_logX`).
- Symmetric `ADDsafeℂ(log (-i), log x)` ← need to prove (analogous, but with `log(-i) = -iπ/2`).
- For `mkExpℂ Iz` (giving `e^{iz}`): unconditional (mkExpℂ has no preconditions). ✓
- For `mkSubℂ (e^{iz}) (e^{-iz})`: `e^{iz} ≠ 0`, `arg(e^{iz}) < π` (need `x ∈ (0, π/2)` to ensure arg ≠ π), `e^{-iz}.im ∈ (-π, π]` (= `-sin x · 1`, need `|sin x| ≤ π` always true).
- For `mkAddℂ (e^{iz}) (e^{-iz})`: ADDsafeℂ for `(e^{iz}, e^{-iz})` — non-trivial, need to compute imag parts and helogexpa.
- For `mkMulℂ iTerm (e^{iz} + e^{-iz})`: ADDsafeℂ for `(log i, log(2 cos x))` — `log(2 cos x)` is real (positive real), so ADDsafe should hold for `x` in some interior interval.
- For `mkDivℂ num denom`: arg(numerator) < π, arg(denominator) < π, `log num` and `log denom` `≠ 0` and `< π` and im in strip.

**Estimated effort:** ~800 lines of side-condition discharge analogous to `addsafe_logI_logX` and `addsafe_one_iX` already shipped.

**Question for GPT Pro:** Are there algebraic simplifications that would shortcut the proof? Specifically:
- (1) Is there a Mathlib lemma proving directly `(exp(I*x) + exp(-I*x)).arg < π` for some explicit interval of real `x`?
- (2) Could we `unfold` once and rely on `simp_arith` or `nlinarith` with `Real.cos_pos_of_mem_Ioo` to crush all 11 ADDsafeℂ fields in a few tactic lines?
- (3) Is there a more efficient witness recipe for `tan` (perhaps using `cos(2x) - 1 = -2 sin²x` so we can avoid `i` in the denominator)?

### Hard problem #3 — `mkSqrtℂ` for arcsin/arccos

**Need:** For chunks 066 (arcsin) and 067 (arccos), the closed-form identities require `√(1 - x²)` as an `EMLTermℂ` value.

**Mathematical recipe:** `√z = exp(½ log z)`.

**Lean recipe:** `mkSqrtℂ T := mkExpℂ (mkHalveℂ (mkLogℂ T))` — but `mkHalveℂ` doesn't exist publicly.

**Building blocks:**
- For `T.eval = 1 - x² > 0` (real positive when `|x| < 1`): `mkLogℂ T` gives `(Real.log(1-x²) : ℂ)`, then need to halve it.
- Halving `(c : ℂ) ↦ c / 2`. We have `mkDivℂ` now, but it requires `b = 2 : ℂ` as an `EMLTermℂ`. We have `realizeℂ_pi.term` and `realizeℂ_i.term` but no `realizeℂ_two`.
- Or directly: `mkExpℂ (mkSubℂ (mkLogℂ Z) (mkLogℂ TwoTerm))` — gives `exp(log Z - log 2) = Z/2`.

**Question for GPT Pro:** What's the cleanest path to expose `2` as a public `EMLTermℂ` witness? Same architecture question as `-i`. And does Mathlib have a direct `Complex.sqrt_eq_rpow` or similar that could shortcut the half-log-exp pattern?

### Hard problem #4 — Domain widening for arctan

**Current:** `paper_claim_arctan_narrow` works for `0 < x < π`.

**Paper claim:** `arctan` for all reals.

**Issue:** `mkMulℂ iTermPubℂ var` requires `var = (x:ℝ):ℂ ≠ 0`, blocking `x = 0`. And `mkAddℂ 1 (i·x)` needs `(i·x).im ∈ (-π, π]`, blocking `x ≥ π`.

**Workaround sketches:**
- `x = 0` boundary: separate witness (constant `0` term, since `arctan 0 = 0`). Then unite via cases.
- `x > π` (or general `|x| > 1`): `arctan(x) = π/2 - arctan(1/x)` for `x > 0`. Requires inverting `x` (we have `mkInv` but only for nonzero), then composing.
- Negative `x`: `arctan(-x) = -arctan(x)`, plus negation.

**Question for GPT Pro:** What's the cleanest architecture for piecewise paper claims (i.e., a single `theorem paper_claim_arctan` that works for all reals via case analysis)? Should we expose multiple witness terms per primitive (one per regime) or build a single ifte-style term?

### Hard problem #5 — `helogexpa` field automation

The `helogexpa` field of `ADDsafeℂ` requires showing `(exp 1 - log(exp(a) - a)).im ∈ (-π, π]`. For each `a`, this requires:
1. Compute `exp(a) - a` as a specific complex value.
2. Take `Complex.log` of that value (which involves `arg`).
3. Show the imaginary part of `e - log(...)` is in the strip.

For `a = log I = iπ/2`, we got `exp(a) - a = i(1 - π/2) ≈ -0.57 i` (negative imag axis), `log = log(π/2 - 1) - iπ/2`, and `(e - log).im = π/2`.

**Question for GPT Pro:** Is there a Mathlib API or a `decide`-style tactic that could automate this for the values we'll encounter (logs of `i`, `-i`, positive reals, sums thereof)? The pattern is very repetitive across chunks.

---

## What we want from GPT Pro

1. **Diagnose hard problem #1** (public `-i` witness). Recommend (A), (B), or (C) with line-budget estimates and any gotchas.
2. **For hard problem #2 (tan witness),** suggest 1-3 algebraic shortcuts that would compress the ADDsafeℂ discharge.
3. **For hard problem #3 (mkSqrtℂ),** suggest the cleanest path including `2` as a public witness.
4. **For hard problem #4 (domain widening),** suggest architecture pattern (case-split vs piecewise terms).
5. **For hard problem #5 (helogexpa automation),** look for a `Complex.arg` characterization lemma or a tactic combination that handles the recurring pattern.
6. **Overall priority advice:** given Friday EOD deadline, which 2-3 of chunks 064/066/067 are most realistic? Should we lean into universal arctan widening (#4) instead of new chunks?

## Files to inspect (give Pro full read access)

- `EML/Framework/Complex/Builders/Trig.lean` (NEW, ~470 lines, our work-in-progress)
- `EML/Framework/Complex/Closures/Trig.lean` (957 lines, existing private scaffolding)
- `EML/Framework/Complex/Closures/Constants.lean` (622 lines, has `realizeℂ_pi` + `realizeℂ_i`)
- `EML/Framework/Complex/Term.lean` (`EMLTermℂ` + `eval?` definition)
- `EML/Framework/Complex/Realization.lean` (`EMLRealizationℂ` structure)
- `EML/Framework/PaperClaims.lean` (talk's public API)
- `EML/Solutions/064_emlterm_for_tan_x.lean` (current closed-form-only chunk)
- `EML/Solutions/065_emlterm_for_arctan_x.lean` (similar)
- `EML/Solutions/066_emlterm_for_arcsin_x.lean` (similar; says literal witness "is false" — disagree)
- `EML/Solutions/067_emlterm_for_arccos_x.lean` (similar)

Repo: workdir at `/Users/airbartek/claude/falenty_2026/lambda_lab/proofs/eml/2603_21852/lean_workspace/`

Build: `lake build` from workspace root. All currently passing 8 048 jobs sorry-free.

Eagle (PCSS): SLURM `verify_all.sbatch` at `/mnt/storage_5/scratch/pl0414-02/`. Last clean re-verify: job 7037030.

## Talk-day deadline

**Saturday 2026-05-09** GhostDay conference. Ideal scoreboard: **34 / 36** (close 064 + 066 + 067 + arctan-domain widening to all reals). Realistic floor: **31 / 36** + scaffolding for future closure (current state).
