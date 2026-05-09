# GPT Pro response — full-real-domain trig

> Received 2026-05-08. Verbatim transcription with citation links
> preserved. Path-of-record below: **Path C′** (range-reduction by
> substitution + `cos`/`arcsin` reuse).

## Headline recommendation

Use **Path C′: range-reduction by substitution**, not boundary
propagation: prove one small real-safe addition/shift layer, use
**`cosTermℂ` to get full-real `sin`**, use **`Real.arctan_eq_arcsin`
for full-real `arctan`**, and use periodic substitution only for
`tan`.

## Why this beats A and B

Path A is the wrong center of gravity. Mathlib does have the right
general branch-jump facts — `Complex.log_exp_eq_sub_toIocDiv` and
`Complex.log_exp_exists` — so if you must track sheets, do it modulo
`2πi`, not by hand-specializing every `arg = π` case. But that still
turns every builder proof into a branch-accounting proof. Your
`mkAddℂ` is already the gnarliest macro; making it sheet-parametric
will infect `mkMulℂ`, `mkDivℂ`, and every trig proof. That is a lot
of proof debt for a phenomenon you can mostly avoid. Mathlib's
complex log docs confirm exactly this principal-branch model and
expose the generalized branch-shift lemmas, but they do not give you
a ready-made compositional "branch monad" for EML trees.[^1]

Path B is mostly a dead end, except for `sin`. The only clean
`mkExpℂ`-outer trick is already sitting in your artefact: `cosTermℂ`
computes `exp (i*x)` on the full real axis except input `0`, so
`sin x = cos (π/2 - x)` gives a full-real `sin` witness by
substitution, with only the isolated point `x = π/2` needing the
constant-one witness. For `tan`, the Cayley formula is still
quotient-shaped; for `arctan`, any Euler/log formula reintroduces the
same branch issue. A genuine "single outer exp" formula for exact
`tan` or `arctan` would amount to smuggling in `log tan` or inverse
trig data.

So I recommend **C, but generalized as a regional/range-reduction
framework**. This matches what your code already does with
positive/negative companion witnesses. It is also philosophically
consistent with the paper's own implementation discussion: the paper
says EML expressions use the principal branch internally, notes the
negative-real-axis jump, and says the compiler manually corrects
signs rather than relying on the raw principal-branch formula
everywhere.[^2]

## Concrete proof sketches

### 1. Real-safe addition: the key lemma for shift terms

Do **not** build `x - 2πk` as `mkMulℂ (intToTerm k) piPubℂ`. That
routes through complex logarithmic multiplication and reopens the
boundary problem. Build shifts by repeated addition of fixed real
constants `±period`.

The lemma you want first is:

```lean
lemma ADDsafeℂ_ofReal_ofReal (a b : ℝ) :
    ADDsafeℂ ((a : ℝ) : ℂ) ((b : ℝ) : ℂ) := by
  -- All imaginary-part side conditions become `0`, hence `simp`/`linarith`.
  -- Main nonzero obligation:
  --   Complex.exp (a : ℂ) - (a : ℂ) ≠ 0
  have hpos : 0 < Real.exp a - a := by
    have h := Real.add_one_le_exp a
    nlinarith
  -- Also use that log of a positive real has imaginary part 0.
  -- Complex.exp ((a:ℝ):ℂ) = (Real.exp a : ℂ)
  -- Complex.log ((Real.exp a - a : ℝ):ℂ) has im = 0.
  constructor <;> simp [hpos.ne']
```

Then package it:

```lean
lemma eval?_mkAddℂ_ofReal
    {env : Nat → ℂ} {A B : EMLTermℂ} {a b : ℝ}
    (hA : A.eval? env = some ((a : ℝ) : ℂ))
    (hB : B.eval? env = some ((b : ℝ) : ℂ)) :
    (mkAddℂ A B).eval? env = some (((a + b : ℝ) : ℂ)) := by
  simpa [Complex.ofReal_add] using
    eval?_mkAddℂ hA hB (ADDsafeℂ_ofReal_ofReal a b)
```

Now define period shifts recursively:

```lean
noncomputable def shiftByPeriodℂ
    (period negPeriod : EMLTermℂ) : ℤ → EMLTermℂ
  | Int.ofNat n =>
      Nat.iterate (fun T => mkAddℂ T negPeriod) n (.var 0)
  | Int.negSucc n =>
      Nat.iterate (fun T => mkAddℂ T period) (n + 1) (.var 0)
```

with the proof shape:

```lean
lemma eval?_shiftByPeriodℂ
    {env : Nat → ℂ} {period negPeriod : EMLTermℂ}
    {p x : ℝ} (hp : period.eval? env = some ((p : ℝ) : ℂ))
    (hnp : negPeriod.eval? env = some (((-p : ℝ) : ℂ)))
    (hx : env 0 = ((x : ℝ) : ℂ)) :
    ∀ k : ℤ,
      (shiftByPeriodℂ period negPeriod k).eval? env =
        some (((x - (k : ℝ) * p : ℝ) : ℂ)) := by
  intro k
  cases k using Int.induction_on <;>
    -- induction over repeated `mkAddℂ`; each step is `eval?_mkAddℂ_ofReal`;
    -- final arithmetic is `ring`.
    sorry
```

This is the most important engineering move in Path C: period/range
shifts stay in the real fragment, so no `arg = π` proof ever appears.

### 2. `sin`: skip periodicity first; reuse full-real `cos`

Define a fixed shifted input term:

```lean
noncomputable def halfPiMinusXℂ : EMLTermℂ :=
  mkSubℂ halfPiPubℂ (.var 0)

noncomputable def sinViaCosℂ : EMLTermℂ :=
  cosTermℂ.subst0 halfPiMinusXℂ
```

Proof sketch:

```lean
lemma eval?_halfPiMinusXℂ (x : ℝ) :
    halfPiMinusXℂ.eval? env_x =
      some (((Real.pi / 2 - x : ℝ) : ℂ)) := by
  -- `mkSubℂ A B` is safe:
  -- A = π/2 is positive, nonzero, arg < π.
  -- B = x has imaginary part 0, so `log_exp` is in the principal strip.
  sorry

lemma sinViaCos_correct {x : ℝ} (hx : x ≠ Real.pi / 2) :
    ∃ vc : ℂ,
      sinViaCosℂ.eval? env_x = some vc ∧
      vc.re = Real.sin x := by
  have hs := eval?_halfPiMinusXℂ x
  rw [EMLTermℂ.eval?_subst0 hs cosTermℂ]
  have hcos := cosTermℂ_correct_full (Real.pi / 2 - x) (by linarith)
  -- hcos gives real part `Real.cos (π/2 - x)`.
  -- Finish with `Real.cos_pi_div_two_sub` / equivalent simp lemma.
  simpa [Real.cos_pi_div_two_sub] using hcos
```

At the isolated point:

```lean
lemma sinViaCos_at_halfPi :
    ∃ t vc,
      t.eval? env_halfPi = some vc ∧ vc.re = Real.sin (Real.pi / 2) := by
  refine ⟨.one, 1, ?_, ?_⟩
  · simp [EMLTermℂ.eval?]
  · simp [Real.sin_pi_div_two]
```

This gives better coverage than your current `sinTermℂ` and avoids
both Path A and periodic machinery.

### 3. `arctan`: use `arcsin`, not the complex-log arctan formula

Mathlib already has the exact identity:

```lean
Real.arctan x = Real.arcsin (x / Real.sqrt (1 + x ^ 2))
```

as `Real.arctan_eq_arcsin`.[^3]

So define a real-fragment term for

```lean
atanArg x = x / sqrt (1 + x^2)
```

then substitute it into the already-full-domain `arcsin` witness.

```lean
noncomputable def atanArgℂ : EMLTermℂ :=
  -- Prefer: compile the EL/F36 real expression
  --   x / sqrt (1 + x^2)
  -- and lift to ℂ.
  atanArgCompiledTerm

noncomputable def arctanViaArcsinℂ : EMLTermℂ :=
  arcsinTermℂ.subst0 atanArgℂ
```

The two hard lemmas are standard:

```lean
lemma atanArg_mem_Ioo (x : ℝ) :
    x / Real.sqrt (1 + x^2) ∈ Set.Ioo (-1 : ℝ) 1 := by
  -- prove `|x| < sqrt (1+x^2)`
  have hpos : 0 < Real.sqrt (1 + x^2) := by positivity
  have hlt : |x| < Real.sqrt (1 + x^2) := by
    -- square both sides:
    -- |x|^2 = x^2 < 1 + x^2
    sorry
  constructor <;> nlinarith [abs_lt.mp hlt |>.1, abs_lt.mp hlt |>.2, hpos]

lemma arctanViaArcsin_correct (x : ℝ) :
    ∃ vc : ℂ,
      arctanViaArcsinℂ.eval? env_x = some vc ∧
      vc.re = Real.arctan x := by
  have hArgEval :
      atanArgℂ.eval? env_x =
        some (((x / Real.sqrt (1 + x^2) : ℝ) : ℂ)) := by
    -- from the compiled real-fragment correctness theorem
    sorry
  rw [EMLTermℂ.eval?_subst0 hArgEval arcsinTermℂ]
  have hAsin := arcsinTermℂ_correct (atanArg_mem_Ioo x)
  -- hAsin gives `vc.re = Real.arcsin atanArg`.
  -- Rewrite with `Real.arctan_eq_arcsin`.
  simpa [Real.arctan_eq_arcsin] using hAsin
```

This should replace the current `mkLogℂ (1 + i*x)` arctan witness for
the full-real theorem. It avoids constructing `1 + i*x`, whose
imaginary part leaves the `mkAddℂ` strip.

### 4. `tan`: use true Path C periodic substitution

For `tan`, keep the existing local positive/negative Cayley witnesses
and range-reduce by period `π`. Mathlib has `Real.tan_periodic` and
concrete lemmas like `Real.tan_sub_int_mul_pi`.[^4]

The theorem shape should be:

```lean
theorem tan_full :
    ∀ x : ℝ, Real.cos x ≠ 0 →
      ∃ t vc,
        t.eval? env_x = some vc ∧
        vc.im = Real.tan x := by
  intro x hxcos
  obtain ⟨k, hylo, hyhi, hydef⟩ := reduce_mod_pi_to_Ioo x hxcos
  let s := shiftByPeriodℂ piPubℂ negPiPubℂ k
  have hs : s.eval? env_x =
      some (((x - (k : ℝ) * Real.pi : ℝ) : ℂ)) :=
    eval?_shiftByPeriodℂ ...
  by_cases hzero : x - (k : ℝ) * Real.pi = 0
  · -- constant-zero witness; `tan (x - kπ) = 0`, then periodicity.
    exact zero_tan_witness ...
  · cases lt_or_gt_of_ne hzero with
    | inl hyneg =>
        refine ⟨tanCoreTermℂ_neg.subst0 s, ?_⟩
        rw [EMLTermℂ.eval?_subst0 hs tanCoreTermℂ_neg]
        -- local negative theorem plus `Real.tan_sub_int_mul_pi`
        sorry
    | inr hypos =>
        refine ⟨tanCoreTermℂ.subst0 s, ?_⟩
        rw [EMLTermℂ.eval?_subst0 hs tanCoreTermℂ]
        -- local positive theorem plus `Real.tan_sub_int_mul_pi`
        sorry
```

I would state the domain as `Real.cos x ≠ 0`, not
`∀ k, x ≠ π/2 + kπ`, unless your paper layer already uses explicit
isolated-point predicates. It is the natural analytic domain for
`tan`, and Mathlib's `Real.tan` development is organized around
`cos x ≠ 0`.

## What to skip

Skip **Path A as a global strategy**. If you ever need it locally,
introduce

```lean
def Tau : ℂ := 2 * Real.pi * Complex.I
def EqModTau (z w : ℂ) : Prop := ∃ k : ℤ, z = w + k * Tau
```

and prove "evaluation modulo `Tau`" only for subterms that are
immediately consumed by `mkExpℂ`. Do not build a large `LogResult`
API unless you are intentionally writing a branch-aware evaluator.

Skip **Path B for `tan` and `arctan`**. The Cayley quotient is
already the right tangent identity; it is not a single-exp escape
hatch. For `arctan`, the clean non-log path is through `arcsin`,
not Euler.

Also skip the proposed `intToTerm k * piPubℂ` construction for Path
C. Repeated real-safe addition of `±π` or `±2π` is simpler and avoids
the exact `arg = π` trap you are trying to escape.

## Paper-faithfulness

Path C′ is not literally the same theorem as `∃ t, ∀ x, ...`. It is
a **regional compiler theorem**: for each real input, the meta-level
proof chooses a suitable EML tree. That discrepancy is meaningful if
your formal target is "one fixed syntax tree per primitive." But it
is not mathematically damning: your artefact already uses
positive/negative companion witnesses, and the paper itself
acknowledges branch corrections in the compiler. A pure EML grammar
has no runtime `floor`, `round`, or `case`; if the compiler uses
those to choose a corrected tree, the formal shape is naturally
`∀ x, ∃ t`.

## Question back to us

**Does your `arcsinTermℂ` theorem expose the result in `.re` or
`.im`?** If it exposes `.re`, `arctanViaArcsinℂ` should be almost
immediate. If it exposes `.im`, the same plan works, but the final
projection in the arctan paper-claim should follow that convention
rather than the old `mkLogℂ` arctan convention.

**Our answer:** `arcsinTermℂ.eval?` exposes the result in `.im` (per
`AUTHOR_SUMMARY.md`: *"each evaluates partially in `Option ℂ` to a
value whose `.re` (for `cos`, `sin`) or `.im` (for `arctan`,
`arccos`, `arcsin`, `tan`) equals the paper's stated real value"*).
So `arctanViaArcsinℂ` projects to `.im`, matching the existing
arctan paper-claim convention.

[^1]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Complex/Log.html
[^2]: https://arxiv.org/html/2603.21852v2
[^3]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Trigonometric/Arctan.html
[^4]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.html
