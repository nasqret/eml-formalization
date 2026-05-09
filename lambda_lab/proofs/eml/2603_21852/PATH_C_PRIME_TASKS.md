# Path C′ task slate — full-real-domain trig (and beyond)

> Long-term task design covering Path C′ (full-real-domain trig — short
> term) and Plans D / E (Sheffer-cousin completeness — long term).
> Identifies which chunks are hand-coded and which are Aristotle-bait.

## Aristotle integration model

Existing chunks (003–070) are submitted to Aristotle as **isolated Lean
files importing `Mathlib` only**. Each `target.lean` inlines whatever
EML grammar fragments it needs and asks for a closed-form Mathlib
identity or a small witness-correctness proof. Aristotle returns a
`result.lean` with the proof filled in.

For Path C′ and the Plans D/E work, Aristotle is best deployed for:

1. **Pure Mathlib-real-analysis lemmas** (e.g. `x/√(1+x²) ∈ (-1, 1)`)
   where library search and `nlinarith`/`polyrith` are decisive
2. **Witness-discovery for Sheffer cousins** (Plans D/E) — given a
   target identity for an EDL or −EML primitive, find a finite term
3. **Closed-form algebraic identities** between exp/log expressions

Aristotle is **not** the right fit for:
- Framework integration (definitions of macros, eval lemmas threading
  the partial-eval semantics)
- Substitution / induction / case-analysis proofs that span existing
  framework lemmas
- ADDsafeℂ-bundle discharges that already have a clean
  `ADDsafeℂ_ofReal_ofReal` shortcut

## Path C′ chunks (71–83)

> Goal: extend `sin`, `arctan`, `tan` to all of ℝ (with isolated
> singularities). All sub-paths use `EMLTermℂ.subst0` + the existing
> full-domain witness for a "downstream" primitive.

| ID | Title | Hand vs Aristotle | Estimated lines | Status |
|---|---|---|---:|---|
| 071 | `eval?_mkSubℂ_ofReal` — real-safe subtraction (parallel to `mkAddℂ_ofReal`) | Hand | 30 | ⏳ |
| 072 | `shiftByPiℂ_pos`, `shiftByPiℂ_neg` — single π-shift terms + eval | Hand | 50 | ⏳ |
| 073 | `shiftByPeriodℂ : ℤ → EMLTermℂ` + `eval?_shiftByPeriodℂ` (induction on `k`) | Hand | 80 | ⏳ |
| 074 | `halfPiPubℂ` — π/2 as EMLTermℂ + eval | Hand | 40 | ⏳ |
| 075 | `sinViaCosℂ` + correctness on `ℝ ∖ {π/2}` (uses `Real.cos_pi_div_two_sub`) | Hand | 60 | ⏳ |
| 076 | `atanArgELℝ` — real-fragment compile of `x / √(1 + x²)` | Hand | 30 | ⏳ |
| **077** | **`atanArg_in_Ioo`** — `x/√(1+x²) ∈ (-1, 1)` for all `x : ℝ` | **Aristotle** | 20 | ⏳ |
| 078 | `arctanViaArcsinℂ` + correctness (uses `Real.arctan_eq_arcsin` + 077) | Hand | 80 | ⏳ |
| **079** | **`tan_period_reduction`** — for `cos x ≠ 0`, ∃ `k : ℤ` with `x - k·π ∈ Ioo (-π/2) (π/2)` | **Aristotle** | 30 | ⏳ |
| 080 | `tan_full` — combine 073/079 with existing `tanCoreTermℂ` | Hand | 80 | ⏳ |
| 081 | `paper_claim_sin_full` (PaperClaims.lean wrap-up) | Hand | 15 | ⏳ |
| 082 | `paper_claim_arctan_full` | Hand | 15 | ⏳ |
| 083 | `paper_claim_tan_full` | Hand | 15 | ⏳ |

**Total estimated effort.** ~545 lines across 13 chunks. With the
foundation (`subst0`, `ADDsafeℂ_ofReal_ofReal`) already landed, each
piece is mostly mechanical. Two chunks (077, 079) are good Aristotle
candidates — pure Mathlib real-analysis with no framework dependencies.

### Chunks 077 and 079 — Aristotle submissions

These two are simple, self-contained Mathlib facts. Submit early to
let Aristotle work in parallel with the hand-coded pieces. If they
return successful proofs, we drop them in. If they fail or take too
long, the proofs are also achievable by hand (~20 lines each).

**Chunk 077 target:**

```lean
import Mathlib

theorem atanArg_in_Ioo (x : ℝ) :
    x / Real.sqrt (1 + x^2) ∈ Set.Ioo (-1 : ℝ) 1 := by
  sorry
```

**Chunk 079 target:**

```lean
import Mathlib

theorem tan_period_reduction (x : ℝ) (hx : Real.cos x ≠ 0) :
    ∃ k : ℤ, x - (k : ℝ) * Real.pi ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) ∧
             Real.tan x = Real.tan (x - (k : ℝ) * Real.pi) := by
  sorry
```

## Plan D chunks (Plan-of-record: ~36 chunks for EDL primitives)

Long-term — Plans D follows once Path C′ is complete. EDL has the same
36 paper primitives as EML; each needs a literal `EDLTerm` witness.
Plan D is heavily Aristotle-driven because each witness must be
**discovered** rather than constructed by composition (the paper
provides EDL witnesses sketchily, not in full).

Submission strategy: **batch-submit identity-style atoms first** (var,
one, e_const, exp via `edl(x, e)`, log via `edl(0, edl(0, y))`-style
search). Hard cases (mul, div, trig family) need oracle support from
Mathematica's `VerifyBaseSet` — Aristotle alone may not find these.

Provisional chunk numbering: 084–119 (one per primitive, mirroring
003-058's structure for EML).

## Plan E chunks (~36 chunks for −EML primitives)

Same structure as Plan D, with the additional complication of the `−∞`
constant. Two approaches:
- **EReal-based:** rebuild `NegEMLTerm` over `EReal` instead of `ℝ`.
  Each chunk needs `EReal`-aware partial-eval semantics.
- **Workaround:** inline `-∞`-needing identities at the witness level
  using sufficiently large finite negatives. Less faithful but simpler.

Provisional chunk numbering: 120–155.

## Submission order (high-priority first)

1. **Hand: 071** — unblocks 072–083 framework integration
2. **Aristotle: 077** — submit early; mechanical real analysis
3. **Aristotle: 079** — submit early; mechanical real analysis
4. **Hand: 072–076** — the rest of Path C′ framework
5. **Hand: 078, 080–083** — wrap-up theorems (depend on Aristotle results)
6. **Aristotle: Plan D atoms (parallel)** — once Path C′ is closed
7. **Hand: Plan D framework integration**
8. **Plan E** — only after Plan D's lessons are codified

## Acceptance criteria per phase

**Path C′ acceptance.** `paper_claim_sin_full`, `paper_claim_arctan_full`,
`paper_claim_tan_full` exist in `PaperClaims.lean`, each a one-line
`∀ x, x ≠ <isolated point> → ∃ t : EMLTermℂ, ...` existential. K-counts
machine-checked in `KCounting.lean`. `lake build` clean.

**Plan D acceptance.** `EDL_PaperClaims.lean` parallel to `PaperClaims.lean`
with 45+ theorems. K-counts in `EDL_KCounting.lean`.

**Plan E acceptance.** Same as Plan D for `NegEMLTerm`.

## Time estimate

| Phase | Effort |
|---|---|
| Path C′ remaining | 3–5 days |
| Plan D | 1–2 weeks |
| Plan E | 1–2 weeks |
| **Total long-term work** | ~1 month focused effort |
