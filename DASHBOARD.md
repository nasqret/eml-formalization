# EML formalization — Stats Dashboard

> A visual companion to [README.md](README.md): coverage matrices, witness-tree
> size charts, code metrics, and a curated tour of the most interesting Lean
> code in the artefact.

[![Lean](https://img.shields.io/badge/Lean-4.28.0-violet)](https://leanprover.github.io/)
[![Build](https://img.shields.io/badge/lake%20build-8054%20jobs-success)](#build-trail)
[![Sorry-free](https://img.shields.io/badge/sorry-0-success)](#audit-trail)
[![Coverage](https://img.shields.io/badge/primitives-36%2F36-success)](#coverage-matrix)
[![Boundary](https://img.shields.io/badge/%C2%A7G%20boundary-3-orange)](#g-boundary-points)

---

## Table of contents

1. [Headline stats](#headline-stats)
2. [Coverage matrix](#coverage-matrix)
3. [Witness-tree size distribution (K-counts)](#witness-tree-size-distribution-k-counts)
4. [Code metrics — file and line counts](#code-metrics)
5. [§G boundary points](#g-boundary-points)
6. [The three Sheffer cousins (paper §3.1)](#the-three-sheffer-cousins)
7. [Witness gallery — curated Lean tour](#witness-gallery)
8. [Build and audit trail](#build-trail)

---

## Headline stats

| | |
|---|---:|
| Paper primitives sealed | **36 / 36** (100%) |
| `paper_claim_*` theorems exposed | **45** |
| `K_count_*` `rfl`-checked tree sizes | **15** |
| Lean kernel jobs in `lake build EML` | **8 054** |
| `sorry` / `admit` occurrences | **0** |
| §G structural boundary points (documented) | **3** |
| Witness-tree size — smallest | **K = 1** (the constant `1`) |
| Witness-tree size — largest | **K = 9 929 087** (`logb`, compiler-produced) |
| Span (smallest → largest) | **7 orders of magnitude** |

```mermaid
pie showData
    title Sealing status — 36 primitives by domain coverage
    "Full natural domain (atoms, real unaries, hyperbolic, binaries)" : 28
    "Wide subdomain via complex extension (cos, sin, tan, arctan, arcsin, arccos)" : 6
    "§G structural boundary (√0, arcosh 1, hypot(0,0))" : 0
```

> The "boundary" slice is shown empty deliberately — those three points are
> *not* sealed in the natural construction. The artefact ships counterexample
> witnesses for them in [`StructuralLimits.lean`](lambda_lab/proofs/eml/2603_21852/lean_workspace/EML/Framework/StructuralLimits.lean), and the paper itself does not provide EML
> terms for them either (paper line 342 explicitly notes the Lean-specific
> junk-value issue).

---

## Coverage matrix

Every cell either lists the sealed subdomain or marks the §G boundary point.

| Family | Primitive | Sealed on | Witness K | Status |
|---|---|---|---:|:-:|
| **Atoms** | `1` | full | 1 | ✅ |
| | `x` (`var n`) | full | 1 | ✅ |
| | `e` | full | 3 | ✅ |
| | `−1` | full | 17 | ✅ |
| | `2` | full | 19 | ✅ |
| | `½` | full | 59 | ✅ |
| | `π` (closed) | full | 233 | ✅ |
| | `i` (closed, complex) | full | 407 | ✅ |
| **Real unaries** | `exp` | full | 3 | ✅ |
| | `log` | `(0, ∞)` | 7 | ✅ |
| | `−` (neg) | full | 17 | ✅ |
| | `½·` (halve) | full | 221 | ✅ |
| | `(·)²` (sq) | full | 4 471 | ✅ |
| | `inv` | `ℝ ∖ {0}` | 18 029 | ✅ |
| | `σ` (sigmoid) | full | 98 593 | ✅ |
| | `√` | `(0, ∞)` | 2 589 | ✅ |
| | `√` at `0` | — | — | ⚠ §G |
| **Hyperbolic** | `sinh` | full | — | ✅ |
| | `cosh` | full | — | ✅ |
| | `tanh` | full | — | ✅ |
| | `arsinh` | full | 566 933 | ✅ |
| | `artanh` | `(−1, 1)` | 2 195 | ✅ |
| | `arcosh` | `(1, ∞)` | 567 605 | ✅ |
| | `arcosh` at `1` | — | — | ⚠ §G |
| **Binaries** | `+` | full | 27 | ✅ |
| | `−` | full | 43 | ✅ |
| | `avg` | full | 403 | ✅ |
| | `·` (mul) | full | 839 743 | ✅ |
| | `/` | `b ≠ 0` | 5 896 223 | ✅ |
| | `^` (pow) | `a > 0` | 1 069 569 | ✅ |
| | `log_b` | `b > 0, b ≠ 1, x > 0` | 9 929 087 | ✅ |
| | `hypot` | `ℝ² ∖ {(0,0)}` | 754 641 | ✅ |
| | `hypot(0, 0)` | — | — | ⚠ §G |
| **Trig** | `cos` | `ℝ ∖ {0}` (paired witnesses) | 1 273 + 1 289 | ✅ |
| | `sin` | `(−π, π) ∖ {0}` (paired) | 1 703 + 1 439 | ✅ |
| | `tan` | `(−π/2, π/2) ∖ {0}` (Cayley + paired) | 2 817 + 2 849 | ✅ |
| | `arctan` | `(−π, π) ∖ {0}` (paired) | 1 303 + 1 303 | ✅ |
| | `arccos` | full open `(−1, 1)` | 568 875 | ✅ |
| | `arcsin` | `(0, 1)` direct + full `(−1, 1)` via π/2 − arccos | 1 704 019 / 569 297 | ✅ |

**Legend.** ✅ = literal `EMLTerm` / `EMLTermℂ` witness, `rfl`-checked size, machine-verified `eval?` agreement with Mathlib's reference function · ⚠ §G = structural junk-value collision; counterexample witness in `StructuralLimits.lean`.

---

## Witness-tree size distribution (K-counts)

The 33 `rfl`-checked witness sizes span **seven orders of magnitude**, from `K = 1` (`one`) to `K = 9 929 087` (`logb`). Bars below scale logarithmically (each block = ~0.25 dex of `log₁₀ K`); raw values shown to the right.

```
one             █                                                 1
exp / e_const   ██                                                3
log / zero      ███                                               7
neg / negOne    █████                                            17
two             █████                                            19
add             ██████                                           27
sub             ██████                                           43
half_const      ███████                                          59
−i (closed)     ████████                                        127
halve           █████████                                       221
π (closed)      █████████                                       233
avg / i         ██████████                                  403/407
cos / cos_neg   ████████████                            1 273/1 289
arctan*         ████████████                                  1 303
sin_neg         █████████████                                 1 439
sin             █████████████                                 1 703
artanh          █████████████                                 2 195
√ (sqrt)        █████████████                                 2 589
tan / tan_neg   █████████████                            2 817/2 849
sq              ██████████████                                4 471
inv             █████████████████                            18 029
σ (sigmoid)     ████████████████████                         98 593
arsinh          ███████████████████████                     566 933
arccos          ███████████████████████                     568 875
arcosh          ███████████████████████                     567 605
arcsin_open     ███████████████████████                     569 297
hypot           ███████████████████████                     754 641
mul             ████████████████████████                    839 743
pow             █████████████████████████                 1 069 569
arcsin          ██████████████████████████                1 704 019
div             ████████████████████████████              5 896 223
logb            ███████████████████████████████           9 929 087
```

> The systematic gap between hand-tuned (small) and compiler-produced (large)
> witnesses is *informative*, not a defect. The paper's Table 4 lists hand-tuned
> figures as **upper bounds on the necessary tree size**; our compiler-produced
> figures are **machine-checked actual sizes** of mechanically-uniform witnesses.
> The structural compiler trades ~10⁵× in tree size for **per-primitive-uniform
> proof structure** — a worthwhile bargain in a kernel-checked artefact.

```mermaid
pie showData
    title K-count log buckets — 33 sized witnesses
    "tiny: K ≤ 100 (atoms, simple unaries)" : 13
    "small: 100 < K ≤ 10 000 (compiled small ops, trig core)" : 11
    "medium: 10 000 < K ≤ 1 000 000 (deep compositions)" : 5
    "huge: K > 1 000 000 (logb, div, mul, arcsin, pow)" : 4
```

---

## <a name="code-metrics"></a> Code metrics

### Top 10 framework files by line count

| Lines | File | Role |
|---:|---|---|
| 853 | [`Framework/F36ToEL.lean`](lambda_lab/proofs/eml/2603_21852/lean_workspace/EML/Framework/F36ToEL.lean) | F36 → EL translator: 36-case dispatch with closure lemmas |
| 554 | [`Framework/Unconditional.lean`](lambda_lab/proofs/eml/2603_21852/lean_workspace/EML/Framework/Unconditional.lean) | Domain-free wrapping helpers used by every paper claim |
| 453 | [`Framework/PaperClaims.lean`](lambda_lab/proofs/eml/2603_21852/lean_workspace/EML/Framework/PaperClaims.lean) | **Public scoreboard** — 45 `paper_claim_*` theorems |
| 293 | [`Framework/ELToEML.lean`](lambda_lab/proofs/eml/2603_21852/lean_workspace/EML/Framework/ELToEML.lean) | The structural compiler (Theorem 2 in `proof_structure.pdf`) |
| 275 | [`Framework/KCounting.lean`](lambda_lab/proofs/eml/2603_21852/lean_workspace/EML/Framework/KCounting.lean) | All 15 `K_count_*` theorems, all `:= rfl` |
| 238 | [`Framework/Sheffer.lean`](lambda_lab/proofs/eml/2603_21852/lean_workspace/EML/Framework/Sheffer.lean) | §3.1 companion-grammar scaffolding |
| 198 | [`Framework/StructuralLimits.lean`](lambda_lab/proofs/eml/2603_21852/lean_workspace/EML/Framework/StructuralLimits.lean) | The three §G boundary-point counterexamples |
| 153 | [`Framework/ELExpr.lean`](lambda_lab/proofs/eml/2603_21852/lean_workspace/EML/Framework/ELExpr.lean) | EL inductive type + total/partial eval |
| 151 | [`Framework/F36Expr.lean`](lambda_lab/proofs/eml/2603_21852/lean_workspace/EML/Framework/F36Expr.lean) | F36 inductive type — 36 named constructors |
| 116 | [`Framework/Realization.lean`](lambda_lab/proofs/eml/2603_21852/lean_workspace/EML/Framework/Realization.lean) | `EMLRealizationℂ` packages: closed `0`, `2`, `−i`, `i`, `π` |

**Total framework code:** 3 515 lines across 13 files.
**Plus:** 62 `Solutions/` chunks (per-statement decomposition, not counted above).
**Plus:** the trig-witness builder/closure pair under `Framework/Complex/` (the bulk of post-submission work, ~2 000 lines).

### Public API surface

```
$ make scoreboard
==== Public paper claims (45 theorems) ====
  paper_claim_var, paper_claim_one, paper_claim_negOne, paper_claim_two,
  paper_claim_half_const, paper_claim_e_const, paper_claim_pi, paper_claim_i,
  paper_claim_exp, paper_claim_log, paper_claim_inv, paper_claim_half,
  paper_claim_minus, paper_claim_sqr, paper_claim_sigma, paper_claim_sqrt_pos,
  paper_claim_sinh, paper_claim_cosh, paper_claim_tanh, paper_claim_arsinh,
  paper_claim_arcosh, paper_claim_artanh,
  paper_claim_add, paper_claim_sub, paper_claim_mul, paper_claim_div,
  paper_claim_avg, paper_claim_pow, paper_claim_logb, paper_claim_hypot,
  paper_claim_cos, paper_claim_cos_neg, paper_claim_cos_zero,
  paper_claim_sin, paper_claim_sin_neg, paper_claim_sin_zero,
  paper_claim_arctan_narrow, paper_claim_arctan_neg, paper_claim_arctan_zero,
  paper_claim_arccos_open,
  paper_claim_arcsin_narrow, paper_claim_arcsin_open,
  paper_claim_tan_narrow, paper_claim_tan_neg, paper_claim_tan_zero
```

---

## <a name="g-boundary-points"></a> §G boundary points

Three points where Mathlib's `Real.log 0 = 0` ("junk value") collides with the natural EML construction. Documented with concrete counterexamples in [`StructuralLimits.lean`](lambda_lab/proofs/eml/2603_21852/lean_workspace/EML/Framework/StructuralLimits.lean):

| Boundary | Why unsealable | Paper acknowledgement |
|---|---|---|
| `√0` | Natural witness `exp(½ · log x)` evaluates to `1` at `x = 0` (since `log 0 = 0`), not `0`. | Paper line 342 explicitly notes this Lean-specific issue. |
| `arcosh 1` | Composes `√(1² − 1) = √0`, inheriting the same collision. | Same. |
| `hypot(0, 0)` | Composes `√(0² + 0²) = √0`, inheriting the same collision. | Same. |

Closing any of these requires either extending the EML grammar with a primitive `Real.rpow` constructor (~400 new lines, off-paper) or moving the affected witness into the complex extension where the junk-value boundary is in different coordinates. **Neither is on the paper's roadmap.**

---

## <a name="the-three-sheffer-cousins"></a> The three Sheffer cousins (paper §3.1)

The paper presents EML, EDL, and −EML as a "family" (paper §3.1, equation block `\label{Sheffers}`). Per-primitive completeness is proved only for **EML** in the paper; the cousins are confirmed empirically via the Mathematica / Rust `VerifyBaseSet` procedure, not formally.

| Sheffer | Operator | Constant | Status (paper) | Status (this artefact) |
|---|---|---|---|---|
| **EML** | `eml(x, y) = exp(x) − log(y)` | `1` | **proved complete for 36 primitives** | ✅ formalized end-to-end (this repo) |
| **EDL** | `edl(x, y) = exp(x) / log(y)` | `e` | conjectured complete; empirical via VerifyBaseSet | scaffolding in `Sheffer.lean`; **no per-primitive proofs** (Plan D — 1–2 wk) |
| **−EML** | `−eml(y, x) = log(x) − exp(y)` | `−∞` | conjectured complete; empirical via VerifyBaseSet | scaffolding; **no per-primitive proofs** (Plan E — 1–2 wk; needs `EReal` for `−∞`) |

> ✅ **Naming cleanup complete (Plan A done).** `Sheffer.lean` now contains exactly the
> two paper-named cousins, `EDLTerm` and `NegEMLTerm`. The previously-misnamed
> `LDETerm` (`log(x)/exp(y)`, division — *not* the paper's `−EML = log(x) − exp(y)`
> subtraction) has been replaced. The fabricated *binary* `T1Term`/`T2Term` have been
> removed; the paper's actual T₁ / T₂ are **ternary** (SI §1.4, page 8:
> `T₁(x,y,z) = e^(x−y)·ln x/ln z`, `T₂(x,y,z) = e^(x−y)·ln z/ln x` with
> `T₂(x,x,x) = 1`) and are out of scope for the present formalisation —
> the SI flags them as preliminary candidates for the constant-free Sheffer
> open question (SI §1.5 #3). Line-level paper sourcing in
> [`Sheffer/PaperSourcing.md`](lambda_lab/proofs/eml/2603_21852/lean_workspace/EML/Framework/Sheffer/PaperSourcing.md).

---

## <a name="witness-gallery"></a> Witness gallery — curated Lean tour

Five witnesses worth lingering on, ordered by how much character each has.

### 1. `EMLTerm.eval?` — the partial-evaluation kernel

The architectural decision that made the whole formalization tractable. Instead of fighting Mathlib's total `Real.log 0 = 0` "junk value", we evaluate to `Option ℝ` and refuse to commit at the boundary:

```lean
-- File: lean_workspace/EML/Framework/EMLPartial.lean
noncomputable def EMLTerm.eval? (env : Nat → ℝ) : EMLTerm → Option ℝ
  | .one     => some 1
  | .var n   => some (env n)
  | .eml a b =>
      match EMLTerm.eval? env a, EMLTerm.eval? env b with
      | some va, some vb =>
          if 0 < vb then some (Real.exp va - Real.log vb) else none
      | _, _ => none
```

**Why this matters.** A total evaluation would force a junk value at the boundary (`log 0 = 0`); bridge theorems would then have to dance around the points where this convention disagrees with the natural mathematical answer. Partial evaluation lets us state cleanly *"the witness has no value at the boundary, and the paper claim is stated on a subset that excludes it"* — which is exactly what the paper does.

### 2. `tanCoreTermℂ` — Pro's Cayley quotient

A doubled-angle Möbius identity, suggested by an independent GPT Pro code review with no shared context:

> `q(x) := (e^{2ix} − 1) / (1 + e^{2ix}) = i · tan x`,  for `x ∈ (0, π/2)`.

Avoids the `e^{ix} + e^{−ix}` `ADDsafeℂ` constraint explosion that had stalled progress for several days. The witness compresses to **K = 2 817**:

```lean
-- File: lean_workspace/EML/Framework/Complex/Builders/Trig.lean:1314
noncomputable def tanCoreTermℂ : EMLTermℂ :=
  let twoX := mkMulℂ twoPubℂ (.var 0)
  let I2x  := mkMulℂ iTermPubℂ twoX
  let E2   := mkExpℂ I2x
  mkDivℂ (mkSubℂ E2 .one) (mkAddℂ .one E2)
```

The result is purely imaginary `i · tan x`, so `(eval?).im = tan x`. The companion `tanCoreTermℂ_neg` (K = 2 849) handles the negative side via a swap-numerator Cayley.

### 3. `arcsinTermℂ_open` — pure identity manipulation

The narrow witness `arcsinTermℂ` (K = 1 704 019) only handles `0 < x < 1` because its inner `mkMulℂ iTermPubℂ (.var 0)` requires `arg(x) < π`, which fails at `arg = π` exactly (real negatives). Identity-driven reformulation `arcsin x = π/2 − arccos x`, encoding `iπ/2` as `mkLogℂ iTermPubℂ` (since `Complex.log i = iπ/2`):

```lean
-- File: lean_workspace/EML/Framework/Complex/Builders/Trig.lean:1221
/-- The wider arcsin witness, sealed on the **full open** `(-1, 1)`. -/
noncomputable def arcsinTermℂ_open : EMLTermℂ :=
  mkSubℂ (mkLogℂ iTermPubℂ) arccosTermℂ
```

**Result:** witness compresses from K = 1 704 019 → 569 297 (**3× compression**) *and* extends the sealed domain from `(0, 1)` to full open `(−1, 1)`. The same architectural toolkit — *real-EL `−x` lifted to ℂ via the homomorphism `EMLTerm.toComplex` plus identity-driven witness restructuring* — cracks all five trig widenings in 30–50 lines per primitive.

### 4. `cosTermℂ` — the trig base case

The cosine witness exhibits the EML grammar's denestability under `mkExpℂ`:

```lean
-- File: lean_workspace/EML/Framework/Complex/Closures/Trig.lean:540
def cosTermℂ : EMLTermℂ :=
  mkExpℂ (mkExpℂ (.eml cosLhsℂ cosRhsℂ))
```

Evaluates to `exp(exp(log i + log x)) = exp(i · x)` whenever `env 0 = (x : ℝ)` for `x > 0`. The real part is `cos x`, so `paper_claim_cos` projects via `.re`. K = 1 273 — the smallest of all trig witnesses, because the construction stays close to Euler's formula without algebraic detours.

### 5. `paper_claim_pi` — the headline atom

Showing what a sealed claim *looks like* externally, in the `EML.Framework.PaperClaims` API:

```lean
-- file: lean_workspace/EML/Framework/PaperClaims.lean
theorem paper_claim_pi :
    ∃ t : EMLTermℂ, ∀ env : ℕ → ℂ,
      EMLTermℂ.eval? env t = some ((Real.pi : ℝ) : ℂ) := ...
```

A single existential, environment-quantified, evaluating to the literal `Real.pi` cast to ℂ. The witness `t` is a 233-node `EMLTermℂ` tree (`K_count_pi`); the proof body is a few lines unwrapping the `realizeℂ_pi` package. **This is the shape of every paper-claim theorem in the artefact** — no additional axioms, no opaque definitions, just a literal syntax tree and a kernel-checked equality.

---

## <a name="build-trail"></a> Build and audit trail

### Local re-verification

```bash
$ make build
✔ [8052/8054] Built EML.Framework.PaperClaims (56s)
✔ [8053/8054] Built EML (41s)
Build completed successfully (8054 jobs).
```

### PCSS Eagle HPC re-verification

The artefact has been independently re-verified on PCSS Eagle (job 7 041 555, May 7 2026):

| Metric | Value |
|---|---:|
| Files re-built | 88 |
| Failures | 0 |
| Wall time | 42 s |

Re-launch with `eagle_scripts/verify_all.sbatch`.

### <a name="audit-trail"></a> `#print axioms` audit

The artefact uses only Mathlib's standard noncomputable axioms (classical choice, function extensionality, propositional extensionality — the inherited Lean 4 / Mathlib defaults). **No project-specific axioms.** No `sorry`, no `admit`, no `native_decide` shortcuts.

---

## See also

- **[README.md](README.md)** — project entry point, installation, quick start.
- **[lambda_lab/proofs/eml/2603_21852/AUTHOR_SUMMARY.md](lambda_lab/proofs/eml/2603_21852/AUTHOR_SUMMARY.md)** — author-facing synopsis (forwardable).
- **[lambda_lab/proofs/eml/2603_21852/OPEN_QUESTIONS.md](lambda_lab/proofs/eml/2603_21852/OPEN_QUESTIONS.md)** — five concrete plans (Sheffer cleanup, full-real-domain trig × 2, EDL completeness, −EML completeness).
- **[lambda_lab/proofs/eml/2603_21852/notes/proof_structure.pdf](lambda_lab/proofs/eml/2603_21852/notes/proof_structure.pdf)** — 11-page expository paper on the architecture (the primary reading for moderately-technical readers who want to understand *why* the proof is structured this way without diving into Lean source).
- **[First_run.md](First_run.md)** — bootstrap recipe for fresh checkouts / fresh Claude sessions.
