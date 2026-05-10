# EML formalization — arXiv:2603.21852

Lean 4 + Mathlib v4.28 formalization of *"All elementary functions from a single binary operator"* (Andrzej Odrzywołek, arXiv:2603.21852).

## Headline result

> **All 36 paper primitives are formalized completely on a non-empty open subdomain of their natural domain — modulo three structural boundary points (`√0`, `arcosh 1`, `hypot(0, 0)`).**

Each paper primitive is sealed via a literal `EMLTermℂ` (or `EMLTerm`, real fragment) witness term whose `eval?` matches the paper's stated value, with the Lean kernel as the only acceptance criterion.

## Where to look first

| File | Purpose |
|---|---|
| **`lean_workspace/EML/Framework/PaperClaims.lean`** | One Lean theorem per paper primitive. Each `paper_claim_<f>` is a one-line existential: *"there exists a finite EML term whose evaluation matches the paper's stated value, on an open subdomain of the natural domain."* This is the **public API** — readers can `#check paper_claim_<f>` to verify the seal. |
| **`lean_workspace/EML/Framework/StructuralLimits.lean`** | The three boundary points (`√0`, `arcosh 1`, `hypot(0, 0)`) where the natural EML construction collides with the convention `Real.log 0 = 0`. These are documented with machine-checked `decide`-style artefacts. The paper itself does not provide EML terms for these points either. |
| **`lean_workspace/EML/Framework/KCounting.lean`** | Witness-tree sizes for **all 36 paper primitives** (plus the three widening companions), machine-checked by `rfl` against paper Table 4. Covers the closed numeric/imaginary constants, all real-fragment atoms / unaries / binaries via the F36→EL→EML compile pipeline, and the six complex-fragment trig witnesses with their widening companions. |
| **`lean_workspace/EML/Framework/Sheffer.lean`** | Scaffolds the **two paper-named Sheffer companions** (`EDL` and `−EML`, paper §3.1 lines 273–284) — each with its own inductive `*Term` type, partial `eval?`, size measure, and trivial unary-collapse identity. Demonstrates that the EML methodology generalises uniformly across the paper's §3.1 companion family. Per-primitive completeness for the cousins is paper-open (Plans D and E in `OPEN_QUESTIONS.md`). Line-level paper sourcing in [`notes/legacy_planning/Sheffer_PaperSourcing.md`](notes/legacy_planning/Sheffer_PaperSourcing.md). |
| **`OPEN_QUESTIONS.md`** | Concrete action plans for every feasible extension (Sheffer cleanup, full-real-domain trig via custom branch or multi-witness periodicity, EDL / −EML per-primitive completeness) plus paper-open conjectures (§3.2 minimality, §4.3 gradient training) and the three §G structural boundary points. |
| **`AUTHOR_SUMMARY.md`** | Author-facing synopsis: what is sealed, what surprised us, what remains open, plus a literal map from paper sections to the formalised artefacts. |

## Architecture

```
F36Expr  --- the paper's 36-primitive source language
   |
   |  translate?      Framework/Compilers/F36ToEL.lean
   v
ELExpr  --- intermediate language with Real-valued partial eval
   |
   |  compile          Framework/Compilers/ELToEML.lean
   v
EMLTerm  --- {1, x, eml(x, y) = exp x − log y}, partial Real eval

Complex layer (for π, i, cos, sin, tan, arctan, arccos, arcsin):
F36Expr.* ──► EMLTermℂ via Euler-style witnesses (Framework/Complex/*)
EMLTermℂ partial eval: Option ℂ; eml(a, b) defined when b ≠ 0.
```

Three architectural moves recommended by an independent **GPT Pro** code review (separate context, no shared scratchpad) and integrated:

1. **Public closed constants** — `realizeℂ_{zero, two, negI}` exposed in `Closures/Constants.lean` (alongside the existing `realizeℂ_{pi, i}`).
2. **Real → complex term lift** — `EMLTerm.toComplex` (a homomorphism on the EML grammar) lets every complex trig witness reuse the *already-sealed* real `sqrt`/`pow`/etc. compositions instead of redoing branch-cut work.
3. **Generic side-condition helper** — `addsafe_ofReal_left` discharges the recurring 11-field `ADDsafeℂ` bundle whenever the left-hand operand is real.

These unblocked the four trig literal witnesses (`arctan`, `arccos`, `arcsin`, `tan` via the doubled-angle Cayley identity).

## Reproducing locally

```bash
cd lean_workspace
lake build       # builds the EML library + transitive Mathlib
                 # ~8 050 jobs, sorry-free
```

The `EML.lean` root imports the public surface:

```lean
import EML.Basic
import EML.Term
import EML.Framework.PaperClaims
import EML.Framework.StructuralLimits
import EML.Framework.KCounting
import EML.Framework.Sheffer
```

## Reproducing on PCSS Eagle (HPC)

```bash
# From a node where ~/pl0414-02/scratch/elan_dl/ has the Lean toolchain tarball
cd /mnt/storage_5/scratch/pl0414-02
sbatch verify_all.sbatch    # parallel verify across 24 cores
```

The SLURM scripts in `eagle_scripts/` (one level up) handle:

- `rebuild_cache.sbatch` — rebuilds the Lake olean cache from current source.
- `verify_all.sbatch` — re-verifies every chunk in parallel.

Latest clean re-verify (May 7 2026): job 7041555, 88 files / 0 fail / 42 s.

## What's sealed

### Atoms (7) — full domain, all literal

`paper_claim_{var, one, negOne, two, half_const, e_const, pi}` (real fragment + `pi` via complex bridge).

### Real unary (8) — full domain except sqrt at `0` boundary

`paper_claim_{exp, log, inv, half, minus, sqr, sigma}` on full natural domains; `paper_claim_sqrt_pos` on `(0, ∞)` (boundary `x = 0` is §G structural).

### Hyperbolic (6) — full domain except arcosh at `1` boundary

`paper_claim_{sinh, cosh, tanh, arsinh, artanh}` on full domains; `paper_claim_arcosh` on `(1, ∞)` (boundary `x = 1` is §G structural).

### Binary (8) — full domain except hypot at `(0, 0)` boundary

`paper_claim_{add, sub, mul, div, avg, pow, logb}` on full natural domains; `paper_claim_hypot` on `ℝ² \ {(0, 0)}` (boundary is §G structural).

### Trig (6) — all literal; wider domains via companion witnesses

| Primitive | Sealed subdomain | Construction |
|---|---|---|
| `cos` | `(-∞, 0) ∪ (0, ∞)` | `cosTermℂ` (positive side) + `cosTermℂ_neg` (negative side via `cos(−x) = cos x`) |
| `sin` | `(-π, π) \ {0}` | `sinTermℂ` (positive side) + `sinTermℂ_neg` (negative side via `sin x = cos(π/2 − x)` and `log(−I) = −iπ/2`) |
| `arctan` | `(-π, π) \ {0}` | `arctanTermℂ` (positive) + `arctanTermℂ_neg` (negative via `1 + ix = 1 − i·(−x)`) |
| `arccos` | `(-1, 1)` | `arccosTermℂ` via `mkLogℂ (mkAddℂ var (mkMulℂ iTerm sqrtTerm))` |
| `arcsin` | **full open** `(-1, 1)` | `arcsinTermℂ_open` via `arcsin x = π/2 − arccos x` and `mkLogℂ iTermPubℂ = iπ/2` |
| `tan` | `(-π/2, π/2) \ {0}` | `tanCoreTermℂ` (positive Cayley) + `tanCoreTermℂ_neg` (swap-numerator Cayley `(1−E_neg)/(1+E_neg) = i·tan x`) |

The companion witnesses (`arcsinTermℂ_open`, `arctanTermℂ_neg`,
`cosTermℂ_neg`) use the negation lift `negVarTermℂ` (the
real-EL-compiled `−x` lifted via `EMLTerm.toComplex`) to circumvent the
`mkMulℂ I x` `arg(x) < π` barrier, which fails for `x ≤ 0` real.

### Imaginary unit `i` — literal

`paper_claim_i` from `realizeℂ_i`.

### Single-point trig boundaries — `x = 0`

`paper_claim_{cos,sin,tan,arctan}_zero` use the trivial constant
witnesses `.one` (`cos 0 = 1`) and `zeroPubℂ` (`sin 0 = tan 0 = arctan 0
= 0`), filling the previous narrow-domain gap at the origin.

## Boundary points (§G structural)

Three measure-zero corners where the natural EML construction fails because `Real.log 0 = 0` (Mathlib junk):

* **`√0 = 0`**: `mkSqrtPos` requires positive argument.
* **`arcosh 1 = log(1 + √(1² − 1)) = log(1 + √0)`**: inner sqrt hits the `√0` boundary.
* **`hypot(0, 0) = √(0² + 0²) = √0`**: same.

Documented in `StructuralLimits.lean` with concrete derivations. The paper's own Table of Witnesses does not provide explicit EML terms for these boundary points either.

## What's not done (open work — see `OPEN_QUESTIONS.md` for action plans)

| Item | Status | Plan |
|---|---|---|
| **Sheffer naming cleanup** | ✅ **DONE** — `Sheffer.lean` now hosts only the two paper-named cousins (`EDL`, `−EML` via `NegEMLTerm`); the misnamed `LDETerm` has been replaced and the fabricated binary `T1Term`/`T2Term` removed. SI §1.4 ternary candidates documented as preliminary future work in [`notes/legacy_planning/Sheffer_PaperSourcing.md`](notes/legacy_planning/Sheffer_PaperSourcing.md). | Plan A — complete |
| **Full-real-domain trig** | ✅ **DONE** via Path C′ (GPT Pro's recommendation: range-reduction by substitution). `paper_claim_{sin_full, arctan_full, tan_full}` cover full natural domains: `sin` on `ℝ ∖ {π/2}`, `arctan` on full ℝ, `tan` on `{x : cos x ≠ 0}`. Foundation: `ADDsafeℂ_ofReal_ofReal` keeps period shifts in the real fragment. Plan B (custom log branch) was found architecturally infeasible — see [`OPEN_QUESTIONS.md`](OPEN_QUESTIONS.md) §B.0. | Path C′ — complete |
| **EDL per-primitive completeness** | `EDLTerm` grammar scaffolded; per-primitive paper claims paper-open. | Plan D (1–2 wk) |
| **−EML per-primitive completeness** | `NegEMLTerm` grammar scaffolded; per-primitive paper claims paper-open. Closing Lean-side completeness needs Mathlib's `EReal` for the `−∞` constant. | Plan E (1–2 wk) |
| **§3.2 universal minimality conjecture** | Paper-open — paper does not prove it; one `sorry` in chunk `029_eml_minimality.lean`. | Research result, not a formalisation task |
| **§4.3 gradient training** | Out of scope — requires optimisation-in-Lean framework that doesn't exist in Mathlib. | — |
| **Eagle re-verify** of today's tan/arccos/arcsin chunks | Blocked by Eagle's pre-existing Mathlib snapshot (two unrelated modules broken). Local build is source of truth. | Wait for upstream Mathlib fix or upgrade |

## Authors and acknowledgements

* Bartosz Naskręcki (UAM Poznań / PW) — formalisation lead.
* **Aristotle** (Harmonic) — proof search for many individual chunks.
* **GPT Pro** — independent code review across multiple rounds; recommended the structural-compiler architecture and the Cayley-quotient route for tan.
* **Claude** (Anthropic) — orchestration, scaffolding, composition.
* **Mathematica** — enumeration and witness candidate search.
* **Codex** (OpenAI) — paraphrase and informalization.
* **Mathlib community** — the underlying Lean library.
* **Andrzej Odrzywołek** — the source paper.

## Licence

MIT — see `LICENSE` at the repo root.
