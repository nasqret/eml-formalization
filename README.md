# EML — All elementary functions from a single binary operator

> A Lean 4 + Mathlib v4.28 formalization of arXiv:2603.21852
> (Andrzej Odrzywołek, *"All elementary functions from a single binary operator"*).

[![Lean](https://img.shields.io/badge/Lean-4.28.0-violet)](https://leanprover.github.io/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28-blue)](https://github.com/leanprover-community/mathlib4)
[![Build](https://img.shields.io/badge/lake%20build-8062%20jobs-success)](#quick-start)
[![Sorry-free](https://img.shields.io/badge/sorry-0-success)](#headline)
[![Paper](https://img.shields.io/badge/arXiv-2603.21852-darkred)](https://arxiv.org/abs/2603.21852)
[![Code license](https://img.shields.io/badge/code-Apache--2.0-blue)](LICENSE)
[![Docs license](https://img.shields.io/badge/docs-CC--BY--SA--4.0-lightgrey)](LICENSE-DOCS)
[![Live demo](https://img.shields.io/badge/live%20demo-EML%20Tree%20Builder-purple)](https://nasqret.github.io/eml-formalization/)

---

## <a name="headline"></a> Headline

**All 36 paper primitives are formalized via literal `EMLTermℂ` (or `EMLTerm`) witness terms whose `eval?` matches the paper's stated value, on a non-empty open subdomain of the natural mathematical domain. The three §G boundary points the paper itself flags (`√0`, `arcosh 1`, `hypot(0, 0)`) are additionally sealed via witness-family theorems (`∀ env, [hyp] → ∃ t, …`) in `GFullFix.lean`.**

The Lean kernel is the only acceptance criterion: every witness is a concrete syntax tree whose partial evaluation (`Option ℂ`-valued) is checked to equal the corresponding `Real.sin x`, `Real.exp x`, `Real.arcsin x`, etc.

### At a glance

|     | Count | Notes |
|---|---:|---|
| 📐 EML paper primitives sealed | **36 / 36** | atoms · real unaries · hyperbolic · binaries · trig |
| 📜 `paper_claim_*` theorems (EML) | **48** | in `EML.Framework.PaperClaims`; includes Path C′ `sin_full`, `arctan_full`, `tan_full` |
| 📜 EDL `paper_claim_*` theorems | **8** | in `EML.Framework.Sheffer` (Plan D) |
| 📜 −EML `paper_claim_*` theorems | **5** | in `EML.Framework.Sheffer` (Plan E) |
| 📜 **Original public claims** | **61** | 48 EML + 8 EDL + 5 −EML |
| ⭐ Frontier theorems (GPT Pro consult) | **+39** | SI §1.5 #5, §G witness-family, polynomial-binary impossibility, EDL closure scaffold (conditional on `EDLTranscendenceBarrier`), direct-macro alternative witnesses, EReal templates |
| 📜 **Total public theorems** | **100** | 61 original + 39 frontier |
| 🌳 K-count theorems (`rfl`-checked tree sizes) | **44** | in `EML.Framework.KCounting` (33 original + 9 direct-macro alternatives + 2 conditional-helper) |
| 🛠 Lean kernel jobs | **8 062** | `lake build` finishes sorry-free |
| 🚫 `sorry` / `admit` / axiom abuse | **0** | clean by `#print axioms` |
| ⚠ §G structural boundary points | **3 / 3 sealed** | `√0`, `arcosh 1`, `hypot(0, 0)` — now sealed via witness-family quantifier flip in `GFullFix.lean` |

---

## Coverage scoreboard

| Family | Count | Single structural witness (open-domain) | Boundary / full-domain (witness-family in `GFullFix.lean`) |
|---|---:|---|---|
| **Atoms** (`1`, `π`, `e`, `−1`, `2`, `½`, `x`, `i`) | 8 | full domain | — |
| **Real unaries** (`exp`, `log`, `inv`, `½·`, `−`, `(·)²`, `σ`) | 7 | full natural domain | — |
| `√` | 1 | `(0, ∞)` — `paper_claim_sqrt_pos` | `∀ x ≥ 0, ∃ t, t.eval = √x` — `paper_claim_sqrt_full` |
| **Hyperbolic** (`sinh`, `cosh`, `tanh`, `arsinh`, `artanh`) | 5 | full natural domain | — |
| `arcosh` | 1 | `(1, ∞)` — `paper_claim_arcosh` | `∀ x ≥ 1, ∃ t, t.eval = arcosh x` — `paper_claim_arcosh_full` |
| **Binaries** (`+`, `−`, `·`, `/`, `avg`, `^`, `log_b`) | 7 | full natural domain | — |
| `hypot` | 1 | `ℝ² ∖ {(0,0)}` — `paper_claim_hypot` | `∀ (x, y), ∃ t, t.eval = hypot(x, y)` — `paper_claim_hypot_full` |
| **Trig** `cos` | 1 | `ℝ ∖ {0}` | — (full domain) |
| **Trig** `sin` | 1 | `ℝ ∖ {π/2}` (full domain via Path C′) | — |
| **Trig** `arctan` | 1 | full ℝ (full domain via Path C′) | — |
| **Trig** `tan` | 1 | `{x ∣ cos x ≠ 0}` (full natural domain via Path C′) | — |
| **Trig** `arccos`, `arcsin` | 2 | full open `(−1, 1)` | — |

**Path C′ delivered full-real-domain witnesses for `sin`, `arctan`, `tan`** via GPT Pro's recommendation: range-reduction by substitution.

> **Two different shapes** appear in the table above:
> - **Single structural witness** (the bulk of the artefact): one closed `EMLTerm` or `EMLTermℂ` whose `eval?` matches the paper's value on an *open* subdomain of the natural domain, independent of any environment.
> - **Witness-family** (used at §G boundaries and for the wider Path-C′ trig domains): a theorem of the form `∀ env, [hyp] → ∃ t : EMLTerm, t.eval? env = some <value>`. The term `t` may depend on `env`. The boundary case picks `mkZero`; off-boundary the existing narrow witness applies.

> **Path C′ in one paragraph.** Pro's refinement of the original Plan C. The narrow trig witnesses fail outside their submission-era domains because intermediate complex values cross the `arg = π` cut. Plan B (custom log branch) is architecturally infeasible — `EMLTermℂ.eval?` hard-codes Mathlib's principal `Complex.log`. Plan C′ instead: (1) prove `ADDsafeℂ_ofReal_ofReal` once — the gnarly 11-condition `mkAddℂ` precondition bundle holds automatically when both arguments are real-valued, so period shifts via repeated `mkAddℂ` of fixed real period constants stay entirely in the real fragment; (2) use `EMLTermℂ.subst0` to replace `var 0` in an existing full-domain witness with a real-valued shift term; (3) reuse, don't reshape: `sin x = cos(π/2 − x)` (cos already covers `ℝ ∖ {0}`), `arctan x = arcsin(x / √(1+x²))` (arcsin already covers `(−1, 1)`), `tan x = tan(x − kπ)` (period reduction). The witness becomes a *family* (∀x∃t shape), faithful to the paper compiler's "manual i-sign correction".

See [`process_archive/gpt_pro_bundle/trig_widening/RESPONSE.md`](process_archive/gpt_pro_bundle/trig_widening/RESPONSE.md) for the verbatim consult and [`OPEN_QUESTIONS.md`](lambda_lab/proofs/eml/2603_21852/OPEN_QUESTIONS.md) for the status of the remaining plans.

<a name="trig-note"></a>**Trig full-domain coverage delivered** (Path C′, 2026-05-09): the previously narrow `sin`, `arctan`, `tan` witnesses are now lifted to full natural domain via range-reduction substitution. See [`OPEN_QUESTIONS.md`](lambda_lab/proofs/eml/2603_21852/OPEN_QUESTIONS.md) for the architectural finding (Plan B's "custom log branch" was found infeasible) and Pro's recommended Path C′.

---

## How the proof is built

The proof reduces `f ↝ T_f` through a three-language pipeline. Each box is an inductive type; each arrow is a total function modulo partial evaluation at the leaves.

```mermaid
flowchart LR
    F36["F36<br/><sub>36 paper primitives<br/>partial denotation</sub>"]
    EL["EL<br/><sub>elementary intermediate<br/>{exp, log, neg, inv, +, −, ·, /, …}</sub>"]
    EML["EML<br/><sub>single-operator grammar<br/>T ::= 1 ∣ xₙ ∣ eml(T,T)</sub>"]
    EMLC["EMLℂ<br/><sub>complex-coefficient<br/>same syntax · ℂ semantics</sub>"]

    F36 -->|"translate?"| EL
    EL  -->|"compile<br/>(structural compiler<br/>Theorem 2)"| EML
    EML -.->|"ι homomorphism<br/>identity on syntax"| EMLC
    F36 ===>|"paper claim<br/>(Theorem 3 — Euler bridges)"| EMLC

    classDef src fill:#fef3c7,stroke:#92400e,color:#92400e
    classDef tgt fill:#dbeafe,stroke:#1e3a8a,color:#1e3a8a
    classDef cpx fill:#ede9fe,stroke:#5b21b6,color:#5b21b6
    class F36 src
    class EL,EML tgt
    class EMLC cpx
```

The headline definition is just three lines:

```
T ::= 1  ∣  xₙ  ∣  eml(T, T)        eml(a, b) := exp(a) − log(b)
```

Everything else — every `+`, every `cos`, every `arctan` — is a fixed-shape sub-tree built from this grammar. See [`notes/proof_structure.pdf`](lambda_lab/proofs/eml/2603_21852/notes/proof_structure.pdf) for the 11-page expository tour.

---

## 📊 Stats dashboard

For the full dashboard with K-count charts, witness-tree size distributions, file-size breakdowns, and a curated tour of the most interesting Lean code, see **[DASHBOARD.md](DASHBOARD.md)**.

A taste:

```mermaid
pie showData
    title K-count distribution across 28 sized witnesses (paper Table 4)
    "≤ 100 (atoms, simple unaries)" : 11
    "100–10 000 (compiled small ops)" : 8
    "10 000–1 000 000 (deep compositions)" : 5
    "> 1 000 000 (logb, div, mul, arcsin, pow)" : 4
```

---

## Curated witnesses

A few terms worth lingering on. Full annotated tour in [DASHBOARD.md § Witness gallery](DASHBOARD.md#witness-gallery).

### `tanCoreTermℂ` — Pro's Cayley quotient

The doubled-angle identity `(e^{2ix} − 1) / (1 + e^{2ix}) = i · tan x` (suggested by an independent GPT Pro code review with no shared context) compresses the `tan` witness to **2 817 nodes**, side-stepping the `e^{ix} + e^{−ix}` `ADDsafeℂ` explosion that had stalled progress for days.

```lean
noncomputable def tanCoreTermℂ : EMLTermℂ :=
  let twoX := mkMulℂ twoPubℂ (.var 0)
  let I2x  := mkMulℂ iTermPubℂ twoX
  let E2   := mkExpℂ I2x
  mkDivℂ (mkSubℂ E2 .one) (mkAddℂ .one E2)
```

### `arcsinTermℂ_open` — pure identity manipulation

The narrow witness `arcsinTermℂ` only handles `0 < x < 1` (its inner `mkMulℂ iTermPubℂ (.var 0)` collides with `arg = π` for `x ≤ 0`). The full open `(−1, 1)` is unlocked by the identity `arcsin x = π/2 − arccos x`, encoding `iπ/2` as `mkLogℂ iTermPubℂ` (since `Complex.log i = iπ/2`):

```lean
noncomputable def arcsinTermℂ_open : EMLTermℂ :=
  mkSubℂ (mkLogℂ iTermPubℂ) arccosTermℂ
```

The full witness has K = 569 297, vs. the narrowed `arcsinTermℂ` at K = 1 704 019 — a **3× compression** as a side-effect of the identity-driven reformulation.

### `EMLTerm.eval?` — the partial-evaluation kernel

The architectural decision that made the whole formalization tractable: instead of fighting Mathlib's total `Real.log 0 = 0` junk value, we work in `Option ℝ` (and `Option ℂ`):

```lean
noncomputable def EMLTerm.eval? (env : Nat → ℝ) : EMLTerm → Option ℝ
  | .one     => some 1
  | .var n   => some (env n)
  | .eml a b =>
      match EMLTerm.eval? env a, EMLTerm.eval? env b with
      | some va, some vb =>
          if 0 < vb then some (Real.exp va - Real.log vb) else none
      | _, _ => none
```

Every nested `eml(_, b)` returns `none` outside its natural mathematical domain (`b ≤ 0`). Bridge theorems are stated as *"if `F36Expr.eval? env e = some v`, then ∃ `t : EMLTerm`, `t.eval? env = some v`"* — we never claim equality at a boundary point, exactly as the paper does.

---

## Quick start

### Prerequisites

```bash
make prereqs              # checks elan, lake, python3, git
```

### Build

```bash
make build                # lake build, ~30–60 min cold cache, seconds incrementally
```

Expected result: `Build completed successfully (8062 jobs).` On a cold Mathlib cache the first build pulls ~6 GB of `olean` files; subsequent builds are incremental.

### Verify what's sealed

```bash
make scoreboard           # lists 48 EML paper_claim theorems + 44 K_count theorems
make sanity               # #checks paper_claim_pi, paper_claim_sin, paper_claim_cos
make stats                # repo-wide statistics
```

### Bootstrap a fresh checkout

A first-time-run recipe is archived at [`process_archive/First_run.md`](process_archive/First_run.md) — reading it executes the full build + memory + sanity + scoreboard sequence and prints a status block. Useful for any new Claude / collaborator joining the project.

---

## Repository layout

| Path | Purpose |
|---|---|
| [`lambda_lab/proofs/eml/2603_21852/`](lambda_lab/proofs/eml/2603_21852/) | The Lean artefact (`lean_workspace/EML/Framework/` is the public API; `notes/` and `report/` for exposition) |
| [`lambda_lab/proofs/eml/2603_21852/lean_workspace/EML/Framework/PaperClaims.lean`](lambda_lab/proofs/eml/2603_21852/lean_workspace/EML/Framework/PaperClaims.lean) | **Public scoreboard.** `#check paper_claim_<f>` to inspect any seal |
| [`lambda_lab/proofs/eml/2603_21852/lean_workspace/EML/Framework/KCounting.lean`](lambda_lab/proofs/eml/2603_21852/lean_workspace/EML/Framework/KCounting.lean) | `rfl`-checked tree sizes for all 36 primitives + companions |
| [`lambda_lab/proofs/eml/2603_21852/lean_workspace/EML/Framework/StructuralLimits.lean`](lambda_lab/proofs/eml/2603_21852/lean_workspace/EML/Framework/StructuralLimits.lean) | The three §G boundary-point counterexamples |
| [`lambda_lab/proofs/eml/2603_21852/report/REPORT.pdf`](lambda_lab/proofs/eml/2603_21852/report/REPORT.pdf) | **Post-frontier technical report (12 May 2026, 11 pp).** Headline-to-handle summary of architecture, what is sealed, frontier sprint, axiom audit. Best single-PDF entry point for a reader who wants the full story without reading the source. |
| [`lambda_lab/proofs/eml/2603_21852/notes/proof_structure.pdf`](lambda_lab/proofs/eml/2603_21852/notes/proof_structure.pdf) | Expository tour of grammars, combinators, and bridges (16 pp) |
| [`lambda_lab/proofs/eml/2603_21852/AUTHOR_SUMMARY.md`](lambda_lab/proofs/eml/2603_21852/AUTHOR_SUMMARY.md) | Author-facing synopsis (Markdown) |
| [`lambda_lab/proofs/eml/2603_21852/OPEN_QUESTIONS.md`](lambda_lab/proofs/eml/2603_21852/OPEN_QUESTIONS.md) | Concrete action plans (Sheffer cleanup, full-real trig, EDL/−EML completeness) |
| [`lambda_lab/proofs/eml/2603_21852/VERIFICATION_EVIDENCE.md`](lambda_lab/proofs/eml/2603_21852/VERIFICATION_EVIDENCE.md) | Build transcript + `#print axioms` output for every headline theorem |
| [`paper/`](paper/) | Canonical paper LaTeX (`EML.tex`, `EML.bib`, figures, `anc/`) + `SupplementaryInformation.pdf` |
| [`eagle_scripts/`](eagle_scripts/) | PCSS Eagle HPC SLURM scripts (`verify_all.sbatch`, `rebuild_cache.sbatch`, …) |
| [`mathematica/`](mathematica/) | Stub pointing at upstream `VA00/SymbolicRegressionPackage` (`VerifyBaseSet`) |
| [`slides/ghostday_post_submission/`](slides/ghostday_post_submission/) | The current post-submission deck reflecting today's sealed status |
| **Live demo:** <https://nasqret.github.io/eml-formalization/> | Interactive in-browser compiler — type a function, see the EML tree built by the same `F36 → EL → EML` macros as the Lean artefact. No install needed. |
| [`web/eml-tree-builder/`](web/eml-tree-builder/) | Source for the live demo above (pure static HTML + JS + CSS; deployed to Pages via `.github/workflows/pages.yml`). |
| [`process_archive/`](process_archive/) | Provenance: Aristotle proof-search chunks, GPT Pro consult bundles, superseded decks, early review bundle, legacy planning notes. **Not part of the verified artefact**, kept for traceability. |

---

## Where to look first

| If you want to… | Start here |
|---|---|
| **Try the EML compiler in the browser** | <https://nasqret.github.io/eml-formalization/> |
| **Read the single-PDF technical summary** | [`report/REPORT.pdf`](lambda_lab/proofs/eml/2603_21852/report/REPORT.pdf) (11 pp, 12 May 2026) |
| **Read the formal claim**, primitive by primitive | [`PaperClaims.lean`](lambda_lab/proofs/eml/2603_21852/lean_workspace/EML/Framework/PaperClaims.lean) |
| **See what's sealed and what isn't** | [Coverage scoreboard ↑](#coverage-scoreboard) and [DASHBOARD.md](DASHBOARD.md) |
| **Understand the architecture in depth** | [`notes/proof_structure.pdf`](lambda_lab/proofs/eml/2603_21852/notes/proof_structure.pdf) (16 pp expository tour) |
| **See what's open** | [`OPEN_QUESTIONS.md`](lambda_lab/proofs/eml/2603_21852/OPEN_QUESTIONS.md) — five concrete plans (A–E) |
| **Get an author-facing synopsis to forward** | [`AUTHOR_SUMMARY.md`](lambda_lab/proofs/eml/2603_21852/AUTHOR_SUMMARY.md) |
| **Re-verify locally** | `make build` |
| **Re-verify on Eagle (PCSS)** | [`eagle_scripts/verify_all.sbatch`](eagle_scripts/verify_all.sbatch) |
| **Bootstrap a fresh Claude session** | [`process_archive/First_run.md`](process_archive/First_run.md) |

---

## Provenance

This repository was extracted from the larger `falenty-2026` workspace on 2026-05-08 via `git filter-repo`, retaining only the paths relevant to the EML formalization and its proof-tooling scaffold. The git history of every retained file is preserved.

---

## Authors and acknowledgements

* **Bartosz Naskręcki** (UAM Poznań / CCAI Warsaw University of Technology) — formalization lead.
* **Andrzej Odrzywołek** (Jagiellonian University) — the source paper. Both for the discovery of the EML operator and for the careful description of the §G boundary issue (paper line 342) which spared us a great deal of confusion when we first hit it in Lean.
* **Aristotle** (Harmonic) — proof search for many individual chunks.
* **GPT Pro** (independent code review, no shared context) — recommended the structural-compiler architecture, the Cayley-quotient route for `tan`, and the public closed-constants packaging.
* **Claude** (Anthropic) — orchestration, scaffolding, post-submission trig widenings.
* **Mathematica / `VerifyBaseSet`** — enumeration and witness candidate search ([upstream repo](https://github.com/VA00/SymbolicRegressionPackage)).
* **Codex** (OpenAI) — paraphrase and informalization.
* **Mathlib community** — the underlying Lean library.

## Licensing

**Dual-licensed.** Code under [Apache License 2.0](LICENSE) (Lean
sources, Python sources, build scripts, web tool); documentation and
narrative prose under [Creative Commons Attribution-ShareAlike 4.0
International](LICENSE-DOCS) (READMEs, DASHBOARD, AUTHOR_SUMMARY,
REPORT.pdf, slide markdown, etc.). The source paper LaTeX in
[`paper/`](paper/) is © Andrzej Odrzywołek and is not covered by
either license here — it is included for reference.

See [`LICENSING.md`](LICENSING.md) for the precise per-file rules
and worked examples.
