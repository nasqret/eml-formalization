# EML formalisation — author-facing summary

> A synopsis of what has been formally verified in Lean 4 + Mathlib v4.28
> for the paper *"All elementary functions from a single binary operator"*
> (A. Odrzywołek, arXiv:2603.21852), with notes on what surprised us,
> what remained out of reach, and where the formalisation aligns or
> diverges from the paper's own approach.

**Status as of 2026-05-07.** `lake build EML` → 8 054 jobs, sorry-free,
clean. The headline result is a literal `EMLTermℂ` (or real-fragment
`EMLTerm`) witness for **every one of the 36 paper primitives**, on a
non-empty open subdomain of its natural mathematical domain. Three
boundary points (`√0`, `arcosh 1`, `hypot(0, 0)`) are documented as
**§G structural limits** that fall outside the natural construction —
the paper itself does not exhibit EML terms for them either.

---

## What is sealed

### Atoms (7 of 7) — full domain
`paper_claim_{var, one, negOne, two, half_const, e_const, pi}` plus
`paper_claim_i`. Each is a one-line existential whose witness is a
concrete, machine-checked `EMLTerm` or `EMLTermℂ` tree.

### Real unaries (8 of 8) — full natural domain bar `√0`
`paper_claim_{exp, log, inv, half, minus, sqr, sigma}` on full domains;
`paper_claim_sqrt_pos` on `(0, ∞)`. The boundary `x = 0` for `√` is the
§G junk-value collision.

### Hyperbolic (6 of 6) — full natural domain bar `arcosh 1`
`paper_claim_{sinh, cosh, tanh, arsinh, artanh}` on full domains;
`paper_claim_arcosh` on `(1, ∞)`.

### Binary (8 of 8) — full natural domain bar `hypot(0, 0)`
`paper_claim_{add, sub, mul, div, avg, pow, logb}` on full domains;
`paper_claim_hypot` on `ℝ² \ {(0, 0)}`.

### Trig (6 of 6) — wide subdomains via paired companion witnesses
| Primitive | Sealed subdomain | Construction |
|---|---|---|
| `cos` | `ℝ \ {0}` | `cosTermℂ` (positive) + `cosTermℂ_neg` (`cos(−x) = cos x`); `cos 0 = 1` via `.one` |
| `sin` | `(-π, π) \ {0}` | `sinTermℂ` (positive) + `sinTermℂ_neg` (uses `sin x = cos(π/2 − x)`, `log(−i) = −iπ/2`); `sin 0 = 0` via `zeroPubℂ` |
| `tan` | `(-π/2, π/2) \ {0}` | `tanCoreTermℂ` (Cayley quotient) + `tanCoreTermℂ_neg` (swap-numerator Cayley); `tan 0 = 0` via `zeroPubℂ` |
| `arctan` | `(-π, π) \ {0}` | `arctanTermℂ` (positive) + `arctanTermℂ_neg` (`1 + ix = 1 − i·(−x)`); `arctan 0 = 0` via `zeroPubℂ` |
| `arccos` | full open `(-1, 1)` | `arccosTermℂ` |
| `arcsin` | full open `(-1, 1)` | `arcsinTermℂ` (`(0, 1)` direct) and `arcsinTermℂ_open` (full, via `arcsin x = π/2 − arccos x`) |

All trig witnesses are **literal `EMLTermℂ`** trees, not real-part
projections of opaque complex objects: each evaluates partially in
`Option ℂ` to a value whose `.re` (for `cos`, `sin`) or `.im` (for
`arctan`, `arccos`, `arcsin`, `tan`) equals the paper's stated real
value on the sealed subdomain.

### Closed numeric and imaginary constants (5)
`realizeℂ_{zero, two, negI, i, pi}` — public, reusable
`EMLRealizationℂ` packages used as building blocks across the trig
witnesses.

### Witness-tree sizes (paper Table 4)
All 36 primitives + 5 widening-companion witnesses have `rfl`-checked
tree sizes (`EML.Framework.KCounting`). For the hand-tuned closed
constants (`zero`, `two`, `−i`, `i`, `π`) our K-counts match the paper
to the unit. For compiler-produced witnesses (`exp`, `log`, …, the
Cayley `tan`) our K is **larger** than the paper's hand-tuned figures —
because our witnesses are produced by a single structural-compiler
theorem rather than per-primitive optimisation. We treat the gap as
informative: the paper's hand-tuned figures are an *upper bound on the
necessary tree size*, and we machine-check the actual size of the
mechanically-produced witness.

---

## Architectural choices and what they cost

The Lean kernel is total (`Real.log 0 = 0`, the "junk value"). Three
consequences:

1. **`EMLTerm.eval?` is `Option ℝ`-valued partial evaluation.** Every
   nested `eml(a, b)` returns `none` outside its natural mathematical
   domain (e.g., `b ≤ 0`). The bridge theorems are stated as
   "if `F36Expr.eval? env e = some v`, then there exists an EMLTerm `t`
   with `t.eval? env = some v`" — i.e., we never claim equality at a
   boundary point.

2. **Three §G boundary points** (`√0`, `arcosh 1`, `hypot(0, 0)`) are
   structurally outside the natural witness. The paper's prose
   (line 342 of `EML.tex`) explicitly remarks on this Lean-specific
   issue:
   > "the Lean 4 proof assistant takes a different approach. Because
   > Lean requires all functions to be total, it assigns the complex
   > logarithm at zero a default 'junk value' (`Complex.log 0 = 0`),
   > causing the straightforward formalization of the EML chain to
   > fail."
   We document each of the three with machine-checked counterexample
   artefacts in `EML.Framework.StructuralLimits`.

3. **Trig narrow vs. paper's "all real x ≠ 0".** Paper line 328 claims
   essentially full real-domain coverage. The paper's compiler
   achieves this by **not using the standard principal branch** —
   line 333: *"Another option, used in EML compiler, is to manually
   correct `i` sign."* Our Lean originally used Mathlib's `Complex.log`
   unmodified and widened only to symmetric subdomains around 0 via
   negative-side companions. Post-submission, **Path C′ closed the
   remaining gap**: range-reduction by substitution (sin via cos(π/2−x),
   arctan via arcsin(x/√(1+x²)), tan via period-π reduction) brings
   `paper_claim_{sin_full, arctan_full, tan_full}` to their full
   natural domains. See `OPEN_QUESTIONS.md` Plan C′ for the
   construction; Plan B (custom log branch) was found architecturally
   infeasible — §B.0 documents why.

---

## What surprised us

0. **The paper itself notes prior Lean attempts failed.** SI Part II §2
   (page 9) records:
   > *"A natural next step would be formalization in Lean 4, but
   > preliminary AI-assisted attempts failed; the extended-value
   > conventions (`ln 0 = −∞`) and branch-cut reasoning required appear
   > to exceed current automation capabilities."*
   What our artefact gets working — modulo the three §G boundary points
   and the trig-narrowing-vs-paper-line-333 mismatch documented above —
   is essentially what the SI flags as exceeding automation. The
   architectural shifts that unlocked this (partial-eval `Option ℝ` to
   sidestep `ln 0 = 0` junk, real-fragment compositional compiler for
   the bulk, complex-grammar `EMLTermℂ` extension for trig) are
   summarised in §3 of the README and worth a careful read before
   accepting our claims at face value.

1. **Pro's Cayley quotient unblocks `tan`.** The doubled-angle form
   `(e^{2ix} − 1) / (1 + e^{2ix}) = i · tan x` (recommended by an
   independent GPT Pro code review with no shared context) avoids the
   `e^{ix} + e^{-ix}` `ADDsafeℂ` explosion that had stalled progress
   for several days. The witness compresses to 2 817 nodes (vs. tens
   of thousands for naive constructions).

2. **`arcsin` widens to full open `(−1, 1)` via `arccos`.** Pure
   identity manipulation: `arcsin x = π/2 − arccos x`. Encoding `iπ/2`
   as `mkLogℂ iTermPubℂ` (because `Complex.log i = iπ/2`) gives a
   clean term whose imaginary part picks up `arcsin x` for **every**
   `x ∈ (−1, 1)`, including the previously narrow negative side.

3. **The `arg < π` barrier is *the* universal blocker.** Across
   `arcsin`, `arctan`, `cos`, `sin`, `tan`, every narrow domain came
   from a single architectural constraint: the `mkLogℂ T` builder
   requires `arg(T.eval) < π` strictly. That constraint propagates
   through `mkMulℂ`, blocking any witness that needs to multiply by
   `i · x` for non-positive real `x`. **The same toolkit cracks all
   five widenings:** a real-EL `−x` lifted to ℂ via the homomorphism
   `EMLTerm.toComplex`, plus identity-driven witness restructuring, in
   ~30–50 lines per primitive.

4. **Witness-tree sizes vary by 7 orders of magnitude.** From `K = 7`
   for `0` to `K = 9 929 087` for the compiler-produced `logb`. The
   paper's Table 4 lists hand-tuned values where available; our
   machine-checked counterparts are systematically larger because the
   structural compiler is uniform-by-design and unoptimised.

---

## What remains open

### Paper-open conjectures (the paper itself does not prove these)

The Supplementary Information (SI §1.5, page 8) gives an explicit
numbered list of seven open questions. We do not address any of these
— they are research questions about the operator landscape, not about
witness construction:

1. Taxonomy of EML, EDL, −EML — discrete family or continuous
   distribution?
2. Canonical-form / non-repetitive enumeration analogue of the
   Stern–Brocot tree.
3. **Constant-free binary Sheffer.** Does one exist? SI §1.4 records a
   Rust exhaustive search (profile B) finding nothing up to operator
   complexity K = 6.
4. Leaf-only-input full binary EML tree for any elementary function.
5. Variable-transplant depths (the identity has depth 4; what other
   depths exist?).
6. **Real-only Sheffer.** Paper §5 (line 540) conjectures impossible:
   *"A continuous Sheffer working purely in the real domain seems
   impossible."* No proof.
7. **−∞-free EML or variant.** Can EML or one of its cousins work
   without using the extended real axis?

**Minimality (paper §5, line 533).** The "informal" minimality claim
that the EML row of Table 2 (`{1, eml}`) cannot be reduced further is
the strongest concrete statement, but the *fully universal* version —
quantifying over every conceivable 2-primitive calculator design — is
explicitly flagged as non-trivial: the paper gives the trap example
`B(x, y) = x − y/2` with `B(x, x) = x/2` yet `B(B(x, x), x) = 0`.
Our `lean_workspace/EML/Solutions/029_eml_minimality.lean` proves two
**concrete corollaries** (constant-only and constant-plus-unary
calculators are constant-functional), no `sorry`. The fully universal
claim is left as a research question.

**§4.3 — gradient-based symbolic regression.** The paper's training
scheme (Section 4.3) is fundamentally numerical. There is no Mathlib
infrastructure for gradient flow / projection / floating-point ↔
symbolic equivalence. **Out of scope for this formalisation.**

### Future-work extensions (deliberately deferred)
* **Full-real-domain trig — DONE (Plan C′ complete).** The paper's
  claim (line 328) of essentially-full-real-domain coverage for sin,
  arctan, tan is now sealed via three witness-family theorems
  (`paper_claim_sin_full`, `paper_claim_arctan_full`,
  `paper_claim_tan_full`). The construction follows GPT Pro's Path C′
  recommendation: real-safe period shifts via repeated `mkAddℂ`
  (foundation: `ADDsafeℂ_ofReal_ofReal`), substitution of the shifted
  argument into the existing local witness via
  `EMLTermℂ.subst0`, and Mathlib identities (`Real.cos_pi_div_two_sub`
  for sin via cos, `Real.arctan_eq_arcsin` for arctan via arcsin,
  `Real.tan_sub_int_mul_pi` for tan via period-π reduction).
  Plan B (custom log branch) was found architecturally infeasible —
  the EML grammar's eval rule hard-codes Mathlib's principal
  `Complex.log`. See `OPEN_QUESTIONS.md` §B.0 for the finding and
  GPT Pro consult bundle (`gpt_pro_bundle/trig_widening/`) for the
  reasoning.
* **Sheffer companions — per-primitive completeness for EDL and −EML.**
  The paper presents EML, EDL, and −EML as a "family" (paper §3,
  equation block `\label{Sheffers}`) but proves completeness only for
  EML; the cousins are confirmed empirically via the Mathematica /
  Rust `VerifyBaseSet` procedure. A full parallel sealing effort for
  either cousin is **1–2 weeks per cousin**. Plans D and E in
  `OPEN_QUESTIONS.md`. **Plan D — IN PROGRESS:** 5 of 36 paper
  claims sealed (`edl_paper_claim_{one, var, e_const, exp, log}`).
  D8 / log x is non-trivial — Aristotle (chunk 085) discovered the
  three-step composition `edl one (edl (edl one (var 0)) e_const)`.
  Constants `−1`, `2`, `1/2` appear conjecturally unreachable from
  closed EDL terms (Aristotle's Schanuel-conjecture analytical note).
  Trig and hyperbolic primitives blocked by addition unreachability.
* **Sheffer naming cleanup — DONE (Plan A complete).** Our scaffolding
  now has exactly the **two paper-named cousins** (`EDL` and `−EML`)
  matching paper §3.1 (lines 273–284). The previously-misnamed
  `LDETerm` (which was `log(x)/exp(y)` division, *not* the paper's
  `−EML = log(x) − exp(y)` subtraction) has been replaced by the
  correct `NegEMLTerm`. The fabricated binary `T1Term`/`T2Term` (the
  paper's actual T₁/T₂ are **ternary** — SI §1.4, page 8:
  `T₁(x, y, z) = e^(x−y) ln x / ln z`,
  `T₂(x, y, z) = e^(x−y) ln z / ln x`, with the special property
  `T₂(x, x, x) = 1`) have been removed; the SI flags them as
  *preliminary unverified candidates* for the constant-free Sheffer
  open question (SI §1.5 #3) and they are out of scope for this
  formalisation. See
  [`Sheffer/PaperSourcing.md`](lean_workspace/EML/Framework/Sheffer/PaperSourcing.md)
  for the full audit trail.

### Three §G boundary points (architectural)
`√0`, `arcosh 1`, `hypot(0, 0)` — Mathlib's `Real.log 0 = 0` makes
these unsealable in the natural EML construction. The paper does not
provide explicit EML terms either. Documented with concrete
counterexamples in `EML.Framework.StructuralLimits`.

---

## Re-verification

```bash
cd lambda_lab/proofs/eml/2603_21852/lean_workspace
lake build       # local re-verify; ~8 054 jobs
```

The `EML.lean` root imports `EML.Framework.PaperClaims` (the public
scoreboard), `EML.Framework.StructuralLimits` (boundary documentation),
`EML.Framework.KCounting` (Table 4 K-counts), and
`EML.Framework.Sheffer` (§3.1 companion grammar scaffolding).

PCSS Eagle HPC re-verify (job 7 041 555, May 7 2026): 88 files, 0 fail,
42 s.

---

## Acknowledgements

* **Andrzej Odrzywołek** (Jagiellonian University) — the source paper.
  Thanks for both the discovery of the EML operator and for the careful
  description of the §G boundary issue (paper line 342) which spared us
  a great deal of confusion when we first hit it in Lean.
* **Bartosz Naskręcki** (UAM Poznań / Politechnika Warszawska) —
  formalisation lead.
* **Aristotle** (Harmonic) — proof search for many individual chunks.
* **GPT Pro** — independent code review (separate-context); recommended
  the structural-compiler architecture, the Cayley-quotient route for
  `tan`, and the public closed-constants packaging.
* **Claude** (Anthropic) — orchestration, scaffolding, post-submission
  trig widenings.
* **Mathematica** — enumeration and witness candidate search.
* **Codex** (OpenAI) — paraphrase and informalisation.
* **Mathlib community** — the underlying Lean library.

---

## Pointers

* `README.md` — repo entry point with build instructions.
* `OPEN_QUESTIONS.md` — concrete action plans for every feasible
  extension.
* `lean_workspace/EML/Framework/PaperClaims.lean` — the public
  scoreboard. Each `paper_claim_<f>` is a one-line existential a reader
  can `#check`.
* `lean_workspace/EML/Framework/StructuralLimits.lean` — the §G boundary
  point documentation.
* `lean_workspace/EML/Framework/KCounting.lean` — `rfl`-checked Table 4.
* `lean_workspace/EML/Framework/Sheffer.lean` — §3.1 companion grammar
  scaffolding (per-primitive completeness deferred).
