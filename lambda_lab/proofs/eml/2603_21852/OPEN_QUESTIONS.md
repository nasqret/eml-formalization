# Open questions & action plans — EML formalization (arXiv:2603.21852)

This file tracks known-open / paper-open / out-of-scope items that the
formalization deliberately does **not** seal, paired with **concrete
action plans** for each feasible direction. The headline
`lake build EML` is sorry-free with respect to the artefact's own scope;
everything below is either a paper-open conjecture, an out-of-scope
direction, or a future-work extension.

## Quick triage

| Direction | Feasibility | Effort | Action plan |
|---|---|---|---|
| **Sheffer cleanup** (align names with paper §3.1) | ✅ **DONE** | — | See [Plan A](#plan-a--sheffer-naming-cleanup-1-2-hours-complete) for the audit trail |
| **Full-real-domain trig** | ✅ **DONE** (Plan C′) | — | `paper_claim_{sin_full, arctan_full, tan_full}` in `PaperClaims.lean` |
| **Full-real-domain trig — custom branch (superseded)** | Not viable | — | [Plan B](#plan-b--full-real-domain-trig-via-custom-branch-1-3-days) — see §B.0 finding |
| **EDL per-primitive completeness** | 🔄 **5/36** | 1–2 wk | [Plan D](#plan-d--edl-per-primitive-completeness-1-2-weeks) — atoms `one`, `var`, `e_const`, `exp x`, `log x` sealed; `−1`, `2`, `1/2` conjecturally unreachable per Schanuel |
| **−EML per-primitive completeness** | 🔄 **2/36** | 1–2 wk | [Plan E](#plan-e--neg-eml-per-primitive-completeness-1-2-weeks) — atoms `one`, `var` sealed; `minusInf` requires switch to `EReal` grammar |
| **§3.2 universal minimality** | Paper-open | — | research result, not a formalization task |
| **§4.3 gradient training** | Out of scope | — | needs Mathlib infrastructure that doesn't exist |
| **Three §G boundary points** | Architectural | — | not closeable in the current grammar |

---

## Paper-open conjectures (the paper itself does not prove these)

### The author's own list — SI §1.5 "Open questions from the search"

The Supplementary Information (page 8) gives an **explicit numbered list
of seven open questions** that the paper itself flags. Our formalisation
does not address any of these — they are research questions in the
author's own framing:

1. **Taxonomy.** "Are EML, EDL, and −EML unrelated, members of a
   discrete family, or random samples from a continuous distribution
   of Sheffer operators?"
2. **Canonical form.** "Can formula enumeration using EML (or one of
   its variants) be made non-repetitive, analogous to the Stern–Brocot
   tree for rationals?"
3. **Constant-free binary Sheffer.** "Does a single binary operator
   exist that generates constants from arbitrary input (no
   distinguished terminal symbol)?" SI §1.4 records a Rust exhaustive
   search (profile B) finding nothing up to operator complexity K = 6.
4. **Leaf-only evaluation.** "Can we find a full binary EML tree for
   any elementary function with inputs restricted to the leaf layer
   only?"
5. **Variable-transplant depths.** "Known identity function has
   depth four, allowing for transplanting variables down the tree by
   multiples of 4. Are there other of this kind, with various depths?"
6. **Real-only Sheffer.** "Does a Sheffer operator exist that works
   purely in the real domain?" Paper §5 (line 540) conjectures
   impossible but offers no proof.
7. **−∞ elimination.** "Can the EML Sheffer, or one of its variants,
   work without use of the extended real axis, −∞ in particular?"

These are paper-open in the strict sense: the author lists them as
future work. Our formalisation operates *downstream* of the EML
operator's discovery — given EML, we mechanically verify its
witnesses for the 36 paper primitives. The seven questions above ask
something about the operator landscape itself.

### Minimality of EML — paper §5 open question

**Status:** paper-open conjecture, posed in paper §5 (Conclusions and
open questions, line 533 of `EML.tex`).

**Where it lives in the paper.** Two related strands:

1. **Operational minimality (paper §2 Methods, line 175).** Ablation
   testing collapses Calc 4 (36 primitives) → Calc 3 → Calc 2 → Calc 1
   → Calc 0 → `{1, eml}`. The endpoint is the EML row of Table 2: one
   constant `1` plus one binary operator `eml`. This is where the
   informal claim "you can't go lower than `{1, eml}`" comes from.

2. **The actual open question (paper §5, line 533).** Verbatim:

   > *"Whether an EML-type binary Sheffer working without pairing with
   > a distinguished constant exists is an open question. Proving such
   > impossibility for any given candidate is non-trivial: one might
   > expect `f(x, x)` being constant to suffice, but consider
   > `B(x, y) = x − y/2`, for which `B(x, x) = x/2` yet
   > `B(B(x, x), x) = 0`. Such traps illustrate why systematic search
   > is essential in this work."*

**The fully universal claim** (what "universal minimality" would mean).
Roughly: for every binary operator `B : ℝ × ℝ → ℝ` (under some
appropriate smoothness / definability constraint) and every constant
`c : ℝ`, if the calculator `{c, B}` reconstructs all 36 paper
primitives then `B = eml` modulo trivial reparameterisation. The paper
does **not** prove this — line 533 explicitly flags it as non-trivial
and gives the `B(x, y) = x − y/2` trap to illustrate why naive arguments
fail.

**What our codebase has.** `lean_workspace/EML/Solutions/029_eml_minimality.lean`
proves two **concrete corollaries** of minimality (no `sorry`):

1. With only the constant `1` and no binary operator, you cannot
   express the identity `x ↦ x`. *(Constant-only calculator is
   constant-functional.)*
2. With one constant `c : ℝ` and one unary `f : ℝ → ℝ` (no variables,
   no binaries), every term evaluates to a constant — so the identity
   is unrepresentable. *(Constant + unary alone is constant-functional.)*

Together these rule out two specific 2-primitive shapes. The chunk's
docstring is explicit:

> *"A fully universal proof would quantify over every conceivable
> 2-primitive calculator design — beyond the scope of this formalisation."*

**Acceptance criterion for closing.** A separate research result. Even
formulating the statement requires picking an appropriate function
class for `B` (smooth? continuous? definable?). A proof would itself
be publishable.

---

### §4.3 — Gradient-based symbolic regression

**Status:** out of scope for the formalization.

**Statement.** The paper (Section 4.3) sketches a gradient-descent
training scheme for EML expression trees: parameterize a binary tree of
EML nodes with simplex weights at each leaf and edge, train via Adam
on observed (input, output) pairs, then snap to the nearest 0/1 vertex
to recover an exact symbolic expression. The paper reports empirical
recovery rates: 100% at depth 2, ~25% at depth 3–4, < 1% at depth 5,
0% at depth 6 (in 448 attempts).

**Why out of scope here.** The training scheme is fundamentally
**numerical** (PyTorch `complex128`, Adam, gradient flow), not symbolic.
Mathlib does not host an optimization-in-Lean framework, so the natural
formalization target — "trained EML weights converge to the symbolic
formula's true minimum" — has no Lean infrastructure to build on.

**What would unblock formalization.** A Lean library for
- gradient flows on parameterized expressions,
- snap-to-vertex projection with convergence guarantees, and
- floating-point ↔ exact-symbolic equivalence after rounding.

None of these exists in Mathlib v4.28.

**Codebase pointer.** No corresponding Lean file. The paper's training
code lives in the upstream `SymbolicRegressionPackage` Mathematica /
Python repository, not in this artefact.

---

## Future-work extensions (deliberately deferred)

### Full-real-domain trig

**Status:** widening companions seal `(-π, π) \ {0}` for `sin`, `arctan`,
`(-π/2, π/2) \ {0}` for `tan`, `ℝ \ {0}` for `cos`, full open `(-1, 1)`
for `arcsin` / `arccos`. The remaining gap is **periodic extension**:
`sin x` for `|x| ≥ π`, `tan x` for `|x| ≥ π/2`, etc.

**Paper claim vs. our formalization.** Paper line 328 states:

> "EML-compiled expressions work on the real axis, both positive and
> negative, except for a few isolated points, especially at zero and
> domain endpoints."

So the paper claims essentially-full-real-domain coverage. The paper's
compiler achieves this by **using a non-standard complex-log branch**
(line 333):

> "A solution working for all real `x ≠ 0` is to redefine the branch for
> EML itself in such a way that `ln z` (and everything derived from it)
> follows standard implementation of principal branch. Another option,
> used in EML compiler, is to manually correct `i` sign."

Our formalization uses Mathlib's `Complex.log` principal branch
unmodified. The narrowing comes from `arg z ∈ (-π, π]` strictness — the
witness's inner expressions stop being well-typed once `arg` hits the
cut.

**What's needed to close this gap (research question).** Two paths:

1. **Custom branch.** Define an EML-internal `ComplexLogEML : ℂ → ℂ`
   that matches the paper's "manually corrected `i` sign" convention,
   and re-derive the witnesses against it. Substantial: each `mkLogℂ`
   eval lemma needs re-proving. Estimated 200–400 lines.

2. **Multi-witness periodicity.** For `sin`, supply one witness per
   fundamental period, indexed by `⌊x / 2π + 1/2⌋`. The bridge is then
   not `∃ t, ∀ x, ...` but `∀ x, ∃ t, ...` (witness-depending-on-input).
   Mathematically straightforward, but architecturally diverges from
   the paper's "single witness per primitive" framing.

**Recommendation.** Worth a GPT Pro consult: ask which path is more
faithful to the paper's intent and which compresses better in Lean.
The paper's compiler effectively does (1) but at the meta-level (manual
sign correction in the compiler output, not in the formal grammar).

---

### Sheffer companions §3.1 — per-primitive completeness

**Status:** scaffolded in `EML.Framework.Sheffer` (grammars + partial
eval + collapse identities). Per-primitive completeness theorems are
**paper-open** for the companions.

**Where in the paper.** Section 3.1 (the "Three Sheffer operators"
block, paper lines 273–284, equation block `\label{Sheffers}`):

```
eml(x, y)   = exp(x) − ln(y)    with constant  1     ← THIS PAPER (proven)
edl(x, y)   = exp(x) / ln(y)    with constant  e     ← cousin, conjectured
−eml(y, x)  = ln(x) − exp(y)    with constant  -∞    ← cousin, conjectured
```

The paper presents EML as the proven complete one; EDL and −EML are
described as **discovered cousins** but their per-primitive
completeness is **not proven in the paper**. From line 273:

> "A month later I realized that it has at least two additional cousins:
> EDL and −EML."

And no Lean-style completeness proof for them. The paper relies on the
empirical `VerifyBaseSet` Mathematica procedure to confirm completeness
for EDL (paper line 287 onwards mentions running the same procedure for
the cousins, but the proof is not given).

**What "per-primitive completeness" would mean.** For each of the 36
paper primitives `f` and each companion `C ∈ {EDL, −EML}`, construct a
literal `CTerm` witness `t_C^f` and prove the closure lemma analogous
to `paper_claim_<f>`. This is a **full parallel sealing effort** — for
each companion, ~30–40 paper-claim theorems, each requiring its own
witness construction (since the EML witnesses do not directly translate;
the operators have different algebraic shape).

**Estimated effort.** Days per primitive per companion. The artefact's
existing `EML.Framework.Sheffer` provides the grammar substrate so that
the proof effort can begin without re-doing the inductive-type
infrastructure.

**Note on the codebase's `Sheffer.lean` (post-Plan-A).** Scaffolding
now hosts exactly the **two paper-named cousins**:
- `EDLTerm` (`edl(x, y) = exp(x) / log(y)`, paper line 281) — matches
  paper exactly.
- `NegEMLTerm` (`negEml(x, y) = log(x) − exp(y)`, paper line 282)
  — matches paper exactly.

The previously-misnamed `LDETerm` (which was *division*, not paper's
*subtraction*) has been replaced; the fabricated binary `T1Term` /
`T2Term` (the paper's actual T₁ / T₂ are **ternary**, SI §1.4) have
been removed. See
[`Sheffer/PaperSourcing.md`](lean_workspace/EML/Framework/Sheffer/PaperSourcing.md)
for line-level paper citations.

---

---

## Concrete action plans

### Plan A — Sheffer naming cleanup (1–2 hours, COMPLETE)

> **Status: ✅ DONE.** `Sheffer.lean` now hosts only the two paper-named
> cousins; `LDETerm` was replaced by `NegEMLTerm` with the correct
> subtraction operator; the fabricated binary `T1Term`/`T2Term` were
> removed; line-level paper sourcing lives in
> [`Sheffer/PaperSourcing.md`](lean_workspace/EML/Framework/Sheffer/PaperSourcing.md);
> README.md, lambda_lab/.../README.md, AUTHOR_SUMMARY.md, and
> DASHBOARD.md updated. `lake build EML.Framework.Sheffer` clean.
> The plan-of-record below is preserved for the audit trail.

**Goal.** Align `EML.Framework.Sheffer` with the paper's actual
companion set. The current scaffolding has four operators; only `EDL`
matches the paper. The other three are misnamed or fabricated relative
to what the paper says.

**Three issues to fix.**

1. **`LDETerm` is not the paper's `−EML`.** Our `lde?(x, y) = log(x) /
   exp(y)` (division). Paper §3 equation (`\label{eml-infty}`):
   `−eml(y, x) = log(x) − exp(y)` (subtraction). These are different
   operators. **Action:** rename `LDETerm → NegEMLTerm` and replace
   `lde?` with:
   ```lean
   def negEml? (x y : ℝ) : Option ℝ :=
     if 0 < x then some (Real.log x - Real.exp y) else none
   ```

2. **`T1Term` and `T2Term` are wrong shape.** The paper's actual T₁ /
   T₂ are **ternary** operators, defined in SI §1.4 (page 8):
   ```
   T₁(x, y, z) = e^(x−y) · ln(x) / ln(z)
   T₂(x, y, z) = e^(x−y) · ln(z) / ln(x)
   ```
   with the property `T₂(x, x, x) = 1` — they generate their own
   constant from arbitrary input, the property the binary EML lacks.
   Our `T1Term`/`T2Term` are *binary* and entirely fabricated.
   **Action:** either (a) replace with a fresh ternary `T1Term3`
   inductive type matching the paper, or (b) remove `T1Term`/`T2Term`
   entirely and document them as "scaffolding error from an earlier
   pass." Recommend (b) — the SI §1.4 explicitly notes ternaries are
   *preliminary unverified candidates*; not worth the effort to
   formalise until the paper firms them up.

3. **No `paper_sourcing.md` next to `Sheffer.lean`.** Add a small
   pointer document citing paper lines 273–284 (the EML/EDL/−EML
   block) and SI §1.4 (page 8, ternary candidates) so the provenance
   is unambiguous to a future reader.

**Steps in order.**

1. Rename `LDETerm → NegEMLTerm` and rewrite `lde? → negEml?` per (1)
   above. Update the collapse identity: in our partial-eval setting,
   `negEml(x, 1) = log(x) − e` for `0 < x` (the paper requires `−∞`
   as constant, but our `negEml(x, 1)` just gives a finite value).
2. Remove `T1Term`, `T2Term` and their helper definitions per (2).
3. Add `EML/Framework/Sheffer/PaperSourcing.md` per (3).
4. Update `README.md` and `AUTHOR_SUMMARY.md` to reflect three
   Sheffers (EML, EDL, −EML) and to cite the SI §1.4 ternary
   candidates as preliminary future work, not as part of our
   scaffolding.

**Acceptance.** `lake build EML` clean; `NegEMLTerm` collapse identity
proved; README and author summary cite paper line numbers correctly;
no fabricated operators remain in the scaffolding.

---

### Plan B — Full-real-domain trig via custom branch (1–3 days)

> **Status update (2026-05-08): architectural finding documented below.**
> The original "custom log branch" framing turns out to *not* be
> implementable as a different log function — the EML grammar's eval
> rule is hard-coded to use Mathlib's principal `Complex.log` (see
> `Framework/Complex/Term.lean:34`). What's actually feasible (and what
> the paper's compiler effectively does) is the more subtle `2πi`-shift
> insight in §B.0 below, which is structurally equivalent to Plan C —
> i.e. **Plans B and C describe the same underlying mathematics in two
> different presentations.** Plan C is the cleaner Lean formulation;
> Plan B is the paper-faithful framing of the same construction.

#### §B.0 — The actual architectural finding

The `EMLTermℂ` grammar's eval rule is fixed in `Framework/Complex/Term.lean`:
```lean
| .eml a b =>
    match ..., ... with
    | some va, some vb =>
        if vb = 0 then none else some (Complex.exp va - Complex.log vb)
    ...
```
There is **no way** to inject a different `log` branch from inside the
EML term language — every `eml(_, b)` evaluates with Mathlib's principal
`Complex.log`. The macro `mkLogℂ T = eml(1, eml(eml(1, T), 1))` reduces
to `Complex.log v` only when `arg(T.eval) ∈ (-π, π)` strictly, by way of
`Complex.log_exp`'s `w.im ∈ (-π, π]` constraint with `w = e − log v` and
`w.im = -arg v`.

**At the cut `arg v = π` exactly** (i.e. `v` a negative real), the
macro is *still* evaluable — `Complex.log` is total — but the value is
**`Complex.log v − 2πi`**, not `Complex.log v`. The `−2πi` arises
because `Complex.log_exp` then steps to the next Riemann sheet:
`log(exp w) = w + 2πi` for `w.im = −π`, and the macro's outer
subtraction propagates this as a `−2πi` shift in the result.

**Why `cos` already covers `ℝ ∖ {0}`.** `cosTermℂ = mkExpℂ (mkExpℂ
(.eml cosLhsℂ cosRhsℂ))` — its outermost layer is an `exp`. Any `2πi`
shift inside the inner log calls is absorbed by `exp(z + 2πi) = exp z`.
So `cos` extends across the cut **for free**, which is why the existing
`paper_claim_cos` already lives on `ℝ ∖ {0}` rather than just `(0, ∞)`.

**Why `sin`, `arctan`, `tan` don't.** Their witnesses' final operation
involves an `mkLogℂ` whose imaginary part is the answer (e.g. `arctan`'s
witness is `mkLogℂ (1 + i·x) / 2`, with `arctan x = (eval).im`). A
`−2πi` shift in the final log makes `(eval).im` differ from
`Real.arctan x` by `−2π`. The paper's "manual `i`-sign correction" is
the meta-level operation of choosing a different witness shape (one
that *doesn't* go through the cut) for inputs in different regions —
which is exactly Plan C's witness-family construction.

#### §B.1 — Reformulated Plan B (= Plan C in Plan B's clothing)

A plan-B-faithful formulation: *for each x ∈ ℝ \ (excluded points), pick
a witness `t_x : EMLTermℂ` whose intermediate evaluations stay in
`{ z : ℂ | arg z ∈ (-π, π) }` (i.e. avoid the cut), such that
`t_x.eval? env_x` projects to `Real.sin x` (resp. `cos`, `arctan`,
`tan`).*

This is **exactly** Plan C's `∀ x, ∃ t_x, ...` framing, with the
"different witness shapes" justified by the paper's prose ("manual
i-sign correction") rather than by abstract periodicity. The
mathematical content is identical to Plan C.

**Recommendation.** Treat Plan B as the **paper-faithful narrative** of
Plan C. Implementation lives in Plan C below; Plan B is the
documentation that explains why this is what the paper meant. No
separate Plan-B-only deliverable is feasible without changing the EML
grammar's eval rule (which would be off-paper).

**Acceptance for "Plan B style" claims.** The same as Plan C:
`paper_claim_sin_full : ∀ x : ℝ, x ≠ 0 ∧ x ≠ ±π ∧ ... → ∃ t : EMLTermℂ,
∃ vc, t.eval? env_x = some vc ∧ vc.re = Real.sin x`. Whether the
witness is *presented* as a single witness with a custom branch (Plan B
narrative) or as a family `(t_k)_{k:ℤ}` with periodicity reduction
(Plan C narrative) is a documentation choice; the Lean artefact is
identical.

---

### Plan C — Full-real-domain trig via multi-witness periodicity (2–3 days)

**Goal.** Same coverage as Plan B but using a **family of witnesses**
indexed by period number, rather than a single witness with a custom
branch. Tradeoff: weakens the existential from `∃ t, ∀ x, ...` to
`∀ x, ∃ t, ...` (the witness depends on the input).

**Approach.**

1. **Define witness-family theorem.** For `sin`:
   ```lean
   theorem sin_witness_family : ∀ x : ℝ, x ≠ 0 →
     ∃ t : EMLTermℂ, ∃ vc : ℂ,
       t.eval? (fun n => if n = 0 then ((x : ℝ) : ℂ) else 0) = some vc ∧
       vc.re = Real.sin x
   ```
   Proof goes by case analysis on `⌊x / 2π + 1/2⌋ : ℤ`:
   - For `k = 0` (i.e., `x ∈ (-π, π)`): use existing `sinTermℂ` /
     `sinTermℂ_neg`.
   - For `k ≠ 0`: build a fresh witness using
     `sin x = sin(x − 2πk)` and re-route through the same machinery
     after symbolic shift. The shifted input is in `(-π, π)`, so
     the existing witnesses apply.

2. **The shift witness.** For `k = 1` (input `x ∈ (π, 3π)`), construct
   `sinTermℂ_shifted_1` whose evaluation at `x` equals `sinTermℂ`'s
   evaluation at `x − 2π`. Mechanically, this means substituting
   `(.var 0)` with an EMLTermℂ encoding `(.var 0) − 2π`. The
   subtraction-by-constant is a real-EL term, lifted to ℂ via
   `EMLTerm.toComplex`.

3. **Generalize over k.** A single Lean theorem parameterized by `k :
   ℤ` covers all shifts. `arctan`, `tan` follow the same pattern
   (with their own period: `π`, not `2π`).

4. **Bridge.** Compose with `Real.sin_periodic`,
   `Real.tan_periodic`, etc. (already in Mathlib).

**Tradeoff vs. Plan B.** This produces a **family of witnesses**
indexed by the period, not a single witness. The paper's framing is
"single witness per primitive", so this is less faithful. But it is
**fully constructive in Lean** without a custom branch, and the proof
is mechanical extension of existing infrastructure.

**Acceptance.** `sin_witness_family`, `cos_witness_family`,
`arctan_witness_family`, `tan_witness_family` covering full real
domain (modulo isolated singularities for tan).

---

### Plan D — EDL per-primitive completeness (1–2 weeks)

**Goal.** For each of the 36 paper primitives `f`, construct a literal
`EDLTerm` witness `t_f` and prove `paper_claim_edl_<f> : ∃ t, ∀ env, ...`
analogous to the existing `paper_claim_<f>` for EML.

**Approach.**

1. **EDL atoms (~3–4 hours).** `paper_claim_edl_{var, one, e_const}` —
   the constant `e` is required because EDL needs `e` to "neutralize"
   `log y`: `edl(x, e) = exp(x) / log(e) = exp(x)`. Build small
   atoms first.

2. **EDL exponential & logarithm (~half day).** `exp x = edl(x, e)`.
   `log y = ?` — non-trivial because `log y` is not a one-step EDL
   identity. Likely `log y = edl(0, edl(0, y))` or similar; need
   systematic enumeration.

3. **EDL arithmetic (~3–5 days).** Subtraction, addition,
   multiplication, division. Each requires a fresh witness search.
   The paper's `VerifyBaseSet` Mathematica tool **could be used as a
   witness oracle**: input "find an EDL term for `x + y`" and it
   returns a candidate, which we then formalize.

4. **EDL trig family (~5+ days).** Hardest. The paper does not provide
   explicit EDL witnesses for `sin`, `cos`, etc. Likely requires
   complex-EDL extension parallel to our `EMLTermℂ`.

5. **EDL Table 4 K-counts.** Once witnesses land, `EDL_KCounting.lean`
   parallel to `KCounting.lean` machine-checks tree sizes.

**Risk.** EDL witnesses are not given in the paper; they must be
**discovered**. The Mathematica package can serve as the witness
oracle, but each candidate still needs Lean-side formalization.

**Recommended split.** Spawn `Aristotle` jobs in parallel for the
identity-style EDL witnesses (atoms + exp + log). The arithmetic and
trig require a more deliberate witness-search loop.

---

### <a name="plan-c-prime--gpt-pro-recommendation-in-progress"></a>Plan C′ — GPT Pro recommendation, in progress

> **Plan-of-record for full-real-domain trig.** Refines Plan C with
> GPT Pro's specific recommendations (see
> [`gpt_pro_bundle/trig_widening/RESPONSE.md`](../../../gpt_pro_bundle/trig_widening/RESPONSE.md)
> for the verbatim consult). Rejects Path A (boundary lemmas) and
> Path B (Euler-form reshaping) as global strategies; keeps the
> witness-substitution architecture from Plan C but generalises it.

**Four sub-paths**, one per primitive:

1. **`sin x`** via `cos(π/2 − x)`. The existing `cosTermℂ` already
   covers `ℝ ∖ {0}`; substituting `(π/2 − x)` for `var 0` gives a
   full-real-domain `sin` witness for all `x ≠ π/2`. Isolated point
   `x = π/2`: use `.one` constant witness (since `sin(π/2) = 1`).

2. **`arctan x`** via `Real.arctan_eq_arcsin : arctan x = arcsin(x / √(1+x²))`.
   The existing `arcsinTermℂ_open` already covers full open `(−1, 1)`;
   the input `x / √(1+x²)` is in `(−1, 1)` for all `x ∈ ℝ`. Build a
   real-fragment compiled term for the input, lift via `.toComplex`,
   substitute into `arcsinTermℂ_open`. **`arcsin` projects to `.im`,
   so the arctan paper-claim follows the same convention.**

3. **`tan x`** via period-`π` reduction. Reduce arbitrary `x` (with
   `cos x ≠ 0`) to the fundamental domain `(−π/2, π/2)` via repeated
   real-safe addition of `±π`, then apply existing `tanCoreTermℂ` /
   `tanCoreTermℂ_neg`. Witness depends on `k = round(x/π) : ℤ`.

4. **`cos x`** is already complete on `ℝ ∖ {0}` — no extension needed.

**The engineering move.** Build period shifts using **repeated
`mkAddℂ`** with fixed real-period constants — never `mkMulℂ` an
integer by `π`. This keeps every shift in the real fragment, so the
`arg = π` boundary trap never appears. The foundation is one lemma:

```lean
lemma ADDsafeℂ_ofReal_ofReal (a b : ℝ) :
    ADDsafeℂ ((a : ℝ) : ℂ) ((b : ℝ) : ℂ)
```

When both arguments are real-valued, the 11-condition `ADDsafeℂ`
bundle holds automatically: 9 `.im = 0` inequalities trivially in
`(−π, π]`, plus non-vanishing of `Real.exp a − a` (via
`Real.add_one_le_exp`).

**Status (2026-05-08):**

- ✅ `EMLTermℂ.subst0` + `eval?_subst0` — substitution machinery
  (in `Framework/Complex/Subst.lean`)
- ✅ `ADDsafeℂ_ofReal_ofReal` — foundation for real-safe addition
  (in `Framework/Complex/Periodicity.lean`)
- ✅ `eval?_mkAddℂ_ofReal` — packaged form (no side conditions)
- ✅ `twoPiPubℂ` + `eval?_twoPiPubℂ` — first concrete witness; validates
  the foundation end-to-end (~30 lines vs. ~80 without the helper)
- ⏳ `negPiPubℂ` — negative-π constant for shift-term construction
- ⏳ `shiftByPeriodℂ : ℤ → EMLTermℂ` — recursive period shift
- ⏳ `eval?_shiftByPeriodℂ` — induction on `k`
- ⏳ `sinViaCosℂ`, `arctanViaArcsinℂ`, `tan_full` — witness families

**Effort remaining.** ~3–5 days of mostly mechanical proof work, much
compressed by `ADDsafeℂ_ofReal_ofReal` and `eval?_subst0`. The
substantial design questions are settled; what's left is
identity-driven plumbing.

---

### Plan E — `−EML` per-primitive completeness (1–2 weeks)

**Goal.** Parallel to Plan D, for the third Sheffer cousin
`−EML(y, x) = ln(x) − exp(y)` paired with constant `−∞`.

**Approach mirrors Plan D** but with two complications:

1. **`−∞` is not a real number.** The paper handles `−∞` symbolically
   (via Mathematica's symbolic processing) or via floating-point
   conventions (`exp(−∞) = 0`). In Lean, our partial-eval framework
   does not natively support `−∞` as a constant. Two options:
   - Use Mathlib's `EReal` (extended reals) for the `−EML` grammar.
   - Work around `−∞` by inlining the limiting identity at the witness
     level (e.g., wherever `−∞` would be needed, use a sufficiently
     large finite negative — but this makes the witness no longer a
     *finite* term in the paper's sense).

2. **The constant requirement.** The paper requires `−∞` as a terminal
   symbol. In Lean we'd need to pick a representation: `EReal.bot` is
   the natural choice; a separate `MinusInftyTerm : NegEMLTerm` constructor
   with `eval? env _ = some EReal.bot`.

**Acceptance.** Parallel `paper_claim_negEml_<f>` family.

---

## Three structural boundary points (§G — junk-value collision)

**Status:** documented in `EML.Framework.StructuralLimits`. Not sealable.

`√0`, `arcosh 1`, `hypot(0, 0)` — three measure-zero corners where the
natural EML construction collides with Mathlib's convention `Real.log 0
= 0` (the "junk value"). The paper itself does not supply EML terms for
these either (see paper line 342: "Lean ... assigns the complex
logarithm at zero a default 'junk value', causing the straightforward
formalization of the EML chain to fail").

**Why not closeable.** Every natural EML witness for `√x` is built as
`exp((1/2) · log x)`, which evaluates to `1` at `x = 0` (because
`log 0 = 0`), not `0`. Composites that internally feed `√` a value of
`0` (`arcosh(1)` via `√(1²−1)`, `hypot(0, 0)` via `√(0² + 0²)`) inherit
the same collision.

A complete fix would require either:
1. Extending the EML grammar with a primitive `Real.rpow` constructor
   (~400 new lines, off-paper),
2. Or moving each affected witness into the complex extension where the
   junk-value boundary is in different coordinates.

Neither is on the paper's roadmap.
