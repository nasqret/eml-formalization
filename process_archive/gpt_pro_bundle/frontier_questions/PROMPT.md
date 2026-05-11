# GPT Pro consult — four frontier directions in the EML formalisation

## What we want from you

We have a Lean 4 + Mathlib v4.28 formalisation of arXiv:2603.21852
(Odrzywołek, *"All elementary functions from a single binary operator"*).
36/36 paper primitives are sealed end-to-end for EML, sorry-free; the
trig-widening question (your earlier consult, in `gpt_pro_bundle/trig_widening/`)
is now closed via Plan C′. What remains is **four research-grade
directions** that are not within-reach engineering and that we want
your independent triage on. Sub-questions Q1/Q2/Q3 follow each direction.

A glance at `CODE_EXCERPTS.md` is enough; you do not need repo access.

---

## Project architecture (90 seconds)

```
F36Expr  --- 36-primitive source language (paper's named constructors)
   │
   │  translate?
   ▼
ELExpr  --- exp/log/arithmetic intermediate (real)
   │
   │  ELExpr.compile (structural compiler — Theorem 2)
   ▼
EMLTerm  --- pure single-operator grammar T ::= 1 ∣ xₙ ∣ eml(T, T)
              eml(a, b) := exp(a) − log(b)
   │
   │  ι : EMLTerm → EMLTermℂ (homomorphic embedding)
   ▼
EMLTermℂ  --- complex-coefficient version, same syntax, ℂ semantics
              eml.eval = Complex.exp(a) − Complex.log(b)
```

**Sheffer cousins** (paper §3.1) — same single-binary-operator-plus-one-
constant shape, paper-conjectured complete:

| Companion  | Operator                          | Constant   | Status                         |
|------------|-----------------------------------|------------|--------------------------------|
| **EML**    | `eml(x, y) = exp(x) − log(y)`     | `1`        | proven complete for 36 prims   |
| **EDL**    | `edl(x, y) = exp(x) / log(y)`     | `e`        | conjectured; **8/36 sealed**   |
| **−EML**   | `−eml(y, x) = log(x) − exp(y)`    | `−∞`       | conjectured; **5/36 sealed**   |

Each `paper_claim_<f>` is a one-line existential

```
∃ t : EMLTermℂ, ∀ env : ℕ → ℂ, t.eval? env = some (paper_value)
```

(or its `EMLTerm`/`EDLTerm`/`NegEMLTerm`/`NegEMLTermE` analogue) with
`eval?` partial (`Option <T>`) and `none` exactly when a sub-expression
hits its junk-value boundary.

---

## Direction (1) — Schanuel-style structural ceiling for Plan D / E

### Background

The artefact has **8/36 EDL primitives** (`one`, `var`, `e_const`,
`exp x`, `log x`, `x/y`, `exp(exp x)`, `log(log x)`) and **5/36 −EML
primitives** (`one`, `var` over ℝ, plus `one_E`, `var_E`, `minusInf`
in the `NegEMLTermE` EReal pilot) sealed.

The remaining 28 EDL primitives (and 31 −EML primitives) appear
**unreachable from closed terms** because the cousin grammars provide
no addition mechanism. In EML, the structural compiler reaches addition
by composing `mul x y = exp(log x + log y)` over the dedicated 9-node
`mkAdd` term; that route uses both `exp` and `log` as outer operators.

In EDL, the combinator `edl(a, b) = exp(a) / log(b)` only ever
*divides* `exp` by `log`. There is no clean way to compose `edl`-trees
to express "value-of-`a` plus value-of-`b`": every closed EDL tree
collapses to a quotient of compositions of `exp`/`log` rooted at the
constants `1`, `e`. Numerically the empirical search (paper §3.1, the
Mathematica `VerifyBaseSet`) does find approximations of negatives and
`2` and `½` for small expression sizes, but no exact witnesses — these
appear to live "outside" the closure under `edl`.

### Aristotle's analytical commentary (chunk 085)

Chunk `lambda_lab/proofs/eml/2603_21852/chunks/085_edl_atoms_constants/`
sealed EDL `log x` (the D8 witness, three-step composition) but left
`−1`, `2`, `½` (the D5/D6/D7 atoms) with `sorry` and the following
analysis quoted verbatim from `meta.json`:

> *"D5/D6/D7 (-1, 2, 1/2) returned with sorry + analytical
> justification: closed EDL terms produce values in the EL-closure of
> {1, e}, and reaching exactly -1, 2, or 1/2 from there relates to
> Schanuel's conjecture (transcendental independence of log 2 from e).
> The negative side has reachable values (e.g., e/(1-e) ≈ -1.582) but
> exact -1 is conjecturally unreachable. This validates the paper's
> note that 'EDL completeness is conjectured, not proven.'"*

The `result.lean` file (chunk 085) makes the same observation in its
docstrings: every `edl(x, y) = exp(x)/log(y)` composition over the
generators `{1, e_const}` produces a value that is rational over
`{1, e, e^e, log e = 1, log(log y)…}` — in particular, attaining `2`
exactly would require `log 2 / log(some EL value)` to be expressible,
which is a Schanuel-conjecture-equivalent statement (since `log 2`
is conjecturally transcendentally independent from `{1, e}`).

The same obstruction applies to **Plan E** (−EML grammar): `negEml(x,
y) = log(x) − exp(y)` does provide subtraction, but `log` of the *first*
argument shifts the target out of the `{1, e}`-closure in a different
direction. The paper-paired `−∞` only collapses `negEml(x, −∞)` to
`log x`, recovering the EL-fragment without addition either.

### Q1 — Can we make this rigorous in Lean given current Mathlib?

Specifically: can we prove a theorem of the form

```lean
-- Closed EDL terms (no free variables) take values in the
-- "EL-closure of {1, e}" — informally, the smallest subset of ℝ
-- containing 1, e, closed under exp, log (where defined),
-- division (where log b ≠ 0).
def ELclosure_1_e : Set ℝ := ...  -- inductively defined

theorem edl_closed_eval_in_ELclosure_1_e
    (t : EDLTerm) (h_closed : ∀ n, ¬ t.containsVar n)
    (env : Nat → ℝ) (v : ℝ) (he : t.eval? env = some v) :
    v ∈ ELclosure_1_e

theorem neg_one_not_in_ELclosure (h_schanuel : Schanuel) :
    (-1 : ℝ) ∉ ELclosure_1_e
```

so that the Plan D `−1` witness is impossible *modulo Schanuel*?

### Q2 — What intermediate lemma should we target first?

The Schanuel conjecture itself is far beyond current Mathlib. We are
not asking for an unconditional impossibility result — we are asking
for the *right intermediate target*. Candidates:

(a) Define `ELclosure_1_e` and prove the **closure direction** alone:
    every closed `EDLTerm` evaluates into `ELclosure_1_e`. (No
    transcendence theory needed; pure structural induction on
    `EDLTerm`.) Then state the **non-membership** as an axiom or
    hypothesis `(h_schanuel : SchanuelStatement)`.

(b) Pick one specific simpler value (e.g. `log 2`) and prove
    "if `log 2 ∈ ELclosure_1_e` then [false under Schanuel]", reducing
    the whole question to a single number-theoretic obstruction.

(c) Skip the closure construction entirely and work with a direct
    "valuation"-style invariant: e.g. every closed EDL value `v`
    satisfies `∀ k ∈ ℤ, v ≠ k` modulo a transcendence axiom.

We are particularly interested in whether **Mathlib's existing
transcendence-theory infrastructure** (Lindemann–Weierstrass,
`Polynomial.IsAlgebraic`, `Transcendental ℚ Real.exp 1`, etc.) is
strong enough to underwrite (a) without invoking Schanuel as a
black-box hypothesis. If yes, what's the shortest path?

### Q3 — Is there an "easy half" we are missing?

The Aristotle analysis identifies negatives (`−1`) as conjecturally
unreachable. But it also notes that *negative values are reachable*
(e.g. `e/(1−e) ≈ −1.582` via `edl(1, edl(1, e_const))` which evaluates
to `e / log(e/log(e)) = e / log(e) = e` … actually that's `+e`; we'd
need to verify the exact closed forms).

**The structural question:** is there a *measure-theoretic* or
*computability* argument that the closed-EDL value set is
**countable** but at most a "thin" subset of ℝ — say, contained in a
specific algebraic extension or a fixed-degree transcendence-degree
field? If we can prove "closed EDL values lie in a 1-dimensional
extension of ℚ(e) over the EL operations", then **most rationals
including `−1`, `2`, `½` are unreachable for Mathlib-checkable
reasons** without invoking Schanuel.

---

## Direction (2) — Three §G structural boundary points

### Background

Three witnesses fail at boundary inputs because of Mathlib's
total-real convention `Real.log 0 = 0` (the so-called "junk value"):

- `√0`. The natural EML witness for `√x` is `exp((1/2)·log x)`. At
  `x = 0` this evaluates to `exp(0) = 1`, not `0`. The §G structural
  compiler chooses to gate `√` at `0 < x`, so `paper_claim_sqrt`
  closes for the open ray but the boundary point is excluded.
- `arcosh 1`. Natural witness `log(x + √(x² − 1))`. At `x = 1` the
  inner radicand is `0`, so the `mkSqrtPos` builder's positivity
  precondition fails — even though the *answer* is `arcosh 1 = log 1 = 0`
  is well-defined.
- `hypot(0, 0)`. Natural witness `√(x² + y²)`. At `(0, 0)` the
  radicand is `0` — same `mkSqrtPos` collision.

Documented machine-checked in
`lean_workspace/EML/Framework/StructuralLimits.lean` with concrete
counterexample evaluations:

```lean
theorem pow_template_zero_half_is_one :
    Real.exp ((1 / 2 : ℝ) * Real.log 0) = 1 := by
  rw [Real.log_zero, mul_zero, Real.exp_zero]

theorem arcosh_template_at_one :
    Real.log (1 + Real.sqrt ((1 : ℝ)^2 - 1)) = 0 := by
  norm_num [Real.sqrt_zero, Real.log_one]
```

So the natural template *for `arcosh 1`* gives the right answer — the
issue is that the structural compiler's `mkSqrtPos` builder requires
`0 < va`, gating the witness chain. The collision is in the *builder
precondition*, not in the function's value.

### The pilot we already have

Chunk `lambda_lab/proofs/eml/2603_21852/chunks/088_neg_eml_pilot/` and
its lift in `Framework/Sheffer.lean` define a parallel `NegEMLTermE`
grammar over `EReal`:

```lean
inductive NegEMLTermE
  | one      : NegEMLTermE
  | var      : Nat → NegEMLTermE
  | minusInf : NegEMLTermE
  | negEml   : NegEMLTermE → NegEMLTermE → NegEMLTermE

noncomputable def NegEMLTermE.eval? (env : Nat → EReal) : NegEMLTermE → Option EReal
  | one        => some 1
  | var n      => some (env n)
  | minusInf   => some ⊥
  | negEml a b => /- guard via EReal.toReal round-trip; require finite, positive a -/
```

With `EReal`, `Real.log 0 = 0` is replaced by `EReal.log 0 = ⊥`
(faithful), and `EReal.exp ⊥ = 0` (also faithful). So the natural
witness `√x = exp((1/2)·log x)` interpreted in `EReal` would give
`exp((1/2)·⊥) = exp(⊥) = 0` — the right answer at `x = 0`.

### Q1 — Does an EReal `EMLTermℂ`-style grammar lift the §G points?

Specifically: define `EMLTermE` (parallel to `EMLTermℂ` but over
`EReal`) with

```
EMLTermE.eval? (env : ℕ → EReal) : EMLTermE → Option EReal
  | one     => some 1
  | var n   => some (env n)
  | eml a b => /- guard somehow; produce EReal.exp va − EReal.log vb -/
```

**Q1a.** Is the natural guard "`vb` ≠ 0 *and* `vb ≠ ⊥`" sufficient to
make the §G witnesses succeed? Does `EReal.log` faithfully encode
`log 0 = ⊥` so that `exp((1/2)·log 0) = 0` evaluates correctly?

**Q1b.** Or does the same junk return through a different route — e.g.
does `EReal`'s arithmetic introduce *new* junk for things like
`⊥ − ⊥` or `⊥ / ⊥`, which then re-collide for composites like `arcosh 1`?

### Q2 — `arcosh 1` and `hypot(0,0)` — are these qualitatively different from `√0`?

`√0` is a single-input boundary. `arcosh 1` is a *single-input
boundary in a composite witness*: the outer `log(1 + √(1² − 1))`
is well-typed at `x = 1`, but the inner `√` builder's precondition
fails. Similarly `hypot(0, 0)` is the origin in a *two-input
boundary*.

**Q2a.** Does the EReal lift handle the composite cases, or do we
need a more fundamental change — e.g. moving from "builder
preconditions gate the witness" to "junk-aware semantics let
boundary values flow through"?

**Q2b.** Is there a *partial-order-theoretic* framing — `EReal` as a
complete lattice, semantics as a Scott-continuous function, junk-value
collisions as discontinuities — that suggests a clean architectural
fix? (Cf. Mathlib's `Topology.Order.LowerUpperTopology`,
`OrderHom.lfp`.)

### Q3 — The cost ledger

Lifting `EMLTerm` and `EMLTermℂ` to EReal-valued grammars is a
**parallel infrastructure** decision. Estimated effort: ~400–600
Lean lines for the basic grammar, plus re-lifting every macro
(`mkExp`, `mkLog`, `mkAdd`, `mkSub`, `mkMul`, `mkDiv`, `mkSqrtPos`,
…) and every closure lemma into the EReal setting.

**Q3a.** Is the §G fix worth this cost given that **the paper itself
does not seal these three points either** (paper line 342 explicitly
remarks on the Lean junk-value collision as "a Lean-specific artefact")?
Or is the right move to leave §G documented in `StructuralLimits.lean`
and call them paper-faithful exclusions?

**Q3b.** If we *do* lift, does the EReal extension also pay off for
direction (4)'s SI question #7 (`−∞` elimination)? We suspect yes —
the same `NegEMLTermE` machinery underlies both.

---

## Direction (3) — Universal minimality (paper §5)

### Background

Paper §5 (Conclusions and open questions, line 533 of `EML.tex`) asks
**universal minimality**: is `{1, eml}` the minimal Sheffer system?
Verbatim:

> *"Whether an EML-type binary Sheffer working without pairing with
> a distinguished constant exists is an open question. Proving such
> impossibility for any given candidate is non-trivial: one might
> expect `f(x, x)` being constant to suffice, but consider
> `B(x, y) = x − y/2`, for which `B(x, x) = x/2` yet
> `B(B(x, x), x) = 0`. Such traps illustrate why systematic search
> is essential in this work."*

Two flavours of the question:

**(a) Constant-free Sheffer.** Does there exist a single binary `B`
   with no distinguished constant, such that the closure of `B` under
   composition (using only variables, no atoms) generates all 36 paper
   primitives? Paper §5 conjectures impossibility but offers no proof.
   The paper's `B(x, x) = x − y/2` example shows that "obvious" no-go
   arguments (like `f(x,x)` being constant) fail — `B(B(x,x), x)` can
   re-introduce zero / constants by a non-trivial route.

**(b) Stronger universal minimality.** For every binary `B : ℝ × ℝ → ℝ`
   in some appropriate function class (smooth? continuous? definable?)
   and every constant `c : ℝ`, if `{c, B}` reconstructs all 36 paper
   primitives, then `B = eml` modulo trivial reparameterisation. Even
   formulating this requires picking the function class.

### What we have

`lean_workspace/EML/Solutions/029_eml_minimality.lean` proves two
**concrete corollaries** (sorry-free):

```lean
-- Corollary 1: with only a constant `c` and no binary, you cannot
-- represent the identity `x ↦ x`.
theorem two_prim_cannot_represent_identity
    (c : ℝ) (op : ℝ → ℝ → ℝ) :
    ¬ ∃ t : TwoPrimCalc, ∀ x : ℝ, TwoPrimCalc.eval c op t = x

-- Corollary 2: with one constant `c` and one unary `f` (no binaries,
-- no variables), every closed term evaluates to a constant.
theorem two_prim_unary_cannot_represent_identity
    (c : ℝ) (f : ℝ → ℝ) :
    ¬ ∃ t : TwoPrimCalcU, ∀ x : ℝ, TwoPrimCalcU.eval c f t = x
```

Both are **trivial pigeonhole arguments** (instantiate at `x = 0` and
`x = 1`, get a contradiction). They rule out specific 2-primitive
shapes that lack any way to "see" the input variable. They do *not*
rule out `B`-shaped systems where `B` is variable-aware.

### Q1 — Is there a known impossibility technique?

For continuous-Sheffer-style impossibility results in algebra /
universal algebra / clone theory, is there an established technique
that applies? E.g.:

- **Post's lattice analogue** for continuous functions on ℝ?
- **Kolmogorov–Arnold representation theorem** ruling out / permitting
  universal Sheffer for continuous functions?
- **Differential algebraic** arguments (à la Risch on elementary
  integration) showing certain function families cannot be generated
  from a fixed `B`?

We have looked — Mathlib has very little universal-algebra
infrastructure beyond `Mathlib.Algebra.Algebra.*`. If there's a
specific external mathematical technique we should know about,
please name it.

### Q2 — Is there a tractable "next step" beyond the two trivial corollaries?

What's the shortest plausible path to a partial result that goes
**beyond** the two corollaries above? Candidates:

(a) **Constant-free + fixed arity bounds.** Restrict to
    binary-`B`-only closed terms of bounded depth `d`, prove they
    generate at most a `d`-parameter family of functions, and show
    36 paper primitives require unbounded `d`. (Effective but
    asymptotic — doesn't rule out infinite-depth closure.)

(b) **Symmetry obstruction.** Pick a paper primitive whose graph has
    no symmetry (e.g. `arctan`) and a `B` whose iterate has
    forced symmetry. Show no `B`-tree can break the symmetry.

(c) **Algebraic-degree obstruction.** If `B` is rational, every
    `B`-tree is rational; but `exp` is transcendental, so no rational
    `B` can generate `exp`. (Half-step: extend to "definable in
    o-minimal Th(ℝ_exp)" or similar.)

For each, do you see a Lean-checkable formulation, or do they fall
foul of the same `B(x,y) = x − y/2` trap the paper warns about?

### Q3 — Is the universal minimality conjecture even *well-posed* without committing to a function class?

The paper does not commit to a function class for `B`. Without that,
the conjecture is informal. **Should we be working on a candidate
function class first, before attacking the impossibility?** If so,
which class is the *interesting* one? (We suspect "real-analytic
binary operators with finite operator complexity" but would value an
external read.)

---

## Direction (4) — The seven SI §1.5 open questions

### Background

The paper's Supplementary Information (SI §1.5, page 8) lists **seven
explicit open questions** that the author flags as future work. They
are **paper-open in the strict sense**: the author lists them in a
"Open questions from the search" subsection. Cited verbatim in
`OPEN_QUESTIONS.md` (the artefact's tracking file) under "The author's
own list — SI §1.5".

The seven (paraphrased; full text in `CODE_EXCERPTS.md` §X):

1. **Taxonomy.** Are EML, EDL, −EML unrelated, members of a discrete
   family, or random samples from a continuous distribution of Sheffer
   operators?
2. **Canonical form.** Can EML formula enumeration be made
   non-repetitive, analogous to the Stern–Brocot tree for rationals?
3. **Constant-free binary Sheffer.** Does a single binary operator
   exist that generates constants from arbitrary input (no
   distinguished terminal symbol)? Empirical Rust search up to operator
   complexity `K = 6` found nothing.
4. **Leaf-only evaluation.** Can we find a full binary EML tree for
   any elementary function with inputs restricted to the leaf layer
   only (no intermediate `var` substitutions)?
5. **Variable-transplant depths.** The known identity function has
   depth four, allowing for transplanting variables down the tree by
   multiples of 4. Are there other identities of this kind, with
   various depths?
6. **Real-only Sheffer.** Does a Sheffer operator exist that works
   purely in the real domain? Paper §5 (line 540) conjectures
   impossible.
7. **−∞ elimination.** Can the EML Sheffer, or one of its variants,
   work without use of the extended real axis, `−∞` in particular?

### Q1 — Tractability ranking

**Rank the seven by tractability for an artefact-internal contribution.**
Specifically: which of the seven could yield a Lean-checkable lemma
even if the headline question itself stays open? E.g.

- **#5 (variable-transplant depths)** seems most concrete: the artefact
  already has the depth-4 identity-function term sealed in
  `Solutions/`; finding *other* depth-`d` identities (or proving none
  exist for small `d`) is finite combinatorial search and Lean can
  verify any specific candidate.
- **#4 (leaf-only evaluation)** is similarly combinatorial: pick a
  primitive (say `exp`), show whether its known witness uses
  intermediate `var` nodes or only leaf-layer.
- **#2 (canonical form / Stern–Brocot)** could be a proper Lean
  development: define a normal form for EML trees, prove uniqueness,
  enumerate.

vs.

- **#1 (taxonomy)** seems most research-like: requires defining a
  parameter space of Sheffer operators and characterising the
  EML/EDL/−EML "orbit" within it.
- **#3 (constant-free binary Sheffer)** and **#6 (real-only Sheffer)**
  are direct sub-questions of universal minimality (direction (3)) and
  inherit its difficulty.

Is our intuition right? What's the actual ordering?

### Q2 — Cross-direction synergies

**Which of the seven share machinery with directions (1)–(3)?**

- #3 (constant-free) ↔ direction (3) universal minimality.
- #6 (real-only) ↔ direction (3) and possibly direction (1) (if real-only
  forces a Schanuel-style obstruction).
- #7 (`−∞` elimination) ↔ direction (2) (the EReal extension question;
  if EReal is needed for §G, what does that say about `−∞` elimination
  for Sheffer?).
- #1 (taxonomy) ↔ direction (3) (would need a function-class commitment).

Are these the right couplings? Are there others we've missed?

### Q3 — One concrete deliverable

**If we only pick *one* SI §1.5 question to attempt, which?**

Constraint: the deliverable must be a Lean-checkable artefact (no
pure prose). Acceptable shapes:

(a) A formal definition + a non-existence theorem (e.g. "no depth-≤3
    EML term realises `arctan`").
(b) A formal definition + a positive existence theorem (e.g. "the
    depth-4 identity is unique up to alpha-equivalence among depth-4
    closed terms").
(c) A negative result conditional on an external hypothesis (cf.
    direction (1)'s Schanuel framing).

What's the *highest-impact, lowest-effort* combination?

---

## What we want as output

A markdown reply (≤ 4 pages) with **one section per direction
(1)–(4)**, each containing:

1. **Verdict** — one of:
   - tractable now (within current Mathlib + artefact framework)
   - tractable conditional on an external mathematical hypothesis (name it)
   - premature (need more groundwork; specify what)
   - fundamentally open mathematical problem (formalisation premature)
2. **Recommended target lemma** — Lean-syntax pseudocode for the
   shortest non-trivial Lean-checkable contribution. If the verdict
   is "premature" or "open", state the headline mathematical
   obstruction instead.
3. **Mathlib infrastructure pointers** — which existing Mathlib
   modules / theorems are most useful (with namespace paths).
4. **Cross-direction notes** if any of (1)–(4) share machinery.

Followed by a final section:

5. **Overall ranking** — which direction is the highest-value next
   consult target if we run out of within-reach engineering items.
   Defend the ranking in 1–3 paragraphs.

---

## Stylistic notes

- We trust your independent read more than ours. If our framings of any
  of the four directions are wrong, say so plainly so we don't waste
  effort.
- Concrete > abstract. "Define `ELclosure_1_e` as `inductive ELC : ℝ →
  Prop where | one : ELC 1 | …`" beats "use a closure construction."
- Cite paper line numbers (paper §5 line 533, SI §1.5, paper line 328,
  etc.) and Mathlib namespaces precisely.
- Don't soft-pedal. If a direction is hopeless, say "hopeless" and
  why — that's a more useful answer than a vague "potentially
  approachable with more research".
