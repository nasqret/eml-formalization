# GPT Pro consult — pre-announcement review

## What we want from you

I'm about to make a **public announcement** of a Lean 4 + Mathlib
formalization of A.~Odrzywołek's 2026 paper *"All elementary
functions from a single binary operator"* (arXiv:2603.21852). The
artefact is hosted at
<https://github.com/nasqret/eml-formalization> under MIT licence.

Before the announcement I want one more independent review. You
have already audited this artefact twice — once for trigonometric
widening (2026-05-08, your Path C′ recommendation) and once for the
four research-grade frontier directions (2026-05-10, your ranking
+ specific target lemmas). Both recommendations were implemented;
the artefact now contains a substantial body of "your" Lean
content.

**This pass is a sanity check on the assembly, not a fresh
direction-setting consult.** Please flag any of:

1. **Mathematical concerns** — anywhere the formalized statement
   doesn't faithfully translate the underlying paper claim. Watch
   especially for over-eager generalizations, quantifier flips that
   silently weaken the claim, or witness families that conceal a
   weaker per-environment guarantee.

2. **Lean-style concerns** — anywhere a stylistic choice might draw
   fire from the formal-methods community:
   - A `def NoIdentityAtDepthThree : Prop` that stands in for a
     real `theorem`.
   - An `EDLTranscendenceBarrier : Prop` typeclass without an
     instance.
   - Witness-family quantifier flips (`∀ env, [hyp] → ∃ t, ...`
     rather than `∃ t, ∀ env, [hyp] → ...`).
   - The use of `Mathlib`-wide imports in some new modules
     (`PolynomialBinary.lean`) where a more focused import would be
     cleaner.

3. **Honesty / over-claiming** — anywhere our documentation says
   "sealed" but the thing on main is weaker. Specific spots to
   check (see code excerpts):
   - We claim §G boundary points are now sealed in
     `GFullFix.lean`. Is the witness-family quantifier flip a fair
     interpretation of "sealing", or is this a different kind of
     statement that should be advertised differently?
   - `CompactWitnesses.lean` provides "alternative direct-macro
     witnesses". Its docstring says they have IDENTICAL K-counts to
     the structural-compile output. Is the inclusion of this
     module misleading (we suggest "compact" but they're not)?
   - The `EDLTranscendenceBarrier` typeclass is a real Lean
     mechanism, but it has no instance. Are the three corollaries
     (`no_closed_edl_{neg_one, two, half}`) over-stated as
     "structural ceiling sealed"?

4. **Public-API correctness** — assuming our `import EML` exposes
   the 100 public theorems we claim (61 original + 39 frontier),
   please verify the type signatures (in the code excerpts) are
   what they should be. We are particularly nervous about:
   - `paper_claim_*_full` signatures with the quantifier-flipped form.
   - `no_polynomial_binary_generates_exp` — the negation might be
     either too strong (does it apply to constants `c ≠ 0` cases?
     to identity `B(x,y) = x`?) or somehow vacuous.
   - The shape of `polynomial_binary_terms_are_polynomial`'s
     conclusion (`∃ P : Polynomial ℝ, ∀ x, ... = P.eval x`) — is
     this the right statement of "every BTerm is a polynomial"?

5. **Embarrassment risk** — anything that, if the source paper's
   author (Andrzej Odrzywołek) or a Lean expert reads the artefact
   and the announcement, would make us look careless or
   overconfident. We have explicitly de-emphasized the K-count
   consolidation finding (it turned out to be a no-op); we have
   honest disclaimers on the d=3 port. Are there other places
   where honesty could be improved?

We want a **ship/don't-ship verdict** on the public announcement
plus a punch list of any concrete fixes you'd want before we go
public.

---

## Project architecture (90 seconds)

The Lean artefact lives in
`lambda_lab/proofs/eml/2603_21852/lean_workspace/EML/`. The
build-target `EML` exports a public API consisting of:

```
EMLTerm  ─ inductive: T ::= 1 ∣ xₙ ∣ eml(T, T)
EMLTermℂ ─ complex variant, same syntax, ℂ-valued evaluation
EDLTerm  ─ Sheffer cousin: edl(x, y) := exp(x) / log(y) with paired constant `e`
NegEMLTerm ─ Sheffer cousin: negEml(x, y) := log(x) − exp(y) (ℝ-grammar)
NegEMLTermE ─ same, over EReal, allowing `−∞` as a primitive
```

Each grammar has:
- A partial `eval?` returning `Option` (we never collapse to a
  junk value at undefined points).
- A `K_count_*` theorem giving the tree size by `rfl`.
- A family of `paper_claim_*` (or `edl_paper_claim_*` /
  `negEml_paper_claim_*`) theorems, each a one-line existential
  stating that the paper's primitive is realized by a literal term
  on a non-empty open subset of its natural domain.

Three layered "compilers" connect the grammars: `F36Expr` (paper's
36 primitives) → `ELExpr` (exp/log/arithmetic intermediate) →
`EMLTerm` (kernel grammar). A single uniform theorem
`F36Expr.real_complete` proves the chain correct.

For the trig family, a complex-valued analogue
`F36Expr.complex_complete` plus a homomorphism `EMLTerm.toComplex`
let us produce real-valued witnesses by `.re` / `.im` projection of
`EMLTermℂ` evaluations.

## The six new frontier modules (this consult's focus)

GPT Pro consulted 2026-05-10 ranked four directions; we delivered
substantive Lean content on all four, totaling 39 new public
theorems on top of the original 61. Full code excerpts in
`CODE_EXCERPTS.md`. Brief tour:

### 1. `TransplantDepths.lean` (SI §1.5 #5 — your direction #1)

**Headline:** for every multiple of 4, there exists an EMLTerm of
exactly that depth that evaluates to the identity function. Plus
two negative results (no identity at depth 1, no identity at
depth 2). Plus a Prop statement of the d=3 case (Aristotle proved
it in a simplified grammar; the canonical-grammar port is a
follow-up).

**Concerns we have:**
- The affirmative is via an explicit construction `idMulFour k`
  iterating `mkLog ∘ mkExp` `k` times. Is this faithful to the
  paper's "transplanting variables down the tree by multiples of
  4" framing? (We believe yes — every iteration of `mkLog ∘ mkExp`
  adds exactly 4 to the depth and preserves the value.)
- The headline conjecture `OnlyMultiplesOfFourHaveIdentities :
  Prop` is a `def`, not a `theorem`. We say so explicitly. Is
  this a clean way to state an open conjecture, or does it look
  like we're hiding a hole?

### 2. `StructuralLimitsEReal.lean` + `GFullFix.lean` (your direction #2)

**Headline:** the three §G boundary points (`√0`, `arcosh 1`,
`hypot(0, 0)`) — previously documented as "structural limits
falling outside the natural construction" — are now sealed in two
complementary ways:

- `StructuralLimitsEReal.lean`: the three boundary values are
  proved correct in extended-real arithmetic (Mathlib's
  `EReal.exp` + `ENNReal.log`). Three template lemmas. This was
  your specific recommendation.

- `GFullFix.lean`: three new public theorems
  `paper_claim_sqrt_full`, `paper_claim_arcosh_full`,
  `paper_claim_hypot_full` extending the existing narrow
  paper_claims to the full natural domain via a witness-family
  quantifier flip. The boundary witness is `mkZero` (which evaluates
  to `some 0` everywhere); off-boundary the narrow witnesses apply.

**Concerns we have:**
- The witness-family quantifier flip (`∀ env, [hyp] → ∃ t, ...`)
  is a real change from the original `∃ t, ∀ env, [hyp] → ...`
  form of the narrow paper_claims. Is advertising this as
  "boundary points sealed" honest, or should we make the
  quantifier-flip prominent?

### 3. `EDLClosedVal.lean` (your direction #3)

**Headline:** for the EDL Sheffer cousin (paper §3.1), we add
- `EDLClosedVal : ℝ → Prop` — inductive predicate giving the exact
  set of values reachable from CLOSED EDL terms.
- `edl_closed_eval_in_closedVal` — closure theorem.
- `EDLTranscendenceBarrier : Prop` typeclass — packages the three
  conjectural non-membership facts (`-1`, `2`, `1/2` not in
  `EDLClosedVal`).
- Three corollaries `no_closed_edl_{neg_one, two, half}` gated by
  the typeclass.

**Concerns we have:**
- The typeclass has **no instance**. We say so explicitly. Is this
  a fair way to formalize "this would close the structural ceiling
  conditional on a Schanuel-style result", or does it look like a
  vacuous claim?

### 4. `PolynomialBinary.lean` (your direction #4)

**Headline:** paper §5 universal-minimality, polynomial-class
first cut.

- `BTerm` — free term language over a single binary op `B`.
- `IsPolynomialBinary B : Prop` — witnessed by an
  `MvPolynomial (Fin 2) ℝ`.
- `polynomial_binary_terms_are_polynomial` — composition lemma:
  every BTerm evaluated under a polynomial `B` on a constant
  environment is a univariate polynomial in the constant.
- `no_polynomial_binary_generates_exp` — main impossibility result,
  via `Polynomial.tendsto_div_exp_atTop`.

**Concerns we have:**
- The proof uses `MvPolynomial.aeval` + `map_eval₂Hom` /
  `eval₂Hom_id`. The composition step has some `erw` and
  `simp +decide` that worry us slightly stylistically. Does the
  proof look kernel-clean to you?
- The contradiction step uses `Filter.Tendsto.const_div` /
  `tendsto_nhds_unique` against the constant function 1. Is this
  the right (and most direct) Mathlib path?
- Does the theorem statement match what one means by "polynomial
  binary `B` cannot generate `exp`"?

### 5. `CompactWitnesses.lean` (post-discovery decoration)

**Headline:** 9 alternative direct-macro witnesses for the
binary/long-unary paper claims (`mul`, `div`, `avg`, `pow`,
`logb`, `hypot`, `inv`, `sq`, `halve`).

**Concerns we have:**
- We discovered empirically that the K-counts of these "compact"
  witnesses are **identical** to the structural-compile output.
  The module docstring is explicit about this honest finding. Is
  the module's name (`CompactWitnesses`) misleading? Should we
  rename it (e.g., `AlternativeWitnesses`)?

---

## Specific verification asks

Beyond the general flag-anything-wrong request, please specifically
verify the following claims hold up:

1. **No silent regression in the original 61 paper claims.** The
   new modules only ADD theorems; they do not modify
   `PaperClaims.lean` or `Sheffer.lean`.

2. **Build cleanliness.** `lake build EML` returns at 8062 jobs.
   No `sorry`, no `admit`, no `native_decide` shortcuts. (See
   `PROJECT_SCOREBOARD.md` for the verification commands.)

3. **`#print axioms` cleanliness.** The artefact uses only
   Mathlib's standard noncomputable axioms (classical choice,
   function extensionality, propositional extensionality). No
   project-specific axioms.

4. **Domain consistency.** Wherever a `paper_claim_*` says
   `t.eval? env = some <value>`, the value is the paper's stated
   mathematical answer, not a junk-shifted variant.

5. **No broken doc links.** All `[...](...)` references in the
   top-level `README.md` and `DASHBOARD.md` resolve to files
   that exist.

6. **Numbers consistent.** 100 public theorems, 8062 lake jobs,
   3/3 §G points sealed. Same numbers in `README.md`,
   `DASHBOARD.md`, `lambda_lab/.../AUTHOR_SUMMARY.md`, and
   `lambda_lab/.../OPEN_QUESTIONS.md`.

---

## Output spec

Please structure your response as:

- **Verdict:** SHIP / SHIP-WITH-FIXES / DON'T-SHIP.

- **Concrete punch list** (if applicable): each item with
  (a) location in the artefact, (b) why it's a concern, (c) the
  smallest fix you'd want.

- **Per-direction sanity check**: brief OK/concern statement for
  each of the six new modules (TransplantDepths,
  StructuralLimitsEReal, EDLClosedVal, PolynomialBinary,
  CompactWitnesses, GFullFix).

- **Anything else** that would be useful for the author to know
  before going public.

We want to ship today. Punch list items would land before the
announcement; deeper structural concerns would delay it.
