# Code excerpts — Lean source for the four frontier questions

> This file contains the relevant Lean definitions and theorem
> statements Pro needs to answer the four frontier directions. Pro can
> answer the prompt from this file alone — no repo access required.

## 1. The four term grammars (with `eval?` rules)

### `EMLTerm` (real fragment) and `EMLTermℂ` (complex extension)

`EML/Term.lean:21-50` and `EML/Framework/EMLPartial.lean:28-55`.
Same shape, ℝ vs. ℂ semantics; `eml(a, b) = exp(a) − log(b)` either way:

```lean
-- EML/Term.lean
inductive EMLTerm | one | var (n : Nat) | eml (a b : EMLTerm)

-- EML/Framework/EMLPartial.lean — partial eval over Option ℝ
noncomputable def EMLTerm.eval? (env : Nat → ℝ) : EMLTerm → Option ℝ
  | .one     => some 1
  | .var n   => some (env n)
  | .eml a b =>
      match EMLTerm.eval? env a, EMLTerm.eval? env b with
      | some va, some vb =>
          if 0 < vb then some (Real.exp va - Real.log vb) else none
      | _, _ => none

-- EML/Framework/Complex/Term.lean — same shape, ℂ-valued; gates on vb ≠ 0
noncomputable def EMLTermℂ.eval? (env : Nat → ℂ) : EMLTermℂ → Option ℂ
  | .one     => some 1
  | .var n   => some (env n)
  | .eml a b =>
      match EMLTermℂ.eval? env a, EMLTermℂ.eval? env b with
      | some va, some vb =>
          if vb = 0 then none else some (Complex.exp va - Complex.log vb)
      | _, _ => none
```

### `EDLTerm` (Plan D, paired with constant `e`)

`EML/Framework/Sheffer.lean:79-116`:

```lean
-- EML/Framework/Sheffer.lean
inductive EDLTerm
  | one     : EDLTerm
  | var     : Nat → EDLTerm
  | e_const : EDLTerm                   -- the paper-paired constant `e`
  | edl     : EDLTerm → EDLTerm → EDLTerm
  deriving Repr

noncomputable def EDLTerm.eval? (env : Nat → ℝ) : EDLTerm → Option ℝ
  | .one     => some 1
  | .var n   => some (env n)
  | .e_const => some (Real.exp 1)
  | .edl a b => (eval? env a).bind fun va =>
                  (eval? env b).bind fun vb =>
                    if Real.log vb = 0 then none
                    else some (Real.exp va / Real.log vb)
```

### `NegEMLTerm` (Plan E, real version, paired with `1`) and `NegEMLTermE` (EReal pilot)

`EML/Framework/Sheffer.lean:144-173` and `:399-430`. Two parallel
grammars: the real-only `NegEMLTerm` (with no `−∞`) and the EReal
pilot `NegEMLTermE` (with a `minusInf` constructor):

```lean
-- EML/Framework/Sheffer.lean
inductive NegEMLTerm
  | one    : NegEMLTerm
  | var    : Nat → NegEMLTerm
  | negEml : NegEMLTerm → NegEMLTerm → NegEMLTerm

noncomputable def NegEMLTerm.eval? (env : Nat → ℝ) : NegEMLTerm → Option ℝ
  | .one        => some 1
  | .var n      => some (env n)
  | .negEml a b => (eval? env a).bind fun va =>
                     (eval? env b).bind fun vb =>
                       if 0 < va then some (Real.log va - Real.exp vb)
                       else none

inductive NegEMLTermE
  | one      : NegEMLTermE
  | var      : Nat → NegEMLTermE
  | minusInf : NegEMLTermE              -- ← the paper-paired `−∞`
  | negEml   : NegEMLTermE → NegEMLTermE → NegEMLTermE

noncomputable def NegEMLTermE.eval? (env : Nat → EReal) : NegEMLTermE → Option EReal
  | .one        => some 1
  | .var n      => some (env n)
  | .minusInf   => some ⊥
  | .negEml a b => (eval? env a).bind fun va =>
                     (eval? env b).bind fun vb =>
                       let ra := va.toReal
                       let rb := vb.toReal
                       if (va = (ra : EReal)) ∧ (vb = (rb : EReal)) ∧ (0 < ra)
                       then some ((Real.log ra : EReal) - (Real.exp rb : EReal))
                       else none
```

The **guard via `EReal.toReal` round-trip** is the key trick: if `va`
equals the `EReal` lift of its real-part (i.e. it isn't `⊥` or `⊤`),
same for `vb`, *and* `ra > 0` — then the result is the finite-real
`log ra − exp rb`. Otherwise `none`. This is what direction (2)'s Q1a
is asking about: does this guard trick generalise to handle the §G
boundary points (`√0`, `arcosh 1`, `hypot(0, 0)`) by letting `va = ⊥`
flow through faithfully rather than colliding with `Real.log 0 = 0`?

---

## 2. The structural compiler `ELExpr.compile`

`EML/Framework/Compilers/ELToEML.lean:24-52` — full definition. Each
EL constructor dispatches to a builder in `EML.Framework.Builders.*`.
**This is the bridge from F36Expr to EMLTerm**; the compile-then-lift
pipeline is what direction (2) would have to re-instantiate over EReal.

```lean
-- EML/Framework/Compilers/ELToEML.lean
namespace EML
open EMLTerm

/-- Structural compiler from `ELExpr` to `EMLTerm`. -/
noncomputable def ELExpr.compile : ELExpr → EMLTerm
  -- Atoms
  | .one          => EMLTerm.one
  | .var n        => EMLTerm.var n
  -- Constants
  | .zero         => mkZero
  | .negOne       => mkNegOne
  | .two          => mkTwo
  | .half_const   => mkHalf
  | .e_const      => mkE
  -- Unary
  | .neg a        => mkNeg a.compile
  | .inv a        => mkInvNonzero a.compile           -- widened: va ≠ 0
  | .sq a         => mkSqAll a.compile                -- widened: any va
  | .sqrt a       => mkSqrtPos a.compile              -- §G barrier: needs 0 < va
  | .exp a        => mkExp a.compile
  | .log a        => mkLog a.compile
  | .halve a      => mkHalveAll a.compile             -- widened: any va
  -- Binary
  | .add a b      => mkAdd a.compile b.compile
  | .sub a b      => mkSub a.compile b.compile
  | .mul a b      => mkMulAll a.compile b.compile     -- widened: any va, vb
  | .div a b      => mkDivNonzeroDenom a.compile b.compile  -- widened: vb ≠ 0
  | .pow a b      => mkPowAll a.compile b.compile     -- widened: any vb ∈ ℝ
  | .logb a b     => mkLogbAll a.compile b.compile    -- widened: 0 < va, va ≠ 1, 0 < vb
  | .avg a b      => mkAvgAll a.compile b.compile     -- widened: any va, vb
  | .hypot a b    => mkHypotAll a.compile b.compile   -- widened: (va,vb) ≠ (0,0)

theorem ELExpr.compile_correct (e : ELExpr) (env : Nat → ℝ) (v : ℝ)
    (h : e.eval? env = some v) :
    e.compile.eval? env = some v
-- 200-line structural induction; one case per ELExpr constructor.

end EML
```

The compiler is the architectural target that direction (2)'s EReal
lift would have to mirror: `compile_E : ELExprE → EMLTermE` over
`EReal`, with `compile_correct_E` as the analogous induction.

---

## 3. Plan D progress — sealed EDL witnesses

`EML/Framework/Sheffer.lean:213-360` — the 8 sealed primitives:

```lean
-- The five "trivial" / structural atoms:
theorem edl_paper_claim_one :     ∃ t, ∀ env, t.eval? env = some (1 : ℝ)
theorem edl_paper_claim_var :     ∃ t, ∀ env, t.eval? env = some (env 0)
theorem edl_paper_claim_e_const : ∃ t, ∀ env, t.eval? env = some (Real.exp 1)
theorem edl_paper_claim_exp :
    ∃ t, ∀ env, t.eval? env = some (Real.exp (env 0))
  -- Witness: edl(var 0, e_const)

theorem edl_paper_claim_log :
    ∃ t, ∀ env, 0 < env 0 → env 0 ≠ 1 →
      t.eval? env = some (Real.log (env 0))
  -- Witness: edl(1, edl(edl(1, var 0), e_const))    (Aristotle chunk 085)

-- Compositions through D8 (log_x):
theorem edl_paper_claim_div :
    ∃ t, ∀ env, 0 < env 0 → env 0 ≠ 1 → env 1 ≠ 0 →
      t.eval? env = some (env 0 / env 1)             -- chunk 086

theorem edl_paper_claim_exp_exp :
    ∃ t, ∀ env, t.eval? env = some (Real.exp (Real.exp (env 0)))
  -- Witness: edl(edl(var 0, e_const), e_const)      (chunk 087)

theorem edl_paper_claim_log_log :
    ∃ t, ∀ env, /- four positivity hypotheses -/
      t.eval? env = some (Real.log (Real.log (env 0)))     -- chunk 087
```

### The three sorry'd EDL atoms — direction (1)'s targets

`chunks/085_edl_atoms_constants/result.lean:34-58`:

```lean
-- chunks/085_edl_atoms_constants/result.lean

/-- **D5** — Witness for `−1`.

**Analysis**: All closed EDL terms (built from `one`, `e_const`, `edl`)
produce values in the EL-closure of `{1, e}`. Constructing exactly
`−1` would require `log(e − 1)` to be in this closure — closely
related to Schanuel's conjecture. Negative values ARE reachable (e.g.,
`e/(1−e) ≈ −1.582`), but hitting `−1` exactly appears beyond pure
closed EDL. -/
theorem edl_witness_neg_one :
    ∃ t : EDLTerm, ∀ env : Nat → ℝ, t.eval? env = some (-1 : ℝ) := by
  sorry

/-- **D6** — Witness for `2`.

**Analysis**: Constructing `2` requires `exp(a)/log(b) = 2` for closed
EDL terms, which would place `log(2)` in the EL-closure of `{1, e}`.
This is believed false by Schanuel's conjecture (ln 2 is
transcendentally independent from e). -/
theorem edl_witness_two :
    ∃ t : EDLTerm, ∀ env : Nat → ℝ, t.eval? env = some (2 : ℝ) := by
  sorry

/-- **D7** — Witness for `1/2`. Same obstruction as D6 (constructing
`1/2` is equivalent in difficulty to constructing `2`). -/
theorem edl_witness_half :
    ∃ t : EDLTerm, ∀ env : Nat → ℝ, t.eval? env = some ((1 : ℝ) / 2) := by
  sorry
```

These three `sorry`s are the only ones in the chunk-085 chunk after
Aristotle's pass. They are the headline targets for direction (1).

---

## 4. The §G boundary lemmas — direction (2)'s motivation

`EML/Framework/StructuralLimits.lean:1-198` (selected):

```lean
-- EML/Framework/StructuralLimits.lean
namespace EML

/-- Mathlib's total `Real.log` returns `0` outside the natural domain.
This is the source of the §G structural collision: any EML witness
that uses `log` cannot distinguish `0` from `1` at the `x = 0`
boundary. -/
theorem log_zero_is_junk : Real.log 0 = 0 := Real.log_zero

theorem log_neg_one_is_junk : Real.log (-1) = 0 := by
  rw [show (-1 : ℝ) = -(1 : ℝ) from rfl, Real.log_neg_eq_log, Real.log_one]

/-- The natural real-EML formula `pow x y := exp(y · log x)` is the
template the structural compiler instantiates for `√x` (with `y = 1/2`).
At `x = 0` this template returns `1` (because `log 0 = 0`), not `0` —
the §G collision. -/
theorem pow_template_zero_half_is_one :
    Real.exp ((1 / 2 : ℝ) * Real.log 0) = 1 := by
  rw [Real.log_zero, mul_zero, Real.exp_zero]

/-- The natural template for `arcosh` is `log(x + √(x² − 1))`. At
`x = 1`, the inner `√(0) = 0` is mathematically clean
(`arcosh 1 = log(1 + 0) = 0`), but the EML structural compiler's
`mkSqrtPos` builder requires `0 < arg`, so the witness chain breaks
at the boundary. -/
theorem arcosh_template_at_one :
    Real.log (1 + Real.sqrt ((1 : ℝ)^2 - 1)) = 0 := by
  norm_num [Real.sqrt_zero, Real.log_one]

/-- `hypot 0 0 = √(0² + 0²) = √0 = 0`, but the natural EML `mkHypot`
construction `√(x² + y²)` requires both `x² + y²` and `√` to evaluate
inside the EML domain — the §G boundary again. -/
theorem hypot_zero_zero_decomposes_to_sqrt_zero :
    Real.sqrt ((0 : ℝ) ^ 2 + (0 : ℝ) ^ 2) = 0 := by
  norm_num

end EML
```

Three different boundary cases, three different builders, **same root
cause**: `Real.log 0 = 0` (junk) propagates into `exp((1/2) · log 0) =
1` for `√0`; into `√(1²−1) = √0` for `arcosh 1`; into `√(0²+0²) = √0`
for `hypot(0, 0)`.

The relevant Mathlib facts on `EReal`:
- `EReal.log_zero : Real.log 0 = 0` is *not* the EReal version. The
  faithful EReal extension would have `EReal.log 0 = ⊥` and
  `EReal.exp ⊥ = 0` so that `exp((1/2) · log 0) = exp(⊥) = 0`. Pro
  should check whether Mathlib's `EReal.log` / `EReal.exp` has the
  right signature.

---

## 5. Universal minimality — direction (3)'s starting point

`Solutions/029_eml_minimality.lean` (full file):

```lean
-- Solutions/029_eml_minimality.lean
namespace EML

/-- Generic 2-primitive calculator with a constant `c` and a binary `op`. -/
inductive TwoPrimCalc : Type
  | const : TwoPrimCalc
  | apply : TwoPrimCalc → TwoPrimCalc → TwoPrimCalc
  deriving Repr

/-- Evaluation of a constant-only / binary-only calculator: it simply
re-applies the binary `op` over a single constant. The variable `x`
never enters. -/
def TwoPrimCalc.eval (c : ℝ) (op : ℝ → ℝ → ℝ) : TwoPrimCalc → ℝ
  | .const     => c
  | .apply a b => op (eval c op a) (eval c op b)

/-- Universal minimality (corollary 1): no 2-primitive calculator
(constant + binary) can represent the identity `x ↦ x` — because the
calculator has no way to refer to `x` at all. -/
theorem two_prim_cannot_represent_identity
    (c : ℝ) (op : ℝ → ℝ → ℝ) :
    ¬ ∃ t : TwoPrimCalc, ∀ x : ℝ, TwoPrimCalc.eval c op t = x := by
  by_contra h
  obtain ⟨t, ht⟩ := h
  linarith [ht 0, ht 1]

/-- Variant: constant + unary. Closed terms again do not depend on `x`. -/
inductive TwoPrimCalcU : Type
  | const : TwoPrimCalcU
  | apply : TwoPrimCalcU → TwoPrimCalcU
  deriving Repr

def TwoPrimCalcU.eval (c : ℝ) (f : ℝ → ℝ) : TwoPrimCalcU → ℝ
  | .const   => c
  | .apply a => f (eval c f a)

theorem two_prim_unary_cannot_represent_identity
    (c : ℝ) (f : ℝ → ℝ) :
    ¬ ∃ t : TwoPrimCalcU, ∀ x : ℝ, TwoPrimCalcU.eval c f t = x := by
  intro h
  obtain ⟨t, ht⟩ := h
  linarith [ht 0, ht 1]

end EML
```

Both proofs are **two-line `linarith`**: the term has no `var`
constructor, so its eval is a constant function of `x`, and therefore
cannot equal both `0` and `1`. **These rule out very specific
2-primitive shapes; they do not address the universal claim** that no
single binary `B : ℝ × ℝ → ℝ` (with or without a paired constant) can
generate all 36 paper primitives modulo `eml`.

---

## 6. The seven SI §1.5 questions — verbatim citation

Verbatim from `OPEN_QUESTIONS.md:59-92` (which itself cites the
paper's SI §1.5 page 8):

```
1. Taxonomy. "Are EML, EDL, and −EML unrelated, members of a
   discrete family, or random samples from a continuous distribution
   of Sheffer operators?"

2. Canonical form. "Can formula enumeration using EML (or one of
   its variants) be made non-repetitive, analogous to the Stern–Brocot
   tree for rationals?"

3. Constant-free binary Sheffer. "Does a single binary operator
   exist that generates constants from arbitrary input (no
   distinguished terminal symbol)?" SI §1.4 records a Rust exhaustive
   search (profile B) finding nothing up to operator complexity K = 6.

4. Leaf-only evaluation. "Can we find a full binary EML tree for
   any elementary function with inputs restricted to the leaf layer
   only?"

5. Variable-transplant depths. "Known identity function has
   depth four, allowing for transplanting variables down the tree by
   multiples of 4. Are there other of this kind, with various depths?"

6. Real-only Sheffer. "Does a Sheffer operator exist that works
   purely in the real domain?" Paper §5 (line 540) conjectures
   impossible but offers no proof.

7. −∞ elimination. "Can the EML Sheffer, or one of its variants,
   work without use of the extended real axis, −∞ in particular?"
```

---

## 7. Closure / domain lemmas Pro might want for direction (1)

For direction (1), Pro may want to express "EL-closure of `{1, e}`"
inductively. Suggested shape (not in repo yet):

```lean
-- Hypothetical scaffolding for direction (1) — not in repo
inductive ELclosure_1_e : ℝ → Prop
  | one : ELclosure_1_e 1
  | e   : ELclosure_1_e (Real.exp 1)
  | exp_of {v : ℝ} : ELclosure_1_e v → ELclosure_1_e (Real.exp v)
  | log_of {v : ℝ} (h : 0 < v) : ELclosure_1_e v → ELclosure_1_e (Real.log v)
  | div_of {a b : ℝ} (hb : Real.log b ≠ 0) :
      ELclosure_1_e a → ELclosure_1_e b →
      ELclosure_1_e (Real.exp a / Real.log b)
```

The closure direction (every closed `EDLTerm` evaluates into
`ELclosure_1_e`) is structural induction on `EDLTerm` and looks
**Lean-tractable without any transcendence theory** (it's a
syntactic-into-semantic embedding).

The non-membership direction (e.g. `-1 ∉ ELclosure_1_e`) is the part
that needs Schanuel or a transcendence-theory black-box hypothesis.
Mathlib namespaces to consider:
- `Mathlib.NumberTheory.Transcendental.Lindemann`
  (`Transcendental ℚ Real.exp 1` is provable here)
- `Mathlib.RingTheory.Algebraic` for `IsAlgebraic ℚ`
- (No `Schanuel` namespace exists in Mathlib v4.28 to our knowledge.)

---

## 8. Companion: the `ELExpr` source language (for context)

`EML/Framework/ELExpr.lean` defines the intermediate `ELExpr` (24
constructors). Relevant excerpt for direction (2)'s "what would the
EReal lift look like":

```lean
-- EML/Framework/ELExpr.lean (excerpt)
inductive ELExpr where
  | one : ELExpr
  | var : Nat → ELExpr
  | zero : ELExpr
  | negOne : ELExpr
  | two : ELExpr
  | half_const : ELExpr
  | e_const : ELExpr
  | neg : ELExpr → ELExpr
  | inv : ELExpr → ELExpr
  | sq : ELExpr → ELExpr
  | sqrt : ELExpr → ELExpr           -- §G primitive
  | exp : ELExpr → ELExpr
  | log : ELExpr → ELExpr             -- §G source
  | halve : ELExpr → ELExpr
  | add : ELExpr → ELExpr → ELExpr
  | sub : ELExpr → ELExpr → ELExpr
  | mul : ELExpr → ELExpr → ELExpr
  | div : ELExpr → ELExpr → ELExpr
  | pow : ELExpr → ELExpr → ELExpr
  | logb : ELExpr → ELExpr → ELExpr
  | avg : ELExpr → ELExpr → ELExpr
  | hypot : ELExpr → ELExpr → ELExpr  -- §G boundary at (0, 0)

noncomputable def ELExpr.eval? (env : Nat → ℝ) : ELExpr → Option ℝ
  -- partial; gates `log`, `sqrt`, `inv`, `div`, `pow`, `logb` at their
  -- natural domain boundaries.
```

**Note on direction (2):** the §G barrier sits at `sqrt` (gated by
`0 < va`) and at `log` (gated by `0 < va`). An `ELExprE` over EReal
would have to face the same gating decisions, but with `EReal.log
0 = ⊥` available as a proper value rather than as junk.

---

## 9. Cross-reference summary

| Direction | Files Pro should look at most carefully |
|---|---|
| (1) Schanuel ceiling | §3 sealed EDL witnesses; §1's `EDLTerm` grammar; §7 ELclosure scaffolding |
| (2) §G boundary points | §1 `NegEMLTermE` grammar; §2 `ELExpr.compile`; §4 boundary lemmas |
| (3) Universal minimality | §5 the two trivial corollaries |
| (4) SI §1.5 list | §6 verbatim list; cross-references to §1, §3, §5 |

The four directions are interlocked: an EReal lift (direction 2) helps
SI §1.5 #7 (direction 4); a Schanuel hypothesis (direction 1) is one
candidate for proving constant-free Sheffer impossibility (direction 3
↔ SI §1.5 #3); universal minimality (direction 3) subsumes SI §1.5 #3
and #6.
