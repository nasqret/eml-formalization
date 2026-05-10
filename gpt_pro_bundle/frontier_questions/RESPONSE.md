# GPT Pro response — four frontier directions

> Received 2026-05-10. Verbatim transcription below.

---

## (1) Schanuel-style ceiling for Plan D/E

**Verdict — tractable conditional on an external hypothesis.**
The Lean-tractable part is the closure theorem. The non-membership theorem `(-1) ∉ ELclosure_1_e` is not within current Mathlib, and I would not label it "from Schanuel" until you formulate the exact Schanuel consequence you need. Current Mathlib has Lindemann–Weierstrass infrastructure, but that only covers exponentials of algebraic inputs; it does not control arbitrary nested expressions built from `e`, `exp`, `log`, and division. Mathlib's `Real.log` is also totalized with `log 0 = 0`, so the closure predicate must mirror your guarded `eval?`, not raw total `Real.log`.

**Recommended target lemma.**
Do not start with a large "EL-closure under exp/log/div" if the aim is an impossibility result; it is too coarse. Start with the exact closed-EDL value grammar.

```lean
inductive EDLClosedVal : ℝ → Prop
  | one : EDLClosedVal 1
  | e_const : EDLClosedVal (Real.exp 1)
  | edl {a b : ℝ} :
      EDLClosedVal a →
      EDLClosedVal b →
      Real.log b ≠ 0 →
      EDLClosedVal (Real.exp a / Real.log b)

def EDLTerm.IsClosed : EDLTerm → Prop
  | .one => True
  | .e_const => True
  | .var _ => False
  | .edl a b => a.IsClosed ∧ b.IsClosed

theorem edl_closed_eval_in_closedVal
    {t : EDLTerm} (ht : t.IsClosed)
    (env : Nat → ℝ) {v : ℝ}
    (he : t.eval? env = some v) :
    EDLClosedVal v := by
  induction t generalizing v with
  | one => simp [EDLTerm.eval?] at he; subst v; exact .one
  | e_const => simp [EDLTerm.eval?] at he; subst v; exact .e_const
  | var n => cases ht
  | edl a b iha ihb =>
      -- destruct eval? a, eval? b, the `if Real.log vb = 0`, then apply `.edl`
      ...
```

Then add the conditional obstruction as a named hypothesis, not as a fake `Schanuel` theorem:

```lean
class EDLTranscendenceBarrier : Prop where
  neg_one_not_closed : ¬ EDLClosedVal (-1)
  two_not_closed : ¬ EDLClosedVal 2
  half_not_closed : ¬ EDLClosedVal ((1 : ℝ) / 2)

theorem no_closed_edl_neg_one
    [EDLTranscendenceBarrier] :
    ¬ ∃ t : EDLTerm, t.IsClosed ∧
      ∀ env : Nat → ℝ, t.eval? env = some (-1 : ℝ) := by
  rintro ⟨t, ht, h⟩
  exact EDLTranscendenceBarrier.neg_one_not_closed
    (edl_closed_eval_in_closedVal ht (fun _ => 0) (h _))
```

This is candidate **(a)** from your list. Candidate **(b)** is premature unless you can state the exact finite exponential-polynomial consequence of Schanuel for one target such as `log 2`. Candidate **(c)** is too optimistic: a valuation invariant strong enough to exclude all integers would itself be deep transcendence theory in disguise.

**Mathlib infrastructure pointers.**
Use `Mathlib.Analysis.SpecialFunctions.Log.Basic`, `Mathlib.Analysis.SpecialFunctions.Exp`, `Mathlib.NumberTheory.Transcendental.Lindemann.*`, `Mathlib.RingTheory.Algebraic`, and `Mathlib.Data.Set.Countable`. For a "thinness" lemma, `Set.Countable` is enough:

```lean
def ClosedEDLValues : Set ℝ :=
  {v | ∃ t : EDLTerm, t.IsClosed ∧ ∃ env, t.eval? env = some v}

theorem closedEDLValues_countable : ClosedEDLValues.Countable := ...
```

But countability only proves "almost every real is unreachable"; it proves nothing about `-1`, `2`, or `1/2`, since `ℚ` itself is countable. The proposed "fixed transcendence-degree extension of `ℚ(e)`" is also probably false under Schanuel: iterates like `e`, `exp e`, `exp (exp e)`, … should generate unbounded transcendence degree, not a one-dimensional field.

**Cross-direction notes.**
This direction shares obstruction language with direction (3), but not much Lean infrastructure. The useful shared product is a clean syntax/value closure API: `ClosedVal`, `IsClosed`, `eval_closed_mem`, and `Countable` lemmas.

---

## (2) EReal lift for the three §G boundary points

**Verdict — tractable now, but only if scoped narrowly.**
The right move is not a full `EMLTermℂ` replacement. Mathlib's extended exponential/logarithm are split across `EReal` and `ENNReal`: `EReal.exp : EReal → ENNReal`, while `ENNReal.log : ENNReal → EReal`, and they form an order isomorphism. That is exactly useful for `log 0 = ⊥` and `exp ⊥ = 0`, but it is not a signed real or complex logarithm.

Your proposed guard "`vb ≠ 0` and `vb ≠ ⊥`" is wrong for the §G goal: excluding `0` kills the very boundary you want. The guard should allow `0`, allow positive finite values, probably allow `⊤`, and reject negative finite values and `⊥`.

**Recommended target lemma.**
First define a tiny extended-domain log adapter and prove the three direct templates. Do not relift every builder yet.

```lean
def EReal.IsENNRealLike (x : EReal) : Prop :=
  x = ((x.toENNReal : ENNReal) : EReal)

noncomputable def logE? (x : EReal) : Option EReal :=
  if hx : x.IsENNRealLike then
    some (x.toENNReal.log)
  else
    none

noncomputable def subE? (a b : EReal) : Option EReal :=
  -- reject the only indeterminate form needed for `exp a - log b`
  if a = ⊤ ∧ b = ⊤ then none else some (a - b)

noncomputable def emlE? (a b : EReal) : Option EReal := do
  let lb ← logE? b
  let ea : EReal := (a.exp : ENNReal)
  subE? ea lb

theorem logE_zero : logE? 0 = some (⊥ : EReal) := by
  ...

theorem exp_half_log_zero :
    ((((1 / 2 : ℝ) : EReal) * (⊥ : EReal)).exp : ENNReal) = 0 := by
  -- use positive scalar times ⊥ = ⊥, then `EReal.exp_bot`
  ...

theorem sqrt_templateE_zero :
    sqrtTemplateE 0 = some (0 : EReal) := by
  ...

theorem arcosh_templateE_one :
    arcoshTemplateE 1 = some (0 : EReal) := by
  ...

theorem hypot_templateE_zero_zero :
    hypotTemplateE 0 0 = some (0 : EReal) := by
  ...
```

The important warning is that `EReal` arithmetic has deliberate conventions at infinities: Mathlib sets problematic additions such as `⊥ + ⊤` by convention, and subtraction inherits those conventions. So an `Option` layer is still necessary; otherwise `⊤ - ⊤` silently becomes a value.

**Mathlib infrastructure pointers.**
Use `Mathlib.Data.EReal.Basic`, `Mathlib.Data.EReal.Operations`, `Mathlib.Data.EReal.Inv`, `Mathlib.Analysis.SpecialFunctions.Log.ERealExp`, and `Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp`. For the order/topology framing, `EReal` is already a `CompleteLinearOrder`, and `EReal.exp`/`ENNReal.log` are order isomorphisms/homeomorphisms.

**Cross-direction notes.**
This helps SI #7 only as infrastructure: it gives a faithful language for `⊥ = -∞`. It does not by itself eliminate `-∞`; it more strongly suggests that `-∞` is a natural semantic boundary, not a disposable artifact. For the main artefact, I would leave §G documented unless you want a separate "faithful extended-real semantics" chapter.

---

## (3) Universal minimality, paper §5

**Verdict — premature as stated.**
As a mathematical statement, universal minimality is not well-posed until you choose a function class for `B`. With arbitrary `B : ℝ × ℝ → ℝ`, pathological encodings can hide a whole evaluator inside one binary operation. With merely continuous `B`, the question is still too broad; Kolmogorov–Arnold-style superposition results warn against naive dimensional or "continuous functions are too simple" arguments. Clone theory is the right external vocabulary, but it is a research programme, not a ready Mathlib tactic. Clones are precisely the closure of operations under projections and composition; that matches your term-generation question.

The paper's own warning at §5 is correct: simple diagonal arguments like "`B(x,x)` is constant" fail, as the `B(x,y)=x-y/2` example shows. In arXiv-v2 HTML, this is §5 lines 257–260; the same section also states the real-only conjectural obstruction.

**Recommended target lemma.**
Do not try to prove "no binary `B`". Prove "no polynomial binary `B`". This is clean, nontrivial, and avoids the diagonal trap.

```lean
inductive BTerm where
  | var : Nat → BTerm
  | const : ℝ → BTerm          -- include this if you want `{c, B}`
  | app : BTerm → BTerm → BTerm

noncomputable def BTerm.eval
    (B : ℝ → ℝ → ℝ) (env : Nat → ℝ) : BTerm → ℝ := ...

def IsPolynomialBinary (B : ℝ → ℝ → ℝ) : Prop :=
  ∃ P : MvPolynomial (Fin 2) ℝ,
    ∀ x y, B x y = MvPolynomial.eval ![x, y] P

theorem polynomial_binary_terms_are_polynomial
    {B : ℝ → ℝ → ℝ} (hB : IsPolynomialBinary B)
    (t : BTerm) :
    ∃ P : Polynomial ℝ,
      ∀ x, BTerm.eval B (fun _ => x) t = P.eval x := by
  induction t with
  | var n => exact ⟨Polynomial.X, by simp [BTerm.eval]⟩
  | const c => exact ⟨Polynomial.C c, by simp [BTerm.eval]⟩
  | app a b iha ihb =>
      -- compose the binary polynomial witness for B with the two unary polynomial witnesses
      ...

theorem no_polynomial_binary_generates_exp
    {B : ℝ → ℝ → ℝ} (hB : IsPolynomialBinary B) :
    ¬ ∃ t : BTerm,
      ∀ x : ℝ, BTerm.eval B (fun _ => x) t = Real.exp x := by
  rintro ⟨t, ht⟩
  obtain ⟨P, hP⟩ := polynomial_binary_terms_are_polynomial hB t
  -- use `Polynomial.tendsto_div_exp_atTop P`
  -- if P.eval x = exp x for all x, then P.eval x / exp x = 1,
  -- contradicting the limit 0.
  ...
```

This is a genuine step beyond the two pigeonhole corollaries. It rules out a large natural class and survives the `x - y/2` trap: that operator can generate constants, but all its terms remain polynomial, hence cannot generate `exp`.

**Mathlib infrastructure pointers.**
Use `Mathlib.Data.MvPolynomial.Basic`, `Mathlib.Data.Polynomial.Eval`, `Mathlib.Analysis.SpecialFunctions.PolynomialExp`, and possibly `Mathlib.FieldTheory.RatFunc.*` if you later upgrade from polynomial to rational `B`. Mathlib already has `Polynomial.tendsto_div_exp_atTop`, exactly the growth lemma needed to show no polynomial is `Real.exp`.

**Cross-direction notes.**
Direction (1) and direction (3) both benefit from "syntax-generated semantic class" lemmas. But direction (3) should stay in algebraic/analytic classes first: polynomial, rational, semialgebraic, Pfaffian, real-analytic with finite expression complexity. "All continuous `B`" is too big.

---

## (4) The seven SI §1.5 questions

**Verdict — tractable now only for #5 and small pieces of #4/#7.**
Your intuition is mostly right, but I would demote #2: a syntactic non-repeating enumerator is easy, while a semantic Stern–Brocot analogue is a serious normal-form problem because EML has many non-obvious identities.

**Tractability ranking for Lean deliverables.**

1. **#5 variable-transplant depths** — best target. Positive identities are easy to verify; bounded-depth nonexistence can be added later by finite enumeration.
2. **#4 leaf-only evaluation** — good definitions, easy positive/negative audits of existing witnesses.
3. **#7 `−∞` elimination** — shares direction (2) machinery; valuable but higher effort.
4. **#2 canonical form** — tractable only syntactically at first; semantic uniqueness is premature.
5. **#3 constant-free binary Sheffer** — tractable only after choosing a class such as polynomial/rational `B`; otherwise direction (3).
6. **#6 real-only Sheffer** — broad, likely open, and entangled with complex/trig completeness.
7. **#1 taxonomy** — most premature; it needs a parameter space of operators before Lean can help.

**Recommended target lemma.**
Pick #5. Formalize the known depth-4 identity as a reusable transplant combinator.

```lean
def EMLTerm.depth : EMLTerm → Nat
  | .one => 0
  | .var _ => 0
  | .eml a b => Nat.succ (max a.depth b.depth)

def EMLTerm.subst (σ : Nat → EMLTerm) : EMLTerm → EMLTerm := ...

theorem eval_subst
    {t : EMLTerm} {σ : Nat → EMLTerm}
    (env : Nat → ℝ)
    (hσ : ∀ n, (σ n).eval? env = some (env n)) :
    (t.subst σ).eval? env = t.eval? env := by
  induction t <;> simp [EMLTerm.subst, EMLTerm.eval?, *]

def id4 : EMLTerm := ...  -- existing sealed depth-4 identity

theorem id4_eval :
    ∀ env : Nat → ℝ, id4.eval? env = some (env 0) := ...

theorem id4_depth : id4.depth = 4 := ...

def transplant4 (t : EMLTerm) : EMLTerm :=
  id4.subst (fun n => if n = 0 then t else .var n)

theorem transplant4_eval
    {t : EMLTerm} {env : Nat → ℝ} {v : ℝ}
    (ht : t.eval? env = some v) :
    (transplant4 t).eval? env = some v := by
  ...
```

A stronger follow-up is:

```lean
theorem identity_terms_at_depth_multiples_of_four
    (k : Nat) :
    ∃ t : EMLTerm,
      t.depth = 4 * k ∧
      ∀ env : Nat → ℝ, t.eval? env = some (env 0) := ...
```

This gives a Lean-checkable answer to the "multiples of 4" part of SI #5, not just another prose note.

**Mathlib infrastructure pointers.**
Mostly artefact-internal: `EMLTerm.depth`, `subst`, `containsVar`, and `eval?`. For bounded search certificates, use `List`, `Finset`, `Fintype`, and generated counterexample lemmas. For #7, reuse the `EReal` modules from direction (2).

**Cross-direction notes.**
#3 and #6 are direction (3). #7 is direction (2). #1 needs direction (3)'s function-class decision. #5 is the cleanest standalone SI contribution.

---

## Overall ranking

Highest-value next target: **direction (4), SI #5**, specifically the transplant-depth development. It is the best ratio of impact to effort: finite syntax, no external mathematics, no new semantic universe, and a result that directly answers one of the author's SI questions with Lean code.

Second: **direction (2), narrow EReal templates** for `√0`, `arcosh 1`, and `hypot(0,0)`. Do this only as a small faithful-boundary semantics file, not as a wholesale compiler relift. The key correction is to allow `log 0 = ⊥`; the guard must not reject zero.

Third: **direction (1), closed-EDL closure plus countability**, with nonmembership left as a named transcendence barrier. This is useful architecture, but it will not solve D5/D6/D7 without a genuine Schanuel-style theorem.

Last: **direction (3) universal minimality as stated**. It is not a Lean problem yet; choose a function class first. The polynomial-binary obstruction is the right first serious lemma.

---

## Mathlib references cited

- [`Mathlib.Analysis.SpecialFunctions.Log.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Log/Basic.html)
- [`Mathlib.Analysis.SpecialFunctions.Log.ERealExp`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Log/ERealExp.html)
- [`Mathlib.Data.EReal.Operations`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/EReal/Operations.html)
- [`Mathlib.Data.EReal.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/EReal/Basic.html)
- [`Mathlib.Analysis.SpecialFunctions.PolynomialExp`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/PolynomialExp.html)
- [arXiv:2203.14054 — Universal clone algebra](https://arxiv.org/pdf/2203.14054)
- [arXiv:2603.21852v2 — Odrzywołek, "All elementary functions from a single operator"](https://arxiv.org/html/2603.21852v2)
