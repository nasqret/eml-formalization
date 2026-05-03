---
title: "Auto-formalizing Mathematics: a Swiss Army Knife"
author: "dr Bartosz Naskręcki"
theme: simple
highlightTheme: atom-one-light
css: assets/theme.css
revealOptions:
  transition: fade
  slideNumber: true
  controls: true
  progress: true
  hash: true
  margin: 0.04
  width: 1280
  height: 720
---

<!-- .slide: class="title-slide" -->

# Auto-formalizing Mathematics

## A Swiss Army Knife

Aristotle + Claude + Codex + Mathematica + Human

**dr Bartosz Naskręcki**

Faculty of Mathematics and Computer Science, Adam Mickiewicz University · Center for Trustworthy AI, Warsaw University of Technology

*Falenty · April 2026*

`github.com/nasqret/falenty-2026`

---

<!-- .slide: class="compact" -->

## Map of the talk

1. **What is proof formalization?** Lean 4, Mathlib, Curry-Howard.
2. **The new generation of AI provers.** Why 2025 is different.
3. **The case study.** A paper claiming "all elementary functions from a single binary operator".
4. **The factory.** Aristotle, Claude, Codex, Mathematica + a human assemble 66 verified Lean chunks.
5. **The mathematics.** EML, witnesses for `e`, `2`, `pi`.
6. **Lessons.** What worked, what hurt, what comes next.

---

<!-- .slide: class="compact" -->

## What is proof formalization?

A **formal proof** is a Lean 4 term whose type matches the theorem statement.
Lean's kernel (~2 000 lines, the *de Bruijn criterion*) checks every step.

Mathlib v4.28 ships ~1.5M lines of formalized mathematics — analysis, algebra, topology, combinatorics.

> Peer review misses an estimated 5% of mathematical errors.
> A Lean kernel misses **none** of those expressible in its type theory.

This talk: how a small team (one human + several AI assistants) sealed a 7-page paper into 66 machine-checked artefacts in three days.

---

<!-- .slide: class="figure-short compact" -->

## Curry-Howard, in one slide

<img src="assets/curry_howard.svg" alt="Curry-Howard"/>

A function `λx : A. x : A → A` is **the same object** as the proof of the implication `A ⇒ A`.
Lean is, internally, an extended lambda calculus with dependent types.

**Consequence:** "send a Lean proof" means *send a typed program*; "verify it" means *type-check the program*.

---

<!-- .slide: class="compact" -->

## The new generation of AI provers

| System | Year | Highlight |
|---|---|---|
| AlphaGeometry / AlphaProof | 2024 | IMO 2024, silver |
| Aristotle (Harmonic) | 2025 | IMO 2025, gold (5/6) |
| DeepSeek-Prover, Kimina | 2024-25 | open-source autoformalization |
| GPT-5.2 Pro + Aristotle | 2026 | Erdős #728 closed autonomously |

What changed: large language models compose with **tactic search** and **RL on Lean traces**. The output is checked by the kernel — zero hallucinations survive verification.

---

<!-- .slide: class="compact" -->

## Aristotle in 60 seconds

- **Where it lives:** Harmonic AI's cloud queue.
- **What you send:** a Lean 4 statement (with imports + spec).
- **What you get back:** a `.lean` file plus a project archive.
- **Surface:** `arist submit`, `arist list`, `arist result <id>`.
- **Concurrency:** ~10 active slots, billed per job.
- **Strength:** one-step lemmas, simp-able identities, small existentials.
- **Weakness:** long, chained existential constructions.

Wall-clock per job in our experiment: 8 minutes to 8 hours.

---

<!-- .slide: class="compact" -->

## The paper

A 7-page paper plus supplementary, claiming:

> "All elementary functions can be derived from a single binary operator on the reals."

The operator (the **EML**, *exp-minus-log*):

$$\mathrm{eml}(x, y) \ =\ \exp(x) - \ln(y).$$

36 primitives in the paper's Table 1: `e, 0, -1, 2, 1/2, exp, log, x+y, x*y, x^y, sin, cos, sqrt, pi, i, ...`.

**Goal:** machine-check every claim in Lean 4 + Mathlib.

---

<!-- .slide: class="figure-tall compact" -->

## The factory

<img src="assets/formalization_factory.svg" alt="formalization factory"/>

Decompose → three parallel lines (Aristotle / Mathematica / manual) → QC (`lake env lean`) → five packaging artefacts.
Output: **`nasqret/falenty-2026`**, 66 chunks all `lake env lean` exit 0; ~5 000 lines of Lean, 31-page LaTeX report, 54-page hybrid PDF, 47-page HTML site, 16 git commits.

---

<!-- .slide: class="compact" -->

## Decomposition methodology

Each chunk is a self-contained directory: `chunk.md` (paper text + Lean target + deps), `meta.json` (status, project_id, history), `target.lean`, `result.lean`. Bilingual end-to-end.

| Group | # | Examples |
|---|---|---|
| Foundations | 5 | `def eml`, `EMLTerm`, `eval` |
| Identities | 12 | Identity 5, `exp(x) = eml(x,1)` |
| Calc-equiv | 7 | Wolfram → Calc 3 → … → EML |
| Constants | 6 | `0, -1, 1/2, 2, e`, `pi, i` (complex) |
| Functions | 15 | `-x, 1/x, x^2, sqrt, x+y, x*y, x^y, x/y` |
| Trig | 8 | `sinh, cosh, tanh, sin, cos, tan, arctan` |
| Master / misc | 13 | umbrellas, Catalan count, sigmoid |

Difficulty distribution (levels 1–5): 11 / 10 / 6 / 19 / 20.

---

<!-- .slide: class="compact" -->

## Mathematica's role

Mathematica plays the **enumeration + signature-dedup** role.

- **v1**: brute-force enumeration + `FullSimplify`. Stalled.
- **v2**: enumerate trees, evaluate at probe constants, dedup by numeric signature.

Numbers from one v2 run targeting `e`:

| Quantity | Count |
|---|---|
| Trees enumerated up to size 31 | 3.8 M |
| Unique numeric signatures | 3.1 M |
| Witnesses confirmed (`e, exp, 2`) | 3 |
| Witnesses for `pi / i / sqrt(x)` | **0** |

**Bridge:** MMA validates a witness numerically; Lean composes the proof; Aristotle (or the human) closes.

---

<!-- .slide: class="figure-mid compact" -->

## Aristotle's role

- 25+ submissions across **5 waves** over a 36-hour window.
- ~10 concurrent slots; overnight rate-limit stall ~6 h.
- One-step identities: ~10 minutes per chunk.
- Long existentials (size > 30): hours, often `COMPLETE_WITH_ERRORS`.

<img src="assets/spec_cycle.svg" alt="spec-tightening cycle"/>

Of 15 wave-3 submissions, 9 returned a clean proof on the first pass.

---

<!-- .slide: class="figure-mid compact" -->

## Claude's role

- **Design.** Chunk schema, factory architecture, calc-equiv inductives, the `EMLTermℂ` extension for `pi` / `i`.
- **Coordination.** Parallel agents, queue monitoring, batch fetching, manifest dedupe, commit cadence.
- **Scaffolding.** REPL command (`/eml`, `/ac`), HTML site generator, LaTeX report.

<img src="assets/dispatch.svg" alt="multi-agent dispatch"/>

---

<!-- .slide: class="compact" -->

## Codex (OpenAI) role

Powered by the OpenAI APIs, configured via `~/.config/openai/env`:

- **Paraphrase generation** for chunk markdown (`ch explore --paraphrase`).
- **Quiz LLM judge** for the lecture's interactive layer.
- **Informalization** of Aristotle's Lean proofs back to natural-language prose (`arist informal`).
- **Bilingual narration** of the hybrid report.

Codex is the *quick-cut blade*: cheap, fast, perfect for textual shape-shifting where ground-truth verification is not the bottleneck.

---

<!-- .slide: class="compact" -->

## The Human role

**What the human did:**

- **Scope.** "Seal the trig family or not?" "Accept primed types?"
- **Quality calls.** Did Aristotle's rich grammar count, or do we recompose?
- **Sign-offs.** Every commit, every wave, every push.
- **Choosing waves.** When to fire, when to wait out the rate limit.

**What the human did NOT do:** write Lean proofs by hand (except the 514-line manual umbrella); mechanically extract chunks; set up monitors.

The verdict: **human-in-charge, not human-out-of-the-loop.**

---

<!-- .slide: class="figure-tall compact" -->

## Wave timeline

<img src="assets/wave_timeline.svg" alt="wave timeline"/>

Five Aristotle waves, manual fixes, then the final umbrellas. Most wall-clock was Aristotle queue waiting; productive *human* time was under a working day.

---

<!-- .slide: class="compact" -->

## When the negatives helped

- **`Project failed` / `no project_id`.** Aristotle's CLI prints the id to *stderr* → added stderr fallback to the extractor.
- **`COMPLETE_WITH_ERRORS`.** Aristotle silently extended the grammar (extra `const : R → EMLTerm`) → manual-composition pass for pure-grammar witnesses.
- **Junk-value `Real.log 0 = 0`.** Forced spec tightenings: `∀ x : R` → `∀ x > 0` on `037, 038, 041, 042`.
- **Mathematica search exhausted at size 31.** Confirmed the paper's `K`-bound for `pi / i / sqrt(x)`; led to the `EMLTermℂ` extension.

---

<!-- .slide: class="compact" -->

## The mathematics — the operator

The EML algebra:

$$\mathrm{eml}(x, y) \ =\ \exp(x) - \ln(y).$$

**Identity 5** (the workhorse):

$$\ln(z) \ =\ \mathrm{eml}\bigl(1,\ \mathrm{eml}(\mathrm{eml}(1, z),\ 1)\bigr), \qquad z > 0.$$

Inner $\mathrm{eml}(1,z) = e - \ln z$; next $\mathrm{eml}(e-\ln z, 1) = \exp(e-\ln z)$;
outer $\mathrm{eml}(1, \exp(e-\ln z)) = e - (e - \ln z) = \ln z$.

Simplest witness: $\mathrm{eml}(1,1) = e^1 - \ln 1 = e.$

---

<!-- .slide: class="compact" -->

## A full Lean witness — `2` (chunk 032)

```lean
private def t₂ : EMLTerm := .eml .one .one
private def t₃ : EMLTerm := .eml .one t₂
private def t₅ : EMLTerm := .eml (.eml .one t₃) .one
private def t₆ : EMLTerm := .eml .one t₅
private def t₇ : EMLTerm := .eml t₆ t₂
private def witness : EMLTerm := .eml .one (.eml t₇ .one)

private lemma e_minus_one_pos : (0 : ℝ) < Real.exp 1 - 1 := by
  linarith [Real.add_one_le_exp (1 : ℝ)]

theorem emlterm_for_two : ∃ t : EMLTerm, EMLTerm.eval t = 2 :=
  ⟨witness, by
    simp [witness, EMLTerm.eval, Real.log_exp,
          Real.exp_log e_minus_one_pos]; ring⟩
```

8 helper lemmas; the witness tree has size 11.

---

<!-- .slide: class="figure-mid compact" -->

## The pi witness — and Euler

<img src="assets/pi_tree.svg" alt="pi witness tree"/>

For trig chunks we extend to `EMLTermℂ₁` and chain Euler:
$\cos x = \tfrac{1}{2}(e^{ix}+e^{-ix})$, $\sin x = \cos(x-\tfrac{\pi}{2})$.

---

<!-- .slide: class="compact" -->

## Panorama of proof steps

| Status | Count | Note |
|---|---|---|
| Literal EML witnesses | 62 | Pure-grammar trees, any size |
| Closed-form identities | 4 | `pi, i, sqrt(x)` plus one calc-equiv |
| Total verified by `lake env lean` | **66 / 66** | exit 0 |

By inductive type:

- `EMLTerm` — closed witnesses (`e, 0, -1, 1/2, 2`).
- `EMLTerm₁` — one-variable functions (`-x, 1/x, x^2, cosh, …`).
- `EMLTerm₂` — two-variable functions (`+, *, ^, /, log_x y, hypot, …`).
- `EMLTermℂ`, `EMLTermℂ₁` — complex extensions (`pi, i, sin, cos, tan, arctan`).
- `Calc3R`, `Calc2`, `Calc1`, `Calc0` — the 5-step Wolfram-to-EML reduction.

---

<!-- .slide: class="compact" -->

## Tools and time

| Tool | Role | Wall-clock | Output |
|---|---|---|---|
| Aristotle | proof search | ~24 h queue | 25+ project archives |
| Mathematica | enumerate + dedup | ~3 h | 3.8 M trees, 3 witnesses |
| Claude | orchestration + composition | ~8 h active | scaffolding, agents, REPL |
| Codex | paraphrase, informalization | ~1 h | bilingual layer |
| Lean | ground truth | seconds / chunk | 66 / 66 exit 0 |
| Human | scope, taste, commits | ~6 h active | 16 commits |

Total elapsed: ~3 days. Active work: under one engineering day.

---

<!-- .slide: class="compact" -->

## Why it succeeded

1. **Atomic decomposition** — each chunk fits in one Aristotle submission.
2. **Ground truth** — `lake env lean` exit 0 is the only acceptance.
3. **Iterative spec tightening** — `∀ x` → `∀ x > 0` is cheap.
4. **Honest partial accounting** — `COMPLETE_WITH_ERRORS` is data, not failure.
5. **Multi-tool diversification** — when MMA dies, Lean composes; when Aristotle stalls, the human writes the umbrella.
6. **Version control as audit trail** — 16 commits = a replayable history of every decision.

---

<!-- .slide: class="compact" -->

## Future prospects

- Seal the 4 closed-form-only chunks with literal trees (size > 100).
- A universal pipeline for *any* paper of this shape (definition + Table-of-witnesses).
- **Acorn** integration (the new tactic-suggestion service).
- Faster Aristotle as Harmonic ramps capacity.
- Fully autonomous loops: doable, but accept the risk of silent grammar drift.
- A larger paper portfolio — the EML push was a pilot.

---

<!-- .slide: class="compact" -->

## Can we remove the human?

Not yet, and not for the right reasons.

- The human holds **scope** ("do we seal trig?"), **taste** ("recompose or accept primed types?") and **commit authority**.
- Mechanical work is increasingly machine-handled; the human's *time* shifts from typing to deciding.
- Forecast for 2027: human-IN-charge, not human-OUT-of-loop. The loop closes around a human who specifies *what counts*.

> Removing the human means removing the question of what counts as a proof *worth having*. That is not a verification problem.

---

<!-- .slide: class="figure-tall" -->

## The Swiss army knife

<img src="assets/swiss_knife.svg" alt="Swiss army knife"/>

Repo: `github.com/nasqret/falenty-2026` · License: MIT.

---

<!-- .slide: class="compact" -->

## Q & A

**Repo:** `github.com/nasqret/falenty-2026`

**Hybrid report:** `lambda_lab/proofs/eml/2603_21852/report/`

**Interactive site:** `docs/`

**Contact:** *bartosz.naskrecki at amu.edu.pl*

Thank you.
