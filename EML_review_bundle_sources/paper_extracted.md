# Paper extraction — arXiv:2603.21852

> "All elementary functions from a single binary operator"
> Andrzej Odrzywołek
> Categories: cs.SC (primary), cs.LG (secondary)
> MSC: 26A09 (primary); 08A40, 68W30
> Length: ~7-8 pages
> License: CC BY 4.0

This file was extracted via WebFetch on 2026-05-01. It is the seed material
for the EML auto-formalization workspace and is re-read by every agent that
participates in decomposition or formalization. Do **not** re-fetch the paper
unless this file is missing or the agent specifically detects a fact that
contradicts it.

---

## Abstract

The paper demonstrates that a single binary operator,
`eml(x,y) = exp(x) − ln(y)`, combined with the constant `1`, can generate
all standard scientific calculator operations. This includes constants
(e, π, i), arithmetic operations (addition through exponentiation), and
transcendental/algebraic functions. The author discovered this through
exhaustive search and proposes EML (Exp-Minus-Log) form as a uniform binary
tree structure. The work also demonstrates feasibility of recovering exact
elementary functions from numerical data using gradient-based symbolic
regression with trainable EML circuits at shallow tree depths.

## Section structure

1. **Introduction** — Establishes historical context; motivates the search
   for a single universal operator for elementary functions.
2. **Methods** — Systematic ablation testing approach; hybrid numeric
   bootstrapping verification using algebraically independent transcendental
   constants (e.g. Euler-Mascheroni γ ≈ 0.577216).
3. **Results** — Discovery chain (Figure 1); progressive reduction from
   36-button calculator to EML; introduces EDL and negated-EML variants.
4. **Usage and Applications**
   - 4.1 EML compiler
   - 4.2 Elementary functions as binary trees and analog circuits
   - 4.3 Symbolic regression by continuous optimization
5. **Conclusions and Open Questions**

---

## Numbered identities (literal)

**Identity 1** (Exp-Log reduction)
- `x × y = exp(ln x + ln y)`
- `x + y = ln(exp(x) × exp(y))`

**Identity 2** (Euler's formula)
- `exp(i·φ) = cos(φ) + i·sin(φ)`

**Equation 3** (EML operator definition)
- `eml(x, y) = exp(x) − ln(y)`

**Identity 4a** (EML variant with constant 1)
- `eml(x, y) = exp(x) − ln(y)`     constant: `1`

**Identity 4b** (EDL variant with constant e)
- `edl(x, y) = exp(x) / ln(y)`     constant: `e`

**Identity 4c** (negated-EML variant)
- `−eml(y, x) = ln(x) − exp(y)`    constant: `−∞`

**Identity 5** (natural logarithm in EML form)
- `ln(z) = eml(1, eml(eml(1, z), 1))`

**Identity 6** (master-formula input parameterization)
- `α_i + β_i·x + γ_i·f`            (per node, `f` = result of previous EML)

**Successor identity** (mentioned in passing)
- `suc(inv(pre(inv(suc(inv(x)))))) = 1/(1/(1/x + 1) − 1) + 1 = −x`

---

## EML expression catalog (Tables 4 + scattered)

| Item             | EML form                              | EML compiler K | Direct search K |
|------------------|---------------------------------------|----------------|-----------------|
| 1 (constant)     | `1`                                    | 1              | 1               |
| identity x       | `x`                                    | 1              | 9               |
| 0                | (7 instructions)                       | 7              | —               |
| e                | `eml(1, 1)`                            | 3              | 3               |
| −1               | (17 instructions)                      | 17             | —               |
| 2                | (27 instructions)                      | 27             | 19              |
| 1/2              | (91 instructions)                      | 91             | 29              |
| π                | (193 instructions)                     | 193            | >53             |
| i                | (131 instructions)                     | 131            | >55             |
| exp(x)           | `eml(x, 1)`                            | 3              | 3               |
| ln(x)            | `eml(1, eml(eml(1, x), 1))`            | 7              | 7               |
| −x               | (57 instructions)                      | 57             | 15              |
| 1/x              | (65 instructions)                      | 65             | 15              |
| x²               | (75 instructions)                      | 75             | 17              |
| √x               | (139 instructions)                     | 139            | >43             |
| x + y            | (27 instructions)                      | 27             | 19              |
| x − y            | (83 instructions)                      | 83             | 11              |
| x × y            | (41 instructions)                      | 41             | 17              |
| x / y            | (105 instructions)                     | 105            | 17              |
| x^y              | (49 instructions)                      | 49             | 25              |
| log_x(y)         | (117 instructions)                     | 117            | 29              |

> "K" denotes the size of the RPN code (number of EML/leaf nodes in the binary
> tree). The full literal trees for the larger entries are in the paper's
> Supplementary Information; we will defer those during the first pass.

## Calculator-configuration ablation (Table 2)

| Config   | Constants | Unary ops              | Binary ops | Count |
|----------|-----------|------------------------|------------|-------|
| Wolfram  | π, e, i   | ln                     | +, ×, ∧    | 7     |
| Calc 3   | none      | exp, ln, −x, 1/x       | +          | 6     |
| Calc 2   | none      | exp, ln                | −          | 4     |
| Calc 1   | e or π    | none                   | x^y, log_x(y) | 4     |
| Calc 0   | none      | exp                    | log_x(y)   | 3     |
| **EML**  | **1**     | **none**               | **eml**    | **3** |

Each row of this table corresponds to a "calculator universality" lemma we
will likely formalize as: "any elementary function expressible in row N is
expressible in row N+1".

## Starting basis (Table 1) — 36 primitives

- **Constants** (8): π, e, i, −1, 1, 2, x, y
- **Unary functions** (20): exp, ln, inv, half, minus, √·, sqr, σ (sigmoid),
  sin, cos, tan, arcsin, arccos, arctan, sinh, cosh, tanh, arsinh, arcosh,
  artanh
- **Binary operations** (8): +, −, ×, /, log, pow, avg, hypot

## Grammar of EML expressions

```
S → 1 | eml(S, S)
```

Context-free language; isomorphic to full binary trees / Catalan structures.

---

## Master formula (§4.3) — for the symbolic regression part

Level-`n` EML master formula has `5 × 2^n − 6` parameters total. Each EML
input is parameterized as a linear combination `α_i + β_i·x + γ_i·f`, where
`f` is the running result. The Gumbel-Softmax reparameterization converts
3 coefficients per node into normalized probabilities over `{1, x,
previous result}`.

This part is a numerical/learning method; it is **not** the target of the
formalization pass. We may formalize the parameter-count formula but skip
the optimization machinery.

## Methodology — numeric bootstrapping

Substitute algebraically independent transcendental constants (typically
Euler-Mascheroni γ) for the symbolic variables x, y, then compare numerical
output to the candidate formula via the "inverse symbolic calculator". This
is a verification methodology, not a theorem.

## What we WILL formalize

- The `eml` operator definition (over ℝ; complex-valued versions deferred).
- Trivial identities: `eml(x, 1) = exp(x)`, `eml(1, 1) = e`.
- The natural-log identity `ln z = eml(1, eml(eml(1, z), 1))` (with positivity
  side conditions on `z`).
- A formal EML term type: `inductive EMLTerm | one | eml : EMLTerm → EMLTerm → EMLTerm`
- An evaluation function `eval : EMLTerm → ℝ`.
- A few small `EMLTerm` values for `e`, `exp(x)`, `ln(x)` and the matching
  `eval` lemmas.
- Calculator-equivalence steps from Table 2 (each as a small lemma about the
  generating set growing or shrinking).

## What we WILL DEFER (or skip)

- Literal `EMLTerm` values for π, i, √·, sin, cos, tan, sinh, … (the 53-193
  instruction trees). These would require either copying the trees verbatim
  from the Supplementary Information, or proving "there exists an EMLTerm
  with eval = …" non-constructively.
- The full completeness theorem ("EML + 1 generates all 36 primitives") — the
  paper itself defers this to Supplementary. We'll state it as a target with
  `sorry` and pass each sub-case as a separate Aristotle submission.
- Symbolic regression / training / softmax part.
- Numeric bootstrapping verification.

## Mathlib lemmas we expect to lean on

- `Real.exp`, `Real.log`, `Real.exp_log`, `Real.log_exp`, `Real.exp_zero`,
  `Real.log_one`, `Real.log_pos`, `Real.exp_pos`
- `Real.exp_add`, `Real.log_mul`
- `Real.exp_log_eq_iff` (positivity)
- `Complex.exp`, `Complex.exp_pi_mul_I` (for the optional complex `i` lemmas)
