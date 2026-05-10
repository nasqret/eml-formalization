# EML Tree Builder

Interactive in-browser compiler for arXiv:2603.21852.
Type a mathematical function; it builds the complete `EMLTerm` tree
using only `1`, variables, and `eml(a, b) = exp(a) − log(b)`.

## What it shows

- The compiled EML tree (SVG, hover the `eml` nodes for the
  sub-expression each one computes).
- The K-count (RPN length) — matches `K_count_*` theorems in
  `EML.Framework.KCounting`.
- Tree depth, leaf count, and `eml`-node count.
- The full RPN string in the paper's notation
  (`E` for the `eml` operator).

## Run locally

It's a pure static page — open `index.html` in a browser, or:

```bash
cd web/eml-tree-builder
python3 -m http.server 8080
# visit http://localhost:8080
```

No build step, no dependencies.

## What's supported

| Category | Names |
|---|---|
| Atoms | `1`, `0`, `2`, integer literals, `e`, `π` (`pi`), variables (any single letter) |
| Real unaries | `exp`, `log`/`ln`, `neg`, `inv`, `sq`, `sqrt`, `halve`, `sigma`/`sigmoid` |
| Hyperbolic | `sinh`, `cosh`, `tanh`, `arsinh` (`asinh`), `arcosh` (`acosh`), `artanh` (`atanh`) |
| Real binaries | `+`, `-`, `*` (`·`, `×`), `/` (`÷`), `^`, `hypot`, `pow`, `logb`/`log_b`, `avg`/`mean` |

## What's *not* supported in the browser tool

The trigonometric primitives (`sin`, `cos`, `tan`, `arcsin`, `arccos`,
`arctan`) are sealed in the formal artefact via the **complex** EML
grammar (`EMLTermℂ`) using Euler-bridge witnesses — the witnesses use
`i` and `Complex.log` of values whose argument crosses the principal
branch cut. The browser tool currently shows only the real-fragment
compile; typing `sin(x)` returns an explanatory error.

The full sealed witnesses live in
[`EML.Framework.Complex.Closures.Trig`](../../lambda_lab/proofs/eml/2603_21852/lean_workspace/EML/Framework/Complex/Closures/Trig.lean)
and [`...Builders/Trig.lean`](../../lambda_lab/proofs/eml/2603_21852/lean_workspace/EML/Framework/Complex/Builders/Trig.lean).

## Recipes (verbatim from SI §2.1)

```
exp(z)  ↦  eml(z, 1)
ln(z)   ↦  eml(1, exp(eml(1, z)))    = eml(1, eml(eml(1, z), 1))
x − y   ↦  eml(ln(x), exp(y))
−z      ↦  ln(1) − z
x + y   ↦  x − (−y)
1/z     ↦  exp(−ln(z))
x · y   ↦  exp(ln(x) + ln(y))
x / y   ↦  x · (1/y)
```

Plus derived: `x²`, `x/2`, `(x+y)/2`, `√x`, `x^y`, `log_b y`,
`hypot(x, y)`, `σ(x)`, hyperbolic family.

## Architecture

| File | Role |
|---|---|
| `index.html` | Page structure |
| `style.css`  | Visual theme (colour-coded by node kind) |
| `eml.js`     | Parser, compiler (`F36 → EL → EML` macros), SVG renderer |

About 600 lines total; vanilla JS, no framework, no build step.

## Provenance

Same compile chain as
[`EML.Framework.Compilers.ELToEML`](../../lambda_lab/proofs/eml/2603_21852/lean_workspace/EML/Framework/Compilers/ELToEML.lean)
in the Lean artefact. K-counts will match for primitives that go
through the structural compiler; hand-tuned witnesses (the closed
constants `0`, `2`, `−i`, `i`, `π`) are smaller in the formal artefact
than the structural-compile sizes shown here, by design (the paper's
Table 4 lists the *upper bounds* the compiler-produced witnesses
inflate against).
