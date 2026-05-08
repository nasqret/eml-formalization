# Paper sourcing for `EML.Framework.Sheffer`

> Line-level pointers into Odrzywołek (arXiv:2603.21852) and the
> Supplementary Information PDF for everything that the
> [`Sheffer.lean`](../Sheffer.lean) scaffolding claims about EDL and −EML.

This file exists so that a future reader (or reviewer) can verify, with
no detective work, which lines of the paper our `Sheffer.lean` is
attempting to formalise. Any mismatch between this file and the paper
is a bug — please open an issue.

---

## §3.1 — The three Sheffer operators (paper lines 273–284)

Verbatim transcription of the relevant block from
`EML_review_bundle_sources/paper_source/EML.tex` (paper Section 3.1,
*"Three Sheffer operators"*):

> *"A month later I realized that it has at least two additional cousins:
> EDL and −EML."* (paper line 273)

The equation block — paper LaTeX `\label{Sheffers}` — gives:

```
eml(x, y)   = exp(x) − ln(y)     paired with constant   1     (the EML this paper proves complete)
edl(x, y)   = exp(x) / ln(y)     paired with constant   e     (cousin, conjectured complete)
−eml(y, x)  = ln(x) − exp(y)     paired with constant  −∞     (cousin, conjectured complete)
```

**Argument-order note.** The paper writes `−eml(y, x)` to make the
exponent/log-symmetric structure with `eml(x, y)` visible. In our
Lean scaffolding we follow Lean convention and use the same `(x, y) ↦
log(x) − exp(y)` argument order as our other binaries; the underlying
operator is identical.

**Status.**

- **EML.** Paper-proves per-primitive completeness for the 36 F36
  primitives. This artefact formalises that proof end-to-end (see
  `EML.Framework.PaperClaims`).
- **EDL.** Discovered by the paper but **completeness is empirical
  only**, via the Mathematica / Rust `VerifyBaseSet` procedure (paper
  line 287 onwards mentions running the procedure on the cousins; the
  formal proof is not given). Our scaffolding provides the grammar /
  partial-eval / collapse-identity skeleton; per-primitive completeness
  is **paper-open**. See Plan D in `OPEN_QUESTIONS.md`.
- **−EML.** Discovered by the paper but **completeness is empirical
  only**, same caveat as EDL. The paper's `−EML` requires `−∞` as its
  distinguished constant (`negEml(x, −∞) = log x − exp(−∞) = log x −
  0 = log x`). Our finite-real partial-eval cannot literalise `−∞`;
  closing −EML completeness in Lean would need Mathlib's `EReal`
  (extended reals). Per-primitive completeness is **paper-open**. See
  Plan E in `OPEN_QUESTIONS.md`.

---

## SI §1.4 — Ternary candidates (preliminary)

Page 8 of the Supplementary Information PDF (`Supplementary
Information.pdf`, §1.4) introduces two **ternary** operators T₁ and T₂
as candidates for a hypothetical *constant-free* Sheffer (i.e. one
that can recover its own distinguished constant from arbitrary input):

```
T₁(x, y, z) = e^(x − y) · ln(x) / ln(z)
T₂(x, y, z) = e^(x − y) · ln(z) / ln(x)
```

with the special property `T₂(x, x, x) = 1` — exactly the property
that the binary EML lacks (binary EML *cannot* generate its constant
from arbitrary input; SI §1.5 question #3, the *constant-free binary
Sheffer* open question).

**Status.** SI §1.4 explicitly notes T₁ and T₂ as **preliminary
unverified candidates** — a Rust exhaustive search up to operator
complexity K = 6 failed to find a constant-free *binary* Sheffer (SI
§1.5 question #3, the empirical evidence). T₁ and T₂ are the natural
ternary attempt to circumvent that obstruction.

**Status in this artefact.** Out of scope. They are not yet verified
in the paper, so formalising them would amount to formalising a
*conjecture* rather than a proven result. Earlier scaffolding in this
file imitated T₁ and T₂ as **binary** operators — that was a misnomer
(T₁ and T₂ are ternary in the paper) and has been removed.

---

## What the four "removed" terms were

For any future reader who runs `git log -p Sheffer.lean` and wonders
what was deleted: pre-cleanup, `Sheffer.lean` had four operators:

| Old name | Old definition | Match with paper |
|---|---|---|
| `EDLTerm` | `edl(x, y) = exp(x) / log(y)` | ✅ matches paper line 281 |
| `LDETerm` | `lde(x, y) = log(x) / exp(y)` | ❌ **division**, not paper's `−EML` (which is **subtraction**); operators differ |
| `T1Term` (binary) | `t1(x, y) = log(exp(x) + y)` | ❌ paper's T₁ is **ternary** (SI §1.4) |
| `T2Term` (binary) | `t2(x, y) = exp(log(x) − y)` | ❌ paper's T₂ is **ternary** (SI §1.4) |

The post-cleanup state is two operators (`EDLTerm` and `NegEMLTerm`)
that match the paper's actual §3.1 nomenclature exactly. The ternary
T₁ / T₂ are documented above as preliminary future work and not
formalised.

---

## See also

- [`Sheffer.lean`](../Sheffer.lean) — the actual scaffolding.
- `EML_review_bundle_sources/paper_source/EML.tex` lines 273–284 — the
  paper's §3.1 block.
- `EML_review_bundle_sources/Supplementary Information.pdf` page 8 —
  SI §1.4 (ternaries) and §1.5 (the seven open questions).
- [`OPEN_QUESTIONS.md`](../../../OPEN_QUESTIONS.md) — Plan D (EDL
  completeness, 1–2 wk), Plan E (−EML completeness, 1–2 wk).
