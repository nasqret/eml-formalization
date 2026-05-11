# Verification evidence (2026-05-11, pre-announcement seal)

This file captures fresh re-verification evidence for the public claims
made in [`README.md`](../../../../README.md),
[`DASHBOARD.md`](../../../../DASHBOARD.md),
[`AUTHOR_SUMMARY.md`](AUTHOR_SUMMARY.md), and the GPT-Pro review packet.

The evidence below was produced on **2026-05-11** after the
GPT-Pro pre-announcement review (verdict: SHIP-WITH-FIXES). It addresses
Pro's punch-list item #9 ("ship a transcript that shows the build is
green and the headline theorems are axiom-clean").

## 1. Full library build — `lake build EML`

```
✔ [8056/8062] Built EML.Framework.Sheffer (31s)
✔ [8057/8062] Built EML.Framework.TransplantDepths (31s)
✔ [8058/8062] Built EML.Framework.EDLClosedVal (35s)
✔ [8059/8062] Built EML.Framework.PolynomialBinary (154s)
✔ [8060/8062] Built EML.Framework.AlternativeWitnesses (154s)
✔ [8061/8062] Built EML (125s)
Build completed successfully (8062 jobs).
```

All 8 062 jobs build clean. The output above is the verbatim tail of
`lake build EML` from a local re-run; warnings are confined to
`linter.unusedSimpArgs` and `linter.unusedVariables` (cosmetic, no
correctness implications).

To reproduce locally:

```bash
cd lambda_lab/proofs/eml/2603_21852/lean_workspace
lake build EML
```

## 2. Axiom audit — `#print axioms` on every headline theorem

The audit script lives at
[`lean_workspace/EML/AxiomCheck.lean`](lean_workspace/EML/AxiomCheck.lean)
and runs `#print axioms` on every headline theorem the project advertises.
Verbatim output of `lake env lean EML/AxiomCheck.lean` on 2026-05-11:

```
'EML.paper_claim_sin_full'               depends on axioms: [propext, Classical.choice, Quot.sound]
'EML.paper_claim_arctan_full'            depends on axioms: [propext, Classical.choice, Quot.sound]
'EML.paper_claim_tan_full'               depends on axioms: [propext, Classical.choice, Quot.sound]
'EML.paper_claim_cos'                    depends on axioms: [propext, Classical.choice, Quot.sound]
'EML.paper_claim_sin'                    depends on axioms: [propext, Classical.choice, Quot.sound]
'EML.paper_claim_arccos_open'            depends on axioms: [propext, Classical.choice, Quot.sound]
'EML.paper_claim_arcsin_open'            depends on axioms: [propext, Classical.choice, Quot.sound]
'EML.paper_claim_sqrt_pos'               depends on axioms: [propext, Classical.choice, Quot.sound]
'EML.EMLTerm.paper_claim_sqrt_full'      depends on axioms: [propext, Classical.choice, Quot.sound]
'EML.EMLTerm.paper_claim_arcosh_full'    depends on axioms: [propext, Classical.choice, Quot.sound]
'EML.EMLTerm.paper_claim_hypot_full'     depends on axioms: [propext, Classical.choice, Quot.sound]
'EML.EMLTerm.identity_terms_at_depth_multiples_of_four'
                                         depends on axioms: [propext, Classical.choice, Quot.sound]
'no_polynomial_binary_generates_exp'     depends on axioms: [propext, Classical.choice, Quot.sound]
'polynomial_binary_terms_are_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
'EML.edl_closed_eval_in_closedVal'       depends on axioms: [propext, Classical.choice, Quot.sound]
'EML.EMLTerm.paper_claim_mul_compact'    depends on axioms: [propext, Classical.choice, Quot.sound]
'EML.EMLTerm.K_count_logb_compact'       does not depend on any axioms
'EML.edl_paper_claim_log'                depends on axioms: [propext, Classical.choice, Quot.sound]
'EML.negEml_paper_claim_minusInf'        depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Reading.** Every headline theorem depends only on Mathlib's three
core axioms: `propext`, `Classical.choice`, `Quot.sound`. No `sorry`,
no `admit`, no project-local axiom. The `K_count_*_compact` theorem
goes further — it is pure `rfl`-decidable, so it depends on **no axioms
at all**.

**What this rules out.**

* No `sorry` hides inside the chains (axiom set is the closed
  Mathlib-standard one).
* No project-side `axiom <X>` was introduced (the printed lists are
  identical across theorems, modulo `K_count`).
* The `EDLTranscendenceBarrier` typeclass — the one place where the
  artefact *consciously* uses an unproved hypothesis — does NOT appear
  as an axiom of `edl_closed_eval_in_closedVal` because that theorem
  is the unconditional closure result. The conditional obstruction
  corollaries (`no_closed_edl_neg_one`, `no_closed_edl_two`,
  `no_closed_edl_half`) take `EDLTranscendenceBarrier` as a typeclass
  parameter and would print it in their axiom set if asked. By design
  no instance is provided, so any user invoking them is signing for
  the hypothesis explicitly.

## 3. Repository hygiene — `grep -r 'sorry\|admit' lean_workspace/EML`

```bash
$ grep -rn '\bsorry\b\|\badmit\b' lean_workspace/EML/ --include='*.lean'
(no output)
```

No `sorry` or `admit` anywhere in the EML source tree. The
[`scripts/check_no_sorries.sh`](../../../../scripts/check_no_sorries.sh)
hook (run in CI) enforces this on every commit.

## 4. PCSS Eagle HPC re-verify

Most recent run: job 7 041 555 (2026-05-07), 88 files, 0 fail, 42 s wall.

The PCSS Eagle re-verify is **on a different machine** and **with a
different Lean toolchain installation** than the local builds. It is
the strongest form of "reproducible elsewhere" evidence the artefact
has. The submission scripts are at
[`eagle_scripts/`](../../../../eagle_scripts/); see
[`eagle_scripts/INODE_QUOTA_REQUEST.md`](../../../../eagle_scripts/INODE_QUOTA_REQUEST.md)
for the current quota status.

## How to regenerate this evidence

```bash
cd lambda_lab/proofs/eml/2603_21852/lean_workspace

# (1) Full build
lake build EML 2>&1 | tail -10

# (2) Axiom audit
lake env lean EML/AxiomCheck.lean

# (3) Sorry check
grep -rn '\bsorry\b\|\badmit\b' EML/ --include='*.lean' | grep -v '^Binary'
```

A green build, the axiom list above, and an empty sorry-check are the
three signals that the artefact is sealed.
