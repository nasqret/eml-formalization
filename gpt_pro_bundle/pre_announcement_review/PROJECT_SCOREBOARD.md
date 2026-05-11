# Project scoreboard — verification targets

Commit on `main`: `66a93ac` (2026-05-11).

## Headline numbers

| | |
|---|---:|
| Paper primitives sealed | **36 / 36** (100%) |
| Public theorems exposed | **100** (61 original + 39 frontier) |
| &nbsp;&nbsp;• `paper_claim_*` (EML) | 48 in `PaperClaims.lean` |
| &nbsp;&nbsp;• Sheffer cousin claims | 13 (8 EDL + 5 −EML) in `Sheffer.lean` |
| &nbsp;&nbsp;• SI §1.5 #5 (transplant depths) | 9 in `TransplantDepths.lean` |
| &nbsp;&nbsp;• §G boundary in EReal | 3 in `StructuralLimitsEReal.lean` |
| &nbsp;&nbsp;• §G full fix (witness family) | 3 in `GFullFix.lean` |
| &nbsp;&nbsp;• Plan D structural ceiling | 4 in `EDLClosedVal.lean` (+ `EDLTranscendenceBarrier` typeclass) |
| &nbsp;&nbsp;• Polynomial-binary impossibility | 2 in `PolynomialBinary.lean` (paper §5) |
| &nbsp;&nbsp;• Compact alternative witnesses | 9 + 9 K-counts in `CompactWitnesses.lean` |
| `K_count_*` `rfl`-checked tree sizes | **44** total |
| Lean kernel jobs in `lake build EML` | **8 062** |
| `sorry` / `admit` occurrences | **0** |
| §G structural boundary points | **3 / 3 sealed** (was "documented" before today) |
| Witness-tree size — smallest | **K = 1** |
| Witness-tree size — largest | **K = 9 929 087** (`logb`, compiler-produced) |

## Verification commands

```bash
# Verify build cleanliness
cd lambda_lab/proofs/eml/2603_21852/lean_workspace
lake build EML
# Expected: Build completed successfully (8062 jobs).

# Verify zero sorry/admit at tactic positions
grep -nE '^[ \t]*(sorry|admit)\b|:=[ \t]*by[ \t]+sorry|:=[ \t]*by[ \t]+admit' \
    EML/Framework/PaperClaims.lean EML/Framework/Sheffer.lean \
    EML/Framework/TransplantDepths.lean EML/Framework/StructuralLimitsEReal.lean \
    EML/Framework/EDLClosedVal.lean EML/Framework/PolynomialBinary.lean \
    EML/Framework/CompactWitnesses.lean EML/Framework/GFullFix.lean
# Expected: empty (exit code 1)
```

## File structure of the frontier modules

```
EML/Framework/
├── TransplantDepths.lean    498 lines — SI §1.5 #5
├── StructuralLimitsEReal.lean  155 lines — §G in EReal templates
├── GFullFix.lean             83 lines — §G full-domain witnesses
├── EDLClosedVal.lean        133 lines — Plan D closure scaffold
├── PolynomialBinary.lean    155 lines — paper §5 first cut
├── CompactWitnesses.lean    176 lines — alternative direct-macro witnesses
```

Each is independently importable; the project root `EML.lean` imports all of them.

## Repository links

- **GitHub:** <https://github.com/nasqret/eml-formalization>
- **Commit being reviewed:** `66a93ac`
- **Source paper:** A. Odrzywołek, *All elementary functions from a single binary operator*, arXiv:2603.21852
- **Mathlib version:** v4.28.0
- **Lean toolchain:** v4.28.0
- **Licence:** MIT

## Prior Pro consults

1. **2026-05-08 — `gpt_pro_bundle/trig_widening/`** — Pro recommended Path C′ (range-reduction by substitution). Sealed via `paper_claim_{sin_full, arctan_full, tan_full}` (PRs #4, #5 on the original branch).

2. **2026-05-10 — `gpt_pro_bundle/frontier_questions/`** — Pro ranked four research-grade directions:
   - #1 SI §1.5 #5: tractable now → `TransplantDepths.lean`
   - #2 §G boundary points via narrow EReal templates: tractable narrowly scoped → `StructuralLimitsEReal.lean` (+ `GFullFix.lean` as a follow-on)
   - #3 Plan D ceiling via `EDLClosedVal`: tractable conditional on named hypothesis → `EDLClosedVal.lean`
   - #4 Polynomial-binary impossibility (paper §5): tractable, ~150 lines → `PolynomialBinary.lean`

All four delivered.

## Quick checklist of things Pro should confirm

- [ ] `lake build EML` returns 8062 jobs, sorry-free.
- [ ] Each public theorem listed in `CODE_EXCERPTS.md` `#check`s cleanly.
- [ ] Witness-family `paper_claim_*_full` theorems honestly state the quantifier-flipped form (∀ env, ∃ t) rather than over-claim the original form (∃ t, ∀ env).
- [ ] `EDLTranscendenceBarrier` typeclass is honestly advertised as having no instance.
- [ ] `NoIdentityAtDepthThree` and `OnlyMultiplesOfFourHaveIdentities` `def`s are honestly advertised as "statement only, full proof remains open".
- [ ] `CompactWitnesses.lean` honestly says the K-counts are identical to the structural-compile output.
- [ ] Polynomial-binary impossibility statement matches what the paper §5 universal-minimality question is asking (for the polynomial class).
