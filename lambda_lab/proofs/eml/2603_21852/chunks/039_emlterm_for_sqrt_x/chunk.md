# EMLTerm₁ realising the function √x — 039_emlterm_for_sqrt_x

**Paper section**: §3 Results, EML expression catalog (√x, K=139)
**Difficulty**: 5/5
**Status**: pending (search exhausted, no witness)

## Source quote
> √x: K = 139 (compiler) / K > 43 (direct search).

## Informal (PL)
Istnieje parametryzowany term EML rozmiaru 139 ewaluujący do √x dla x ≥ 0. PROBABLE PERMANENT SORRY: drzewo o 139 węzłach poza budżetem ręcznej transkrypcji.

## Informal (EN)
There exists a parameterised EML term of size 139 whose evaluation equals √x for x ≥ 0. PROBABLE PERMANENT SORRY: 139-node literal tree beyond the manual-transcription budget.

## Formal target

```lean
theorem emlterm1_for_sqrt_x : ∃ t : EMLTerm₁, ∀ x : ℝ, 0 ≤ x → EMLTerm₁.eval x t = Real.sqrt x := by sorry
```

## Dependencies
023_emlterm_exp_x_witness

## v2 search

**Tool**: `lambda_lab/proofs/eml/tools/mma_eml_search_v2.wls`
**Spec**: `lambda_lab/proofs/eml/tools/spec_039.json`
**Result JSON**: `search_v2_result.json` in this directory.

| Param            | Value         |
| ---------------- | ------------- |
| max_size         | 15            |
| sample points    | 6 (real)      |
| trees generated  | 39,996        |
| unique signatures (after numerical dedup) | 26,722 |
| numeric matches  | 0             |
| symbolic checks  | 0             |
| wall clock       | ~2 s          |

**Outcome**: no match. 1-variable EML trees enumerated up to size 15 with
a 6-point numerical signature dedup; not one signature matched `Sqrt[x]`
within 1e-6 tolerance at any sample point. Paper's `K > 43` direct-search
lower bound makes this expected.

**Next steps**:
1. Transcribe the 139-node Supplementary tree, then verify numerically
   with this harness.
2. Alternatively, lift `√x = exp(½ · log x)` over the constructed `x²`
   witness from chunk 038 — half is a known witness (chunk 033) and we
   already build `log` and `exp` at the term level.
3. Otherwise leave as a permanent sorry.

## Aristotle status
not submitted (witness unavailable below the paper's lower bound).
