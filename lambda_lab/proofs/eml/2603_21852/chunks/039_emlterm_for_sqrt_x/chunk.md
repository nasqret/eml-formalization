# EMLTerm₁ realising the function √x — 039_emlterm_for_sqrt_x

**Paper section**: §3 Results, EML expression catalog (√x, K=139)
**Difficulty**: 5/5
**Status**: pending

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

## Aristotle status
pending (project_id: null)
