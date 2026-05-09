# `x / √(1 + x²) ∈ (-1, 1)` — 077_atan_arg_in_ioo

**Paper section**: Path C′ Plan (post-paper, GPT Pro recommendation)
**Difficulty**: 2/5
**Status**: pending

## Source

GPT Pro consult `gpt_pro_bundle/trig_widening/RESPONSE.md` §3 — the
proof plan for `arctanViaArcsinℂ` requires showing that the
substitution argument `x / √(1+x²)` always lies in `arcsin`'s natural
domain `(-1, 1)`. This is the pure Mathlib lemma.

## Informal (EN)

For all `x : ℝ`, `x / √(1 + x²) ∈ (-1, 1)`. Standard real-analysis
fact: `|x| < √(1 + x²)` because `x² < 1 + x²`.

## Formal target

```lean
theorem atanArg_in_Ioo (x : ℝ) :
    x / Real.sqrt (1 + x^2) ∈ Set.Ioo (-1 : ℝ) 1
```

## Dependencies

None (Mathlib only).

## Aristotle status

pending (project_id: null)
