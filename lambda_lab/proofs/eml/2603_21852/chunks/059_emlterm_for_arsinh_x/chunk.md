# EMLTerm₁ realising arsinh(x) — 059_emlterm_for_arsinh_x

**Paper section**: §Sup. Table S2 step 27 (`arsinh(x)`, K=6)
**Difficulty**: 4/5
**Status**: pending

## Source quote
> 27  arsinh(x)    K=6    ln(x + hypot(-1, x))

## Informal (PL)
Funkcja odwrotna do sinh: `arsinh x = ln(x + √(x² + 1))`. Świadek
korzysta z chunków 040 (`+`), 054 (hypot z `y=1`) i 011 (`ln`). Pełna
identyczność jest globalna (`x ∈ ℝ`); świadek formalny ma chwilowo
ograniczenie `x > 0` z powodu chunku 054.

## Informal (EN)
Inverse of sinh: `arsinh x = ln(x + √(x² + 1))`. Witness uses chunks 040
(`+`), 054 (hypot at `y=1`) and 011 (`ln`). The mathematical identity is
global (`x ∈ ℝ`); the formal witness is currently restricted to `x > 0`
due to chunk 054's positivity hypothesis.

## Formal target

```lean
theorem emlterm1_for_arsinh :
    ∃ t : EMLTerm₁, ∀ x : ℝ, 0 < x → EMLTerm₁.eval x t = Real.arsinh x := by sorry
```

## Dependencies
011_ln_via_eml, 040_emlterm_for_add_xy, 054_emlterm_for_hypot_xy

## Aristotle status
pending (project_id: null)
