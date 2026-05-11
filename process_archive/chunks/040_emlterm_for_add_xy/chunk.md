# EMLTerm₂ realising x + y — 040_emlterm_for_add_xy

**Paper section**: §3 Results, EML expression catalog (x + y, K=27)
**Difficulty**: 5/5
**Status**: pending

## Source quote
> x + y: K = 27 (compiler) / K = 19 (direct search).

## Informal (PL)
Istnieje 2-zmienny term EML rozmiaru 27, który dla każdej pary (x,y) ewaluuje do x + y. Wymagana 2-zmienna gramatyka EMLTerm₂ (z liśćmi .varX, .varY) i nowa funkcja ewaluacji eval₂ : ℝ → ℝ → EMLTerm₂ → ℝ.

## Informal (EN)
There exists a two-variable EML term of size 27 whose evaluation at (x,y) equals x + y. Requires a 2-variable grammar EMLTerm₂ (with .varX, .varY leaves) and an evaluation eval₂ : ℝ → ℝ → EMLTerm₂ → ℝ.

## Formal target

```lean
theorem emlterm2_for_add : ∃ t : EMLTerm₂, ∀ x y : ℝ, EMLTerm₂.eval x y t = x + y := by sorry
```

## Dependencies
014_add_via_eml

## Aristotle status
pending (project_id: null)
