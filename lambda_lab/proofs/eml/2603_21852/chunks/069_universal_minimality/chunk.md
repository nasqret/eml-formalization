# Universal minimality — 069_universal_minimality

**Paper section**: §3 Results, Table 2 closing remark (extension)
**Difficulty**: 5/5
**Status**: pending

## Source quote
> No calculator with strictly fewer than three primitives suffices for
> elementary expressiveness. (Open in the paper for the universal claim.)

## Informal (PL)
Wzmocnienie chunku 029: każda 2-prymitywna konfiguracja (jedna stała
nullarna + jedna funkcja unarna LUB binarna) nie wyraża identyczności
`ℝ → ℝ` jako funkcji jednej zmiennej. Indukcja po kształcie zamkniętego
termu pokazuje, że ewaluacja jest stała (nie zależy od `x`), więc
żadnego unwięzłego termu odwzorowującego `x ↦ x`.

## Informal (EN)
Strengthens chunk 029: every 2-primitive configuration (one nullary
constant + one unary OR one binary function) cannot express the
identity `ℝ → ℝ` as a function of one variable. Structural induction
on the closed-term shape shows the evaluation is constant
(independent of `x`), so no closed term realises `x ↦ x`.

## Formal target

```lean
theorem two_prim_cannot_represent_identity
    (c : ℝ) (op : ℝ → ℝ → ℝ) :
    ¬ ∃ t : TwoPrimCalc, ∀ x : ℝ, TwoPrimCalc.eval c op t = x := by sorry

theorem two_prim_unary_cannot_represent_identity
    (c : ℝ) (f : ℝ → ℝ) :
    ¬ ∃ t : TwoPrimCalcU, ∀ x : ℝ, TwoPrimCalcU.eval c f t = x := by sorry
```

## Dependencies
029_eml_minimality

## Aristotle status
pending (project_id: null)
