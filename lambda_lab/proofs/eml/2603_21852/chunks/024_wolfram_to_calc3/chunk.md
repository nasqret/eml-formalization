# Wolfram → Calc 3 reduction — 024_wolfram_to_calc3

**Paper section**: §3 Results, Table 2 (rows 'Wolfram' and 'Calc 3')
**Difficulty**: 4/5
**Status**: pending

## Source quote
> From the 7-symbol Wolfram set {π, e, i, ln, +, ×, ∧} we can drop π, e, i and the binary × and ∧, replacing them with {exp, ln, −x, 1/x, +} (Calc 3, 6 symbols).

## Informal (PL)
Pierwszy krok łańcucha redukcji: każda funkcja wyrażalna w zbiorze Wolfram (rzeczywisty podzbiór, bez `i`) jest wyrażalna w zbiorze Calc 3. Stwierdzenie istnieniowe: dla każdego `e : Wolfram` istnieje `e' : Calc3` taki, że ewaluacje rzeczywiste pokrywają się dla wszystkich `x y : ℝ`. Stała `π` musi zostać zakodowana operacjami z `Calc3` na `e` (Calc3 nie ma prymitywu `π`), a `pow a b` zwykle zapisuje się jako `exp(b · ln a)` z założeniem dodatniości podstawy. Z tych powodów chunk pozostaje `sorry`-ed.

## Informal (EN)
First step of the reduction chain: every function expressible in the Wolfram set (real-valued subset, no `i`) is expressible in Calc 3. We state it as: for every `e : Wolfram` there exists `e' : Calc3` whose real evaluation agrees with `e`'s for all `x y : ℝ`. The constant `π` must be encoded via Calc3 operations on `e` (Calc3 has no `π` primitive), and `pow a b` is generally written `exp(b · ln a)` under a positivity assumption on the base. For these reasons the chunk remains `sorry`-ed.

## Formal target

```lean
theorem wolfram_to_calc3 :
    ∀ e : Wolfram, ∃ e' : Calc3,
      ∀ x y : ℝ, Calc3.eval x y e' = Wolfram.eval x y e := by sorry
```

## Dependencies
(none — but builds on `EML/Calc.lean`)

## Aristotle status
pending (project_id: null) — not submitted; left as a permanent `sorry` stub due to the `π` and `pow` obstacles described above.
