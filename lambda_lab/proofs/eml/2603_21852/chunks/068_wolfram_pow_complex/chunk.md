# Wolfram → Calc 3 (complex, full pow) — 068_wolfram_pow_complex

**Paper section**: §3 Results, Table 2 (Wolfram, Calc 3) + §1 Sup. (complex extension)
**Difficulty**: 5/5
**Status**: pending

## Source quote
> From the 7-symbol Wolfram set {π, e, i, ln, +, ×, ∧} we can drop π, e, i
> and replace ×, ∧ by {exp, ln, −x, 1/x, +} (Calc 3, 6 symbols).
> [Sup. §1.4: complex extension extends to the full `pow` and `i`.]

## Informal (PL)
Rozszerzenie zakresu: redukcja Wolfram → Calc 3 z PEŁNYM konstruktorem
`pow` w domenie zespolonej. Generalizuje chunk 024 (który ograniczał się
do nieujemnej podstawy w ℝ). Definiuje `Calc3ℂ` nad ℂ; przypadek `pow`
korzysta z tożsamości `a^b = exp(b · log a)` na głównej gałęzi
(`a ≠ 0`). Dodatkowo dopuszcza stałą `i`.

## Informal (EN)
Scope extension: Wolfram → Calc 3 reduction with the FULL `pow`
constructor over the complex domain. Generalises chunk 024 (which was
restricted to non-negative real bases). Defines `Calc3ℂ` over ℂ; the
`pow` case uses the identity `a^b = exp(b · log a)` on the principal
branch (`a ≠ 0`). Additionally permits the constant `i`.

## Formal target

```lean
theorem wolframℂ_to_calc3ℂ (e : Wolframℂ) :
    ∀ z : ℂ, z ≠ 0 → ∃ e' : Calc3ℂ, Calc3ℂ.eval z e' = Wolframℂ.eval z e := by sorry
```

## Dependencies
022_emlterm_e_witness, 024_wolfram_to_calc3, 034_emlterm_for_pi, 035_emlterm_for_i

## Aristotle status
pending (project_id: null)
