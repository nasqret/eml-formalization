# Main completeness — full umbrella (Round 2) — 070_main_completeness_full

**Paper section**: §3 Results, abstract claim of universality (Round 2 update)
**Difficulty**: 5/5
**Status**: pending

## Source quote
> EML + 1 generates all standard scientific calculator operations.

## Informal (PL)
Aktualizacja chunku 045: parasolowy egzystencjał obejmuje wszystkie 30+
konstruktywnych pod-świadków, w tym 21 nowych z rundy 2 (chunki 050-067).
Każdy spójnik to istnienie termu EML (jednej z czterech gramatyk) ewaluującego
do oczekiwanej funkcji. Plik samodzielny.

## Informal (EN)
Updates chunk 045: umbrella existential covering all 30+ constructive
sub-witnesses, including the 21 added in Round 2 (chunks 050-067). Each
conjunct asserts existence of an EML term (in one of four grammars)
evaluating to the target function. Self-contained file.

## Formal target

A 29-conjunct existential covering:
- 5 Round-1 constants (0, −1, 2, 1/2, e)
- 3 Round-1 unary (−x, 1/x, x²)
- 3 Round-1 binary (x+y, x·y, x^y)
- 6 Round-2 Group A (x/y, avg, half, log_x y, hypot, σ)
- 3 Round-2 Group B (cosh, sinh, tanh)
- 3 Round-2 Group C (arsinh, arcosh, artanh)
- 3 Round-2 Group D (cos, sin, tan)
- 3 Round-2 Group E (arctan, arcsin, arccos)

```lean
theorem main_completeness_full : <29-conjunct existential> := by sorry
```

## Dependencies
022, 030, 031, 032, 033, 036, 037, 038, 040, 041, 042,
050, 051, 052, 053, 054, 055, 056, 057, 058, 059, 060, 061,
062, 063, 064, 065, 066, 067

## Aristotle status
pending (project_id: null)
