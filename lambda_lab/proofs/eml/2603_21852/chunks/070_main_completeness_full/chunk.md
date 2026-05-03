# Main completeness — full umbrella (Round 2) — 070_main_completeness_full

**Paper section**: §3 Results, abstract claim of universality (Round 2 update)
**Difficulty**: 5/5
**Status**: complete (20-conjunct delivered)

## Source quote
> EML + 1 generates all standard scientific calculator operations.

## Informal (PL)
Aktualizacja chunku 045: parasolowy egzystencjał obejmujący wszystkie *czyste*
konstruktywne pod-świadki dostępne na chwilę dostarczenia. Plik samodzielny.

## Informal (EN)
Updates chunk 045: umbrella existential covering all *clean* constructive
sub-witnesses available at delivery time. Self-contained file.

## Formal target — delivered (20 conjuncts)

- 5 Round-1 constants (0, −1, 2, 1/2, e) — chunks 030, 031, 032, 033, 022
- 3 Round-1 unary (−x, 1/x on positives, x² on positives) — chunks 036, 037, 038
- 3 Round-1 binary (x+y, x·y on positives, x^y on positives) — chunks 040, 041, 042
- 3 Round-2 R-functions on positives (x/y, avg(x,y), x/2) — chunks 050, 051, 052
- 1 Round-2 sigmoid σ — chunk 055
- 3 Round-2 hyperbolic (cosh, sinh, tanh) — chunks 056, 057, 058
- 1 Round-2 inverse hyperbolic (arcosh on √2 < x) — chunk 060
- 1 universal-minimality corollary — chunk 069

```lean
theorem main_completeness_full :
    (...20-conjunct existential...) := ⟨..., ..., ...⟩
```

## Excluded (with reason)

- 034 (π), 035 (i), 039 (√x): require paper Supplementary trees → permanent sorries.
- 053 (log_x y): upstream uses `simp +decide` and a non-portable `mkDiv`.
- 054 (hypot), 059 (arsinh): rely transitively on 039.
- 061 (artanh), 062–064 (cos/sin/tan), 065/067 (arctan/arccos):
  partial / submitted upstream or rely on a complex grammar.
- 066 (arcsin): the upstream file shows the original statement is **false**
  in the restricted `EMLTermℂ₁` grammar.
- 068 (Wolfram → Calc 3 complex): off-topic; different inductive grammar.

## Dependencies
022, 030, 031, 032, 033, 036, 037, 038, 040, 041, 042,
050, 051, 052, 055, 056, 057, 058, 060, 069

## Aristotle status
complete (verified locally by `lake env lean`, exit 0).
