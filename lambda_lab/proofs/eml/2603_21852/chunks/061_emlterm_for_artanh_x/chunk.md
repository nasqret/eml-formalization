# EMLTerm₁ realising artanh(x) — 061_emlterm_for_artanh_x

**Paper section**: §Sup. Table S2 step 30 (`artanh(x)`, K=5)
**Difficulty**: 4/5
**Status**: pending

## Source quote
> 30  artanh(x)    K=5    arsinh(1/tan(arccos(x)))

## Informal (PL)
Funkcja odwrotna do tanh, dziedzina `|x| < 1`. Standardowa forma:
`artanh x = (1/2) ln((1+x)/(1-x))`. Świadek korzysta z chunków 040 (`+`),
050 (`/`), 011 (`ln`) i 052 (`half`). Paperowa recepta przez `arsinh ∘
tan⁻¹ ∘ arccos` jest równoważna, ale zawiera kompozycję trygonometryczną
ω complex; tu pozostajemy w ℝ.

## Informal (EN)
Inverse of tanh, domain `|x| < 1`. Standard form: `artanh x = (1/2) ln
((1+x)/(1-x))`. Witness uses chunks 040 (`+`), 050 (`/`), 011 (`ln`),
and 052 (`half`). Paper's recipe via `arsinh ∘ 1/tan ∘ arccos` is
equivalent but routes through complex trig; we stay in ℝ.

## Formal target

```lean
theorem emlterm1_for_artanh :
    ∃ t : EMLTerm₁, ∀ x : ℝ, -1 < x → x < 1 →
      EMLTerm₁.eval x t = Real.artanh x := by sorry
```

## Dependencies
011_ln_via_eml, 040_emlterm_for_add_xy, 050_emlterm_for_div_xy, 052_emlterm_for_half_x

## Aristotle status
pending (project_id: null)
