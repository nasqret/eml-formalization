# EML term with x-leaf whose eval is exp(x) — 023_emlterm_exp_x_witness

**Paper section**: §3 Results, EML expression catalog (exp(x), K=3)
**Difficulty**: 3/5
**Status**: pending

## Source quote
> exp(x): eml(x, 1) — K = 3.

## Informal (PL)
Aby zapisać exp(x) jako term EML, rozszerzamy gramatykę o liść .var reprezentujący zmienną x; ewaluacja w punkcie x daje EMLTerm₁.eval x (.eml .var .one) = exp(x). Wprowadzamy oddzielny typ EMLTerm₁ aby nie zaburzać oryginalnego (stałe-tylko) EMLTerm.

## Informal (EN)
To realise exp(x) as an EML term we add a .var leaf representing the variable x; the evaluation at x gives EMLTerm₁.eval x (.eml .var .one) = exp(x). We introduce a separate type EMLTerm₁ to avoid disturbing the original (constants-only) EMLTerm.

## Formal target

```lean
theorem emlterm1_exp_x_witness (x : ℝ) : EMLTerm₁.eval x (.eml .var .one) = Real.exp x := by sorry
```

## Dependencies
002_def_eml_term

## Aristotle status
pending (project_id: null)
