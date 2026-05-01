# Definition of the EML operator — 001_def_eml

**Paper section**: §3 Results, Equation 3
**Difficulty**: 1/5
**Status**: pending

## Source quote
> eml(x, y) = exp(x) − ln(y)

## Informal (PL)
Operator EML jest binarnym operatorem rzeczywistym zdefiniowanym wzorem eml(x,y) = exp(x) − ln(y). Stanowi serce konstrukcji Odrzywołka: w połączeniu ze stałą 1 generuje wszystkie elementarne funkcje kalkulatora naukowego.

## Informal (EN)
The EML operator is a binary real-valued operator defined by eml(x,y) = exp(x) − ln(y). It is the heart of Odrzywołek's construction: combined with the constant 1 it generates every elementary function of a scientific calculator.

## Formal target

```lean
def eml (x y : ℝ) : ℝ := Real.exp x - Real.log y
```

## Dependencies
(none)

## Aristotle status
pending (project_id: null)
