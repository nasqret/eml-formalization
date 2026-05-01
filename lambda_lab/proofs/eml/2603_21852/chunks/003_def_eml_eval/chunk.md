# Evaluation of EML terms — 003_def_eml_eval

**Paper section**: §4.1 EML compiler
**Difficulty**: 1/5
**Status**: pending

## Source quote
> Each EML term evaluates to a real number obtained by replacing every leaf 1 by the constant 1 and every internal node eml(t,u) by exp(eval t) − ln(eval u).

## Informal (PL)
Funkcja eval mapuje każdy term EML na wartość rzeczywistą: liść .one daje 1, a węzeł .eml t u daje exp(eval t) − ln(eval u). Z powodu Real.log junk-value dla niedodatnich argumentów funkcja jest totalna na ℝ, ale 'sensowne' wartości otrzymujemy tylko gdy poddrzewa eval-ują do liczb dodatnich.

## Informal (EN)
The eval function maps each EML term to a real number: a .one leaf gives 1, and a .eml t u node gives exp(eval t) − ln(eval u). Because Real.log is junk-valued at non-positive arguments the function is total on ℝ, but the 'meaningful' values arise only when the subtrees evaluate to positive reals.

## Formal target

```lean
def EMLTerm.eval : EMLTerm → ℝ
  | .one => 1
  | .eml t u => Real.exp (EMLTerm.eval t) - Real.log (EMLTerm.eval u)
```

## Dependencies
002_def_eml_term

## Aristotle status
pending (project_id: null)
