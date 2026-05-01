# Master-formula parameter count at level n — 043_master_formula_param_count

**Paper section**: §4.3 Master formula — symbolic regression
**Difficulty**: 2/5
**Status**: pending

## Source quote
> Level-n EML master formula has 5 × 2^n − 6 parameters total.

## Informal (PL)
Liczba parametrów master-formuły poziomu n wynosi 5·2^n − 6. Definicja parametrCount n := 5·2^n − 6 i lemat sprawdzający kilka małych wartości (n=1: 4, n=2: 14, n=3: 34).

## Informal (EN)
The level-n master formula has 5·2^n − 6 parameters. We define parametrCount n := 5·2^n − 6 and check small values (n=1: 4, n=2: 14, n=3: 34).

## Formal target

```lean
def masterParamCount (n : ℕ) : ℤ := 5 * 2 ^ n - 6
```

## Dependencies
(none)

## Aristotle status
pending (project_id: null)
