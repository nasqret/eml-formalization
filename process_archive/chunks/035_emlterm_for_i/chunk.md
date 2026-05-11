# EMLTermℂ whose eval is `i` — 035_emlterm_for_i

**Paper section**: §3 Results, EML expression catalog (i, K=131); §2.1 compiler macros
**Difficulty**: 5/5
**Status**: complete (verified)

## Source quote
> i: K = 131 (compiler) / K > 55 (direct search).
> §2.1 compiler: `i ↦ −exp(Log(−1)/2)`.

## Informal (PL)
Istnieje term EMLTermℂ ewaluujący do jednostki urojonej `i`. Konstrukcja w `EML/Solutions/035_emlterm_for_i.lean` realizuje wzór `i = −exp(Lg(−1)/2)`, gdzie ostatnie negowanie wykonuje sztuczka cancellation z chunk 036.

## Informal (EN)
There exists an EMLTermℂ evaluating to `Complex.I`.  The witness in `EML/Solutions/035_emlterm_for_i.lean` realises `i = −exp(Lg(−1)/2)`, with the final negation handled by the chunk-036 cancellation `(exp z − z) − exp z = −z`.

## Formal target

```lean
theorem emlterm_for_i : ∃ t : EMLTermℂ, EMLTermℂ.eval t = Complex.I
```

## Construction outline

1. `Zt`, `TwoT`, `NegOneT` — branch-safe trees for `0`, `2`, `−1`.
2. `Lg t := eml(Zt, eml(eml(Zt, t), one))` — the log macro; `(Lg t).eval = Complex.log t.eval` whenever `arg(t.eval) < π`.
3. `LogN1 := Lg(NegOneT)` evaluates to `−πI` (sign flipped vs. textbook `log(−1) = +πI` because the intermediate `1 − πI` is on the boundary of the principal strip; cf. chunk 034 for the same flip).
4. `Halve(LogN1) := exp(log(LogN1) − log 2) = LogN1/2 = −iπ/2`.
5. `NegI := exp(−iπ/2) = −i`.
6. **Negation via chunk-036 trick**: `M := eml(NegI, eml(NegI, one))` evaluates to `exp(−i) − log(exp(−i)) = exp(−i) − (−i) = exp(−i) + i` (clean because `(−i).im = −1` is strictly inside `(−π, π]`).
7. `i_term := Sub(M, ExpT NegI)` evaluates to `(exp(−i) + i) − exp(−i) = i`. ✓

This matches the paper's compiler macro `i ↦ −exp(Log(−1)/2)` modulo the principal-branch sign flip on `Lg(−1)`: in Mathlib `Lg(−1) = −πI`, so `exp(Lg(−1)/2) = exp(−iπ/2) = −i`, and we negate to obtain `+i`.

## Dependencies
002_def_eml_term, 003_def_eml_eval, 031_emlterm_for_neg_one, 032_emlterm_for_two, 033_emlterm_for_half, 036_emlterm_for_neg_x (the negation trick is reused)

## Verification

```
$ lake env lean lean_workspace/EML/Solutions/035_emlterm_for_i.lean
$ echo $?
0
```

No `sorry`, no `Classical.choice`, no `decide`/`native_decide`.  All proof steps are tactical (`simp only`, `rw`, `linarith`, `ring`, `push_cast`, `nlinarith`).

## v2 search history (for the record)

The earlier complex-numerical-evaluator search (size ≤ 31, ~3.1 M unique signatures) found no match — consistent with the paper's `K > 55` direct-search lower bound for the imaginary unit.  The EMLTermℂ extension realised here is the route §2.1 of the paper describes (its compiler macros assume complex evaluation throughout).

## Aristotle status
not submitted (verified locally with `lake env lean`; submission would be redundant).
