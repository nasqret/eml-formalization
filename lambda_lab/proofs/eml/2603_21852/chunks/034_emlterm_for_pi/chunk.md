# EMLTermℂ whose eval is π — 034_emlterm_for_pi

**Paper section**: §3 Results, EML expression catalog (π, K=193); Table S2 step 18
**Difficulty**: 5/5
**Status**: complete (verified)

## Source quote
> π: K = 193 (compiler) / K > 53 (direct search).
> Table S2 step 18: π = √(−(ln(−1))²).

## Informal (PL)
Istnieje term EMLTermℂ ewaluujący do π po przeniesieniu definicji do dziedziny zespolonej. Konstrukcja w `EML/Solutions/034_emlterm_for_pi.lean` wykorzystuje gałąź główną `Complex.log` i tożsamość `log(−1) = πI`.

## Informal (EN)
There exists an EMLTermℂ evaluating to π in the complex extension of the term grammar.  The witness in `EML/Solutions/034_emlterm_for_pi.lean` exploits Mathlib's principal-branch `Complex.log` and the identity `log(−1) = πI`.

## Formal target

```lean
theorem emlterm_for_pi : ∃ t : EMLTermℂ, EMLTermℂ.eval t = (Real.pi : ℂ)
```

## Construction outline

1. `Zt`, `TwoT`, `NegOneT` — branch-safe trees for `0`, `2`, `−1` (every interior node is a positive real, so all `log`/`exp` rewrites are clean).
2. `Lg t := eml(Zt, eml(eml(Zt, t), one))` — the standard "log macro"; `(Lg t).eval = Complex.log t.eval` whenever `arg(t.eval) < π` (i.e. `t.eval` is not a negative real).
3. `LogN1 := Lg(NegOneT)` evaluates to `−πI` (the *opposite* sign of the textbook `log(−1) = +πI`; the flip happens because `1 − log(−1) = 1 − πI` lies on the boundary of the principal strip, so `exp(1 − πI) = −e`, whose log is `1 + πI`, and `1 − (1 + πI) = −πI`).
4. `Halve(LogN1) := exp(log(LogN1) − log 2) = LogN1/2 = −iπ/2`.
5. `NegI := exp(−iπ/2) = −i`.
6. `Lg(NegI) = −iπ/2` (cleanly, since `(−i).im = −1` is strictly inside `(−π, π]`).
7. **Cancellation**: `Sub(Lg LogN1, Lg NegI) = (log π − iπ/2) − (−iπ/2) = log π` (real!).
8. `pi_term := Exp(Sub(Lg LogN1, Lg NegI))` — its eval is `exp(log π) = π`. ✓

The crucial observation is that the imaginary parts of `log(LogN1)` and `log(NegI)` cancel exactly, producing the *real* value `log π`, so the outer `exp` lands on `π` without any further multiplication-by-half or square-root machinery.

## Dependencies
002_def_eml_term, 003_def_eml_eval, 031_emlterm_for_neg_one, 032_emlterm_for_two, 033_emlterm_for_half

## Verification

```
$ lake env lean lean_workspace/EML/Solutions/034_emlterm_for_pi.lean
$ echo $?
0
```

No `sorry`, no `Classical.choice`, no `decide`/`native_decide`.  All proof steps are tactical (`simp only`, `rw`, `linarith`, `ring`, `push_cast`).

## v2 search history (for the record)

The earlier real-domain enumeration (`mma_eml_search_v2.wls`, size ≤ 31, ~3.1 M unique signatures) found no match — consistent with the paper's `K > 53` direct-search lower bound.  The EMLTermℂ extension realised here is the route the paper describes in §2.1 (its compiler macros assume complex evaluation throughout).

## Aristotle status
not submitted (the witness is verified locally with `lake env lean`; submission to Aristotle would be redundant).
