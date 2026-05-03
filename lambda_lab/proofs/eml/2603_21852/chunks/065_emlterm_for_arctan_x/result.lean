import Mathlib

/-!
# Chunk 065 — EMLTermℂ₁ witness for `arctan(x)` (PARTIAL)

## Status

Partial: a concrete construction is given in the docstring below; the full
Lean formalisation is deferred from this push.

## Updated analysis (supersedes previous reasoning)

The earlier theorem-state used `sorry` with no construction. We now know
(from chunks 062, 063 sealed in this push) that the EMLTermℂ₁ grammar
DOES admit periodic / inverse-trig functions of a real input, via Euler's
identity.  For arctan, restrict to `x > 0` and use:

  `arctan(x) = Im(Complex.log (1 + i·x)) = Re(-i · log(1 + i·x))`.

Construction:

1. From chunk 062's sealed construction we obtain `mid_term : EMLTermℂ₁`
   with `(mid_term.eval (x:ℂ)) = (x:ℂ) * I` for `x > 0`.
2. `one_plus_ix := mkADD .one mid_term` evaluates to `1 + i·x`.
   For `x > 0`, `arg(1+ix) = arctan x ∈ (0, π/2) < π`, so `mkLOG`
   applies cleanly.
3. `log_one_plus_ix := mkLOG one_plus_ix` evaluates to
   `log(1+ix) = (1/2)·log(1+x²) + i·arctan(x)`.
   Real part `(1/2)·log(1+x²) > 0`, so `arg(log(1+ix)) ∈ (0, π/2) < π`.
4. `log_log := mkLOG log_one_plus_ix`.
5. `arctan_term := mkEXP (mkSUB log_log (mkLOG iTerm))`.
   Eval = `exp(log(log(1+ix)) − I·π/2) = log(1+ix) · exp(−Iπ/2)
        = log(1+ix) · (−I)`.
   Re of that = `Im(log(1+ix)) = arctan x`. ✓

The mkADD / mkLOG / mkSUB combinator scaffolding is the same `ADDsafe`
pattern as in chunks 062, 063.  Around 800 lines of mechanical Lean.

## Spec tightening proposed

Restrict to `0 < x` (and possibly `x ≠ √(e²−1)` to avoid `log(1+ix) = 1`).
For `x = 0`, `arctan 0 = 0`, witnessed trivially by the closed
`zero_term`.  For `x < 0` use `arctan(−x) = −arctan(x)`.
-/

namespace EML

inductive EMLTermℂ₁ : Type
  | one : EMLTermℂ₁
  | var : EMLTermℂ₁
  | eml : EMLTermℂ₁ → EMLTermℂ₁ → EMLTermℂ₁
  deriving Repr

noncomputable def EMLTermℂ₁.eval (z : ℂ) : EMLTermℂ₁ → ℂ
  | .one      => 1
  | .var      => z
  | .eml t u  => Complex.exp (eval z t) - Complex.log (eval z u)

theorem emlterm1c_for_arctan :
    ∃ t : EMLTermℂ₁, ∀ x : ℝ,
      (EMLTermℂ₁.eval (x : ℂ) t).re = Real.arctan x := by
  sorry

end EML
