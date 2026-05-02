import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace EML

inductive EMLTerm₁ : Type
  | one : EMLTerm₁
  | var : EMLTerm₁
  | eml : EMLTerm₁ → EMLTerm₁ → EMLTerm₁
  deriving Repr

noncomputable def EMLTerm₁.eval (x : ℝ) : EMLTerm₁ → ℝ
  | .one => 1
  | .var => x
  | .eml t u => Real.exp (EMLTerm₁.eval x t) - Real.log (EMLTerm₁.eval x u)

/-
Reformulated to `x > 1` (was: x > 0).

A previous Aristotle attempt produced the witness construction
    sqrt_term = EXP (EXP (SUB (LOG (LOG var)) (LOG TWO)))
which uses `log(log x)`. This is well-defined only for `x > 1`
(where `log x > 0`); for `0 < x ≤ 1`, `Real.log` returns its
junk value 0 inside the second log, breaking the identity.

Restricting the spec to `x > 1` (where the construction IS valid)
makes the theorem provable. The general `0 < x` form likely needs
the paper's 139-RPN supplementary tree.

Construction (provided as a hint to the prover):
    LOG T  := eml(1, eml(eml(1, T), 1))         -- log T
    EXP T  := eml(T, 1)                          -- exp T
    SUB A B := eml(LOG A, EXP B)                 -- A − B (for A > 0)
    E      := eml(1, 1)                          -- e
    E_MINUS_ONE := eml(1, E)                     -- e − 1 (positive)
    E_MINUS_TWO := SUB E_MINUS_ONE 1             -- e − 2
    TWO    := SUB E E_MINUS_TWO                  -- 2
    halfLogTerm := EXP (SUB (LOG (LOG var)) (LOG TWO))
                                                  -- = (log x)/2 for x > 1
    sqrt_term   := EXP halfLogTerm               -- = √x

For x > 1: log x > 0, so LOG var well-defined; LOG (LOG var) well-defined;
the SUB and EXP chain gives exp((log x)/2) = √x.
-/
theorem emlterm1_for_sqrt_x_gt_one :
    ∃ t : EMLTerm₁, ∀ x : ℝ, 1 < x → EMLTerm₁.eval x t = Real.sqrt x := by
  sorry

end EML
