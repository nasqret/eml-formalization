import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib

namespace EML

/-- `Calc0` is the term language for elementary calculator expressions
built from two variables `x`, `y`, the exponential function, and the
natural logarithm. -/
inductive Calc0 : Type
  | varX : Calc0
  | varY : Calc0
  | exp_ : Calc0 → Calc0
  | ln_  : Calc0 → Calc0

/-- Evaluate a `Calc0` term at real values `x` and `y`. -/
noncomputable def Calc0.eval (x y : ℝ) : Calc0 → ℝ
  | .varX   => x
  | .varY   => y
  | .exp_ a => Real.exp (Calc0.eval x y a)
  | .ln_  a => Real.log (Calc0.eval x y a)

/-- `EMLTerm₂` is the term language for the EML calculus with two
variables.  The only non-trivial combinator is `eml`, which computes
`exp(a) − log(b)`. -/
inductive EMLTerm₂ : Type
  | varX : EMLTerm₂
  | varY : EMLTerm₂
  | one  : EMLTerm₂
  | eml  : EMLTerm₂ → EMLTerm₂ → EMLTerm₂

/-- Evaluate an `EMLTerm₂` at real values `x` and `y`. -/
noncomputable def EMLTerm₂.eval (x y : ℝ) : EMLTerm₂ → ℝ
  | .varX    => x
  | .varY    => y
  | .one     => 1
  | .eml a b => Real.exp (EMLTerm₂.eval x y a) - Real.log (EMLTerm₂.eval x y b)

/-
**Calc 0 → EML** (Table 2, row 5 → row 6).

For every `Calc0` term `e` there exists an `EMLTerm₂` `e'` whose
real-valued evaluation agrees with `e`'s.

This is the paper's central calculator-equivalence claim: the
3-symbol set `{1, eml(·,·), x}` (here also with `y`) suffices for
every elementary expression in `Calc0 = {exp, ln}`.

**Key identities** (from earlier chunks):
* `eml(x, 1) = exp(x)` (chunk 007)
* `ln(z) = eml(1, eml(eml(1, z), 1))` for all `z` (chunk 011)

**Translation**:
* `varX ↦ varX`, `varY ↦ varY`.
* `exp_ a ↦ eml (translate a) one` (literal Identity 2).
* `ln_ a ↦ eml one (eml (eml one (translate a)) one)`.

The `ln_` translation works because:
  `eml(1, eml(eml(1, t), 1))`
  = `exp(1) − log(exp(exp(1) − log(t)))`
  = `exp(1) − (exp(1) − log(t))`
  = `log(t)`.
-/
theorem calc0_to_eml :
    ∀ e : Calc0, ∃ e' : EMLTerm₂,
      ∀ x y : ℝ, EMLTerm₂.eval x y e' = Calc0.eval x y e := by
  intro e; induction e;
  · exact ⟨ EMLTerm₂.varX, fun x y => rfl ⟩;
  · exact ⟨ EMLTerm₂.varY, fun x y => rfl ⟩;
  · use EMLTerm₂.eml ( Classical.choose ‹_› ) EMLTerm₂.one ; ( intro; simp +decide [ *, EMLTerm₂.eval ] );
    exact fun y => by rw [ Classical.choose_spec ‹∃ e', ∀ x y, EMLTerm₂.eval x y e' = Calc0.eval x y _› _ _, Calc0.eval ] ;
  · obtain ⟨ e', he' ⟩ := ‹_›;
    use EMLTerm₂.eml EMLTerm₂.one (EMLTerm₂.eml (EMLTerm₂.eml EMLTerm₂.one e') EMLTerm₂.one);
    intro x y; simp +decide [EMLTerm₂.eval]
    exact Real.ext_cauchy (congrArg Real.cauchy (congrArg Real.log (he' x y)))

end EML
