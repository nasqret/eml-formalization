import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import EML.Basic
import EML.Term

/-!
# Calculator-language inductives (Table 2 of arXiv:2603.21852)

This module formalizes the six calculator configurations from the paper's
"calculator-configuration ablation" table as small abstract-syntax types
together with real-valued evaluators. Each configuration is parameterised
by two free variables `x y : ℝ`; constants are zero-ary constructors and
operations are constructors of the appropriate arity.

## Scope

The paper's `Wolfram` row mentions the imaginary unit `i ∈ ℂ` and the
generic complex power `x ∧ y` (= `x^y`) which is multivalued / signed.
We restrict to the **real-valued subset** of the calculator chain so the
translation lemmas live entirely in `ℝ`. The omission of `i` and the
restriction of `pow` to `Real.rpow` (which agrees with the principal
branch for positive bases) are flagged in each chunk's `notes`.

## Source

Each row of the table:

| Config   | Constants | Unary ops              | Binary ops    |
|----------|-----------|------------------------|---------------|
| Wolfram  | π, e, i   | ln                     | +, ×, ∧       |
| Calc 3   | none      | exp, ln, −x, 1/x       | +             |
| Calc 2   | none      | exp, ln                | −             |
| Calc 1   | e or π    | none                   | x^y, log_x(y) |
| Calc 0   | none      | exp                    | log_x(y)      |
| EML      | 1         | none                   | eml(x,y)      |

The paper's EML row is realised by the existing `EMLTerm₂` from chunk 036.

-/

namespace EML

/-- Wolfram calculator (real-valued subset).
Constants: π, e (the imaginary unit `i` is dropped — see module docstring).
Unary: ln. Binary: +, ×, ∧ (power, restricted to `Real.rpow`).
-/
inductive Wolfram : Type
  | piConst : Wolfram
  | eConst  : Wolfram
  | varX    : Wolfram
  | varY    : Wolfram
  | ln      : Wolfram → Wolfram
  | add     : Wolfram → Wolfram → Wolfram
  | mul     : Wolfram → Wolfram → Wolfram
  | pow     : Wolfram → Wolfram → Wolfram
  deriving Repr

/-- Real-valued evaluation of a `Wolfram` term. `pow` uses `Real.rpow`;
the imaginary-unit constructor is omitted by design. -/
noncomputable def Wolfram.eval (x y : ℝ) : Wolfram → ℝ
  | .piConst => Real.pi
  | .eConst  => Real.exp 1
  | .varX    => x
  | .varY    => y
  | .ln a    => Real.log (Wolfram.eval x y a)
  | .add a b => Wolfram.eval x y a + Wolfram.eval x y b
  | .mul a b => Wolfram.eval x y a * Wolfram.eval x y b
  | .pow a b => (Wolfram.eval x y a) ^ (Wolfram.eval x y b)

/-- Calculator 3: constants none, unary {exp, ln, −·, 1/·}, binary {+}. -/
inductive Calc3 : Type
  | varX : Calc3
  | varY : Calc3
  | exp_ : Calc3 → Calc3
  | ln_  : Calc3 → Calc3
  | neg  : Calc3 → Calc3
  | inv  : Calc3 → Calc3
  | add  : Calc3 → Calc3 → Calc3
  deriving Repr

/-- Real evaluation of `Calc3`. `inv 0` is `0` per Mathlib's `Real` field
convention, which agrees with the calculator semantics on its domain. -/
noncomputable def Calc3.eval (x y : ℝ) : Calc3 → ℝ
  | .varX    => x
  | .varY    => y
  | .exp_ a  => Real.exp (Calc3.eval x y a)
  | .ln_ a   => Real.log (Calc3.eval x y a)
  | .neg a   => -(Calc3.eval x y a)
  | .inv a   => (Calc3.eval x y a)⁻¹
  | .add a b => Calc3.eval x y a + Calc3.eval x y b

/-- Calculator 2: constants none, unary {exp, ln}, binary {−}. -/
inductive Calc2 : Type
  | varX : Calc2
  | varY : Calc2
  | exp_ : Calc2 → Calc2
  | ln_  : Calc2 → Calc2
  | sub  : Calc2 → Calc2 → Calc2
  deriving Repr

/-- Real evaluation of `Calc2`. -/
noncomputable def Calc2.eval (x y : ℝ) : Calc2 → ℝ
  | .varX    => x
  | .varY    => y
  | .exp_ a  => Real.exp (Calc2.eval x y a)
  | .ln_ a   => Real.log (Calc2.eval x y a)
  | .sub a b => Calc2.eval x y a - Calc2.eval x y b

/-- Calculator 1: constants {e}, unary none, binary {x^y, log_x(y)}.

Following the paper we keep a single base constant `e`; π would also
suffice (`Real.log Real.pi ≠ 0`), but `e` is closer to the natural
exponential identities used in the paper.
-/
inductive Calc1 : Type
  | eConst : Calc1
  | varX   : Calc1
  | varY   : Calc1
  | pow    : Calc1 → Calc1 → Calc1
  | logb   : Calc1 → Calc1 → Calc1   -- log_a(b)
  deriving Repr

/-- Real evaluation of `Calc1`. `logb a b = Real.log b / Real.log a`. -/
noncomputable def Calc1.eval (x y : ℝ) : Calc1 → ℝ
  | .eConst   => Real.exp 1
  | .varX     => x
  | .varY     => y
  | .pow a b  => (Calc1.eval x y a) ^ (Calc1.eval x y b)
  | .logb a b => Real.log (Calc1.eval x y b) / Real.log (Calc1.eval x y a)

/-- Calculator 0: constants none, unary {exp}, binary {log_x(y)}. -/
inductive Calc0 : Type
  | varX : Calc0
  | varY : Calc0
  | exp_ : Calc0 → Calc0
  | logb : Calc0 → Calc0 → Calc0
  deriving Repr

/-- Real evaluation of `Calc0`. -/
noncomputable def Calc0.eval (x y : ℝ) : Calc0 → ℝ
  | .varX     => x
  | .varY     => y
  | .exp_ a   => Real.exp (Calc0.eval x y a)
  | .logb a b => Real.log (Calc0.eval x y b) / Real.log (Calc0.eval x y a)

/-! ### EML row of Table 2

The paper's EML calculator has constants `{1}`, no unary operators, and
the single binary `eml(x, y) = exp(x) − ln(y)`. The corresponding term
type with two free variables is exactly `EMLTerm₂` introduced in
chunk 036, redeclared here so the calc-equivalence chunks can refer to
it without an explicit `Solutions` import.
-/

/-- Two-variable EML term language (mirrors `EMLTerm₂` from chunk 036
but with two named variables `x` and `y`). This is the destination of
the calculator-equivalence chain. -/
inductive EMLTerm₂ : Type
  | one  : EMLTerm₂
  | varX : EMLTerm₂
  | varY : EMLTerm₂
  | eml  : EMLTerm₂ → EMLTerm₂ → EMLTerm₂
  deriving Repr

/-- Real evaluation of a two-variable EML term. -/
noncomputable def EMLTerm₂.eval (x y : ℝ) : EMLTerm₂ → ℝ
  | .one     => 1
  | .varX    => x
  | .varY    => y
  | .eml a b => Real.exp (EMLTerm₂.eval x y a) - Real.log (EMLTerm₂.eval x y b)

end EML
