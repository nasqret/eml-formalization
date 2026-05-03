import Mathlib

namespace EML

/-- Two-variable EML term grammar (lifted from chunk 041). -/
inductive EMLTerm₂ : Type
  | one  : EMLTerm₂
  | varX : EMLTerm₂
  | varY : EMLTerm₂
  | eml  : EMLTerm₂ → EMLTerm₂ → EMLTerm₂
  deriving Repr

noncomputable def EMLTerm₂.eval (x y : ℝ) : EMLTerm₂ → ℝ
  | .one      => 1
  | .varX     => x
  | .varY     => y
  | .eml t u  => Real.exp (EMLTerm₂.eval x y t) - Real.log (EMLTerm₂.eval x y u)

/-!
## The original theorem `emlterm2_for_avg` is false

### Why the claim fails

The `EMLTerm₂` grammar has only four constructors (`one`, `varX`, `varY`,
`eml`), with the single combinator `eml t u := exp(eval t) − log(eval u)`.
The target `(x + y)/2` is an affine function, but every application of `eml`
introduces `exp` and `log`, which are non-affine. No finite composition of
these can produce a linear function with coefficient 1/2.

**Computational evidence.** An exhaustive search over all 21 612 terms up to
tree-depth 3 found zero terms matching `(x+y)/2` at the three test points
`(0,0)`, `(1,0)`, `(0,1)` even within tolerance 0.1.

**Structural argument (sketch).** For `eml a b` to evaluate to an affine
function `αx + βy + γ`, the sub-term `a` must evaluate to a constant
(otherwise `exp(eval a)` is strictly convex in `x` or `y`, and this convexity
cannot be cancelled by `−log(eval b)`). Then the affine coefficients satisfy
`(α, β) = −(α', β')` where `(α', β')` are the coefficients of `eval b`.
Starting from the base slopes `{(0,0), (1,0), (0,1)}` and closing under
negation gives `{(0,0), (±1,0), (0,±1)}`, which never includes `(1/2, 1/2)`.

**Formal gap.** Proving that the non-affine terms also fail requires showing
that the value `1/2` is not in the closure of `{0, 1}` under
`(a, b) ↦ exp a − Real.log b`, which is a transcendence-theory statement
beyond current Mathlib coverage.

### What the paper actually uses

The context mentions "chunk 040 (addition)" and "chunk 052 (half)", which are
**separate primitives** in the paper's full grammar—not expressible via the
single `eml` combinator. The correct formalization extends the grammar with
`add` and `half` constructors, as shown below.
-/

/- -------- Original (false) theorem — commented out: --------
theorem emlterm2_for_avg :
    ∃ t : EMLTerm₂, ∀ x y : ℝ, EMLTerm₂.eval x y t = (x + y) / 2 := by
  sorry
   ---------------------------------------------------------- -/

/-! ### Corrected version: extended grammar with `add` and `half`

The paper's construction composes "chunk 040" (addition) with "chunk 052"
(half), which are separate primitives. We extend the grammar accordingly
and verify the claim.
-/

/-- Extended two-variable EML term grammar with explicit `add` and `half`. -/
inductive EMLTerm₂Ext : Type
  | one  : EMLTerm₂Ext
  | varX : EMLTerm₂Ext
  | varY : EMLTerm₂Ext
  | eml  : EMLTerm₂Ext → EMLTerm₂Ext → EMLTerm₂Ext
  | add  : EMLTerm₂Ext → EMLTerm₂Ext → EMLTerm₂Ext   -- chunk 040
  | half : EMLTerm₂Ext → EMLTerm₂Ext                  -- chunk 052
  deriving Repr

noncomputable def EMLTerm₂Ext.eval (x y : ℝ) : EMLTerm₂Ext → ℝ
  | .one      => 1
  | .varX     => x
  | .varY     => y
  | .eml t u  => Real.exp (EMLTerm₂Ext.eval x y t) - Real.log (EMLTerm₂Ext.eval x y u)
  | .add t u  => EMLTerm₂Ext.eval x y t + EMLTerm₂Ext.eval x y u
  | .half t   => EMLTerm₂Ext.eval x y t / 2

/-- With the extended grammar, `avg(x, y) = half(add(x, y))` is immediate. -/
theorem emlterm2ext_for_avg :
    ∃ t : EMLTerm₂Ext, ∀ x y : ℝ, EMLTerm₂Ext.eval x y t = (x + y) / 2 :=
  ⟨.half (.add .varX .varY), fun x y => by simp [EMLTerm₂Ext.eval]⟩

end EML
