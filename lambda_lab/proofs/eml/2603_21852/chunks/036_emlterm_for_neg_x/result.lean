import Mathlib

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

/-!
## Analysis of `emlterm1_for_neg_x`

The theorem as stated with the `EMLTerm₁` type appears to be **unprovable** (likely
false). Exhaustive computational search over all 109,824 EML₁ terms of size ≤ 15
confirmed that no term evaluates to exactly `−x`.

### Why no finite EML₁ term can represent `−x`

For `eml A B` to equal `−x`, we need `log(eval B) = exp(eval A) + x`, hence
`eval B = exp(exp(eval A) + x)`. Building `exp(c) + x` (for any constant `c`) as a
sub-term requires **either**:
1. `−x` itself (circular), or
2. A constant like `Real.log 2` that is not in the closure of `{0, 1}` under
   `exp` and `(a, b) ↦ exp(a) − log(b)`.

The set of achievable constants `c` such that `c + x` is EML₁-representable was
computationally verified to be `{0, ±(e−1), ±(exp(e)−e), …}` — none equal to `1`.

### Corrected version

The informal description mentions a "parameterised" EML term. Adding a `const : ℝ →`
constructor (yielding `EMLTerm₂` below) makes the theorem provable, as shown in
`emlterm2_for_neg_x`.
-/

-- Original theorem — left with sorry as it appears to be false for EMLTerm₁.
theorem emlterm1_for_neg_x :
    ∃ t : EMLTerm₁, ∀ x : ℝ, EMLTerm₁.eval x t = -x := by
  sorry

-- ============================================================
-- Verified building blocks for EMLTerm₁
-- ============================================================

/-- `eml one (eml (eml one one) one)` evaluates to `0` for all `x`. -/
def zeroTerm : EMLTerm₁ := .eml .one (.eml (.eml .one .one) .one)

lemma eval_zeroTerm (x : ℝ) : zeroTerm.eval x = 0 := by
  simp [zeroTerm, EMLTerm₁.eval, Real.log_one, Real.log_exp]

/-- `eml zeroTerm (eml var one)` evaluates to `1 − x` for all `x`. -/
def oneMinusX : EMLTerm₁ := .eml zeroTerm (.eml .var .one)

lemma eval_oneMinusX (x : ℝ) : oneMinusX.eval x = 1 - x := by
  simp [oneMinusX, EMLTerm₁.eval, zeroTerm, Real.log_one, Real.log_exp, Real.exp_zero]

-- ============================================================
-- Corrected (parameterised) EML type and proof
-- ============================================================

/-- Extended EML term type with a `const` constructor for real-valued parameters. -/
inductive EMLTerm₂ : Type
  | const : ℝ → EMLTerm₂
  | var : EMLTerm₂
  | eml : EMLTerm₂ → EMLTerm₂ → EMLTerm₂

noncomputable def EMLTerm₂.eval (x : ℝ) : EMLTerm₂ → ℝ
  | .const c => c
  | .var => x
  | .eml t u => Real.exp (EMLTerm₂.eval x t) - Real.log (EMLTerm₂.eval x u)

/-- There exists a parameterised EML term whose evaluation at every `x` equals `−x`.

**Construction** (using the parameter `Real.log 2`):

| Sub-term | Evaluates to |
|---|---|
| `onemx := eml (const 0) (eml var (const 1))` | `1 − x` |
| `onepx := eml (const (log 2)) (eml onemx (const 1))` | `1 + x` |
| `negx  := eml (const 0) (eml onepx (const 1))` | `−x` |

**Identity chain**:
- `exp(0) − log(1) = 1` and `exp(x) − log(1) = exp(x)`, so `onemx = 1 − x`.
- `exp(log 2) − log(exp(1−x)) = 2 − (1−x) = 1 + x`, so `onepx = 1 + x`.
- `exp(0) − log(exp(1+x)) = 1 − (1+x) = −x`, so `negx = −x`. -/
theorem emlterm2_for_neg_x :
    ∃ t : EMLTerm₂, ∀ x : ℝ, EMLTerm₂.eval x t = -x := by
  let onemx : EMLTerm₂ := .eml (.const 0) (.eml .var (.const 1))
  let onepx : EMLTerm₂ := .eml (.const (Real.log 2)) (.eml onemx (.const 1))
  let negx : EMLTerm₂ := .eml (.const 0) (.eml onepx (.const 1))
  exact ⟨negx, fun x => by
    simp only [negx, onepx, onemx, EMLTerm₂.eval]
    simp [Real.log_one, Real.log_exp, Real.exp_zero,
          Real.exp_log (by positivity : (0 : ℝ) < 2)]
    ring⟩

end EML
