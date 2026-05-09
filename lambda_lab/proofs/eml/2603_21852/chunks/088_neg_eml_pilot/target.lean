import Mathlib

/-!
# Plan E pilot — `−EML` atom witnesses

The −EML grammar (paper §3.1, line 282):
```
NegEMLTerm ::= 1 ∣ xₙ ∣ minusInfinity ∣ negEml(T, T)
              negEml(x, y) := log(x) − exp(y)
```

paired with the constant `−∞` (`EReal.bot`).

This pilot tests whether `−EML` per-primitive completeness can be
formalized in Lean. For finite-real partial-eval, we use `EReal` to
accommodate `−∞` as a primitive value. The simplest atoms are `1`,
`var 0`, `−∞`, and `log x` (since `negEml(x, −∞) = log x − exp(−∞) =
log x − 0 = log x`).

Goal: define the grammar, prove the four trivial atom witnesses.
-/

namespace NegEMLPilot

/-- The −EML term grammar over EReal (extended reals). -/
inductive NegEMLTerm
  | one : NegEMLTerm
  | var : Nat → NegEMLTerm
  | minusInf : NegEMLTerm
  | negEml : NegEMLTerm → NegEMLTerm → NegEMLTerm
  deriving Repr

/-- Partial evaluation. Returns `none` outside the domain of `negEml`
(which requires `x > 0` for `log x` to be defined; `exp y` is total).

Note: we use `EReal` to support `minusInf`. The eval of `negEml(x, y) =
log(x) − exp(y)` is `log x − exp y` interpreted in `EReal`:
- For finite `x > 0`, `log x` is finite.
- For `x = ⊥` (i.e. `−∞`), `log x` is `⊥` (junk in EReal).
- `exp(−∞) = 0`. -/
noncomputable def NegEMLTerm.eval? (env : Nat → EReal) : NegEMLTerm → Option EReal
  | .one => some 1
  | .var n => some (env n)
  | .minusInf => some ⊥
  | .negEml a b => (a.eval? env).bind fun va =>
                     (b.eval? env).bind fun vb =>
                       -- negEml(x, y) = log(x) - exp(y) only if x > 0.
                       -- Use EReal.log and EReal.exp where available; or
                       -- restrict to finite real values.
                       if h : (∃ ra : ℝ, va = (ra : EReal) ∧ 0 < ra) then
                         match va, vb with
                         | (ra : EReal), (rb : EReal) =>
                             some ((Real.log ra : EReal) - (Real.exp rb : EReal))
                         | _, _ => none
                       else none

/-- **E1** — Witness for `1`. -/
theorem negEml_witness_one :
    ∃ t : NegEMLTerm, ∀ env : Nat → EReal, t.eval? env = some 1 := by
  sorry

/-- **E2** — Witness for variable `x` (i.e. `env 0`). -/
theorem negEml_witness_var :
    ∃ t : NegEMLTerm, ∀ env : Nat → EReal, t.eval? env = some (env 0) := by
  sorry

/-- **E3** — Witness for `−∞`. -/
theorem negEml_witness_minusInf :
    ∃ t : NegEMLTerm, ∀ env : Nat → EReal, t.eval? env = some (⊥ : EReal) := by
  sorry

end NegEMLPilot
