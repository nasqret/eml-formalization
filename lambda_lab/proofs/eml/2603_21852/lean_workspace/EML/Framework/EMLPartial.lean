import EML.Term
import EML.Framework.Partial

/-!
# Partial evaluation of EML terms

`EMLTerm.eval?` is the partial-semantics version of `EMLTerm.eval`. It
returns `none` exactly when some sub-`eml(_, b)` has its second
argument `b` evaluate to a non-positive real (so `log b` would be
undefined under paper semantics). This is the right semantics for the
paper's intended math; the total `Real.log` is just a Lean
implementation artefact.

The bridge `eval?_eq_some_iff` lets us lift any existing total-eval
witness `t.eval env = v` (proved in chunks 030–067) to the partial
form `t.eval? env = some v`, **provided** we also prove the witness
stays in the partial domain (every nested `eml(_, b)` has `b > 0`).

For witnesses where positivity is automatic (e.g. `eml(t, .one)`,
since `1 > 0`), the lift is trivial. For others (like chunk 061's
artanh witness, where intermediate sub-terms must be shown positive
on the artanh domain), the existing positivity sub-lemmas already
discharge the obligation.
-/

namespace EML

/-- Partial-semantics evaluation of an EML term. Returns `none` if any
intermediate `eml(_, b)` has `b ≤ 0`. -/
noncomputable def EMLTerm.eval? (env : Nat → ℝ) : EMLTerm → Option ℝ
  | .one     => some 1
  | .var n   => some (env n)
  | .eml a b =>
      match EMLTerm.eval? env a, EMLTerm.eval? env b with
      | some va, some vb =>
          if 0 < vb then some (Real.exp va - Real.log vb) else none
      | _, _ => none

@[simp] lemma EMLTerm.eval?_one (env : Nat → ℝ) :
    (EMLTerm.one).eval? env = some 1 := rfl

@[simp] lemma EMLTerm.eval?_var (env : Nat → ℝ) (n : Nat) :
    (EMLTerm.var n).eval? env = some (env n) := rfl

/-- Constructive `eml` rule: when both children evaluate and the second
is strictly positive, the partial eval gives the expected value. -/
lemma EMLTerm.eval?_eml_of_pos
    {env : Nat → ℝ} {a b : EMLTerm} {va vb : ℝ}
    (ha : a.eval? env = some va) (hb : b.eval? env = some vb)
    (hvb : 0 < vb) :
    (EMLTerm.eml a b).eval? env = some (Real.exp va - Real.log vb) := by
  unfold EMLTerm.eval?
  rw [ha, hb]
  simp [hvb]

/-- Bridge: when partial eval is defined, it agrees with the existing
total `EMLTerm.eval`. Useful for lifting existing chunk witnesses. -/
lemma EMLTerm.eval?_eq_some_iff (t : EMLTerm) (env : Nat → ℝ) (v : ℝ) :
    t.eval? env = some v → EMLTerm.eval env t = v := by
  induction t generalizing v with
  | one =>
      intro h
      simp [EMLTerm.eval?] at h
      exact h ▸ rfl
  | var n =>
      intro h
      simp [EMLTerm.eval?] at h
      exact h ▸ rfl
  | eml a b iha ihb =>
      intro h
      unfold EMLTerm.eval? at h
      split at h
      next va vb hva hvb =>
        split at h
        next hpos =>
          have hav := iha va hva
          have hbv := ihb vb hvb
          simp only [EMLTerm.eval, hav, hbv]
          exact (Option.some.injEq _ _).mp h
        next _ => simp at h
      next _ => simp at h

end EML
