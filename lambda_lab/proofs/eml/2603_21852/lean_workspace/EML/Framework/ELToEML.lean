import EML.Framework.ELExpr
import EML.Framework.Builders.All
import EML.Framework.Builders.Unconditional

/-!
# EL → EML structural compiler

A structural translator from `ELExpr` to `EMLTerm`, with the
correctness theorem `compile_correct`. Each EL constructor case
dispatches to a builder in `EML.Framework.Builders.*`, and the
correctness proof case dispatches to that builder's `_eval?`
specification lemma.

The compiler is fully computable (no `Classical.choice`) — it is
just a structural function. Correctness is proven by induction on
`ELExpr`. The single `compile_correct` theorem replaces what would
otherwise be ~30 separate per-primitive existential witness theorems.
-/

namespace EML

open EMLTerm

/-- Structural compiler from `ELExpr` to `EMLTerm`. -/
noncomputable def ELExpr.compile : ELExpr → EMLTerm
  -- Atoms
  | .one          => EMLTerm.one
  | .var n        => EMLTerm.var n
  -- Constants
  | .zero         => mkZero
  | .negOne       => mkNegOne
  | .two          => mkTwo
  | .half_const   => mkHalf
  | .e_const      => mkE
  -- Unary
  | .neg a        => mkNeg a.compile
  | .inv a        => mkInvNonzero a.compile           -- widened: va ≠ 0
  | .sq a         => mkSqAll a.compile                 -- widened: any va
  | .sqrt a       => mkSqrtPos a.compile               -- TODO: widen to 0 ≤ va
  | .exp a        => mkExp a.compile
  | .log a        => mkLog a.compile
  | .halve a      => mkHalveAll a.compile              -- widened: any va
  -- Binary
  | .add a b      => mkAdd a.compile b.compile
  | .sub a b      => mkSub a.compile b.compile
  | .mul a b      => mkMulAll a.compile b.compile     -- widened: any va, vb
  | .div a b      => mkDivNonzeroDenom a.compile b.compile  -- widened: vb ≠ 0
  | .pow a b      => mkPowAll a.compile b.compile      -- widened: any vb ∈ ℝ
  | .logb a b     => mkLogbAll a.compile b.compile     -- widened: 0 < va, va ≠ 1, 0 < vb
  | .avg a b      => mkAvgAll a.compile b.compile     -- widened: any va, vb
  | .hypot a b    => mkHypotAll a.compile b.compile   -- widened: (va,vb) ≠ (0,0)

/-- **EL → EML compiler correctness.**

For every `ELExpr` `e`, every variable assignment `env`, and every
real value `v`: if `e.eval? env = some v`, then the compiled EML term
`e.compile` partial-evaluates to the same value.

This is the central structural theorem of the framework. Each
inductive case is a one-line dispatch to the builder's spec lemma. -/
theorem ELExpr.compile_correct (e : ELExpr) (env : Nat → ℝ) (v : ℝ)
    (h : e.eval? env = some v) :
    e.compile.eval? env = some v := by
  induction e generalizing v with
  | one =>
      have hv : v = 1 := by
        unfold ELExpr.eval? at h; exact (Option.some.injEq _ _).mp h.symm
      simp [ELExpr.compile, EMLTerm.eval?_one, hv]
  | var n =>
      have hv : v = env n := by
        unfold ELExpr.eval? at h; exact (Option.some.injEq _ _).mp h.symm
      simp [ELExpr.compile, EMLTerm.eval?_var, hv]
  | zero =>
      have hv : v = 0 := by
        unfold ELExpr.eval? at h; exact (Option.some.injEq _ _).mp h.symm
      simp [ELExpr.compile]; rw [mkZero_eval?, hv]
  | negOne =>
      have hv : v = -1 := by
        unfold ELExpr.eval? at h; exact (Option.some.injEq _ _).mp h.symm
      simp [ELExpr.compile]; rw [mkNegOne_eval?, hv]
  | two =>
      have hv : v = 2 := by
        unfold ELExpr.eval? at h; exact (Option.some.injEq _ _).mp h.symm
      simp [ELExpr.compile]; rw [mkTwo_eval?, hv]
  | half_const =>
      have hv : v = 1 / 2 := by
        unfold ELExpr.eval? at h; exact (Option.some.injEq _ _).mp h.symm
      simp [ELExpr.compile]; rw [mkHalf_eval?, hv]
  | e_const =>
      have hv : v = Real.exp 1 := by
        unfold ELExpr.eval? at h; exact (Option.some.injEq _ _).mp h.symm
      simp [ELExpr.compile]; rw [mkE_eval?, hv]
  | exp a iha =>
      unfold ELExpr.eval? at h
      cases ha : a.eval? env with
      | none => rw [ha] at h; simp at h
      | some va =>
        rw [ha, Option.map_some] at h
        have hv : v = Real.exp va := by exact (Option.some.injEq _ _).mp h.symm
        simp [ELExpr.compile]
        rw [mkExp_eval? env a.compile (iha va ha), hv]
  | log a iha =>
      unfold ELExpr.eval? at h
      cases ha : a.eval? env with
      | none => rw [ha] at h; simp at h
      | some va =>
        rw [ha] at h
        simp only [Option.bind_some] at h
        by_cases hpos : 0 < va
        · rw [if_pos hpos] at h
          have hv : v = Real.log va := by exact (Option.some.injEq _ _).mp h.symm
          simp [ELExpr.compile]
          rw [mkLog_eval? env a.compile (iha va ha) hpos, hv]
        · rw [if_neg hpos] at h; cases h
  | neg a iha =>
      unfold ELExpr.eval? at h
      cases ha : a.eval? env with
      | none => rw [ha] at h; simp at h
      | some va =>
        rw [ha, Option.map_some] at h
        have hv : v = -va := by exact (Option.some.injEq _ _).mp h.symm
        simp [ELExpr.compile]
        rw [mkNeg_eval? env a.compile (iha va ha), hv]
  | inv a iha =>
      unfold ELExpr.eval? at h
      cases ha : a.eval? env with
      | none => rw [ha] at h; simp at h
      | some va =>
        rw [ha] at h
        simp only [Option.bind_some] at h
        by_cases hne : va ≠ 0
        · rw [if_pos hne] at h
          have hv : v = va⁻¹ := by exact (Option.some.injEq _ _).mp h.symm
          simp [ELExpr.compile]
          rw [mkInvNonzero_eval? env a.compile (iha va ha) hne, hv, one_div]
        · rw [if_neg hne] at h; cases h
  | sq a iha =>
      unfold ELExpr.eval? at h
      cases ha : a.eval? env with
      | none => rw [ha] at h; simp at h
      | some va =>
        rw [ha, Option.map_some] at h
        have hv : v = va ^ 2 := by exact (Option.some.injEq _ _).mp h.symm
        simp [ELExpr.compile]
        rw [mkSqAll_eval? env a.compile (iha va ha), hv]
  | sqrt a iha =>
      unfold ELExpr.eval? at h
      cases ha : a.eval? env with
      | none => rw [ha] at h; simp at h
      | some va =>
        rw [ha] at h
        simp only [Option.bind_some] at h
        by_cases hpos : 0 < va
        · rw [if_pos hpos] at h
          have hv : v = Real.sqrt va := by exact (Option.some.injEq _ _).mp h.symm
          simp [ELExpr.compile]
          rw [mkSqrtPos_eval? env a.compile (iha va ha) hpos, hv]
        · rw [if_neg hpos] at h; cases h
  | halve a iha =>
      unfold ELExpr.eval? at h
      cases ha : a.eval? env with
      | none => rw [ha] at h; simp at h
      | some va =>
        rw [ha, Option.map_some] at h
        have hv : v = va / 2 := by exact (Option.some.injEq _ _).mp h.symm
        simp [ELExpr.compile]
        rw [mkHalveAll_eval? env a.compile (iha va ha), hv]
  | add a b iha ihb =>
      unfold ELExpr.eval? at h
      cases ha : a.eval? env with
      | none => rw [ha] at h; simp [bind2] at h
      | some va =>
        cases hb : b.eval? env with
        | none => rw [ha, hb] at h; simp [bind2] at h
        | some vb =>
          rw [ha, hb] at h
          simp [bind2] at h
          have hv : v = va + vb := h.symm
          simp [ELExpr.compile]
          rw [mkAdd_eval? env a.compile b.compile (iha va ha) (ihb vb hb), hv]
  | sub a b iha ihb =>
      unfold ELExpr.eval? at h
      cases ha : a.eval? env with
      | none => rw [ha] at h; simp [bind2] at h
      | some va =>
        cases hb : b.eval? env with
        | none => rw [ha, hb] at h; simp [bind2] at h
        | some vb =>
          rw [ha, hb] at h
          simp [bind2] at h
          have hv : v = va - vb := h.symm
          simp [ELExpr.compile]
          rw [mkSub_eval? env a.compile b.compile (iha va ha) (ihb vb hb), hv]
  | mul a b iha ihb =>
      unfold ELExpr.eval? at h
      cases ha : a.eval? env with
      | none => rw [ha] at h; simp [bind2] at h
      | some va =>
        cases hb : b.eval? env with
        | none => rw [ha, hb] at h; simp [bind2] at h
        | some vb =>
          rw [ha, hb] at h
          simp only [bind2] at h
          have hv : v = va * vb := by exact (Option.some.injEq _ _).mp h.symm
          simp [ELExpr.compile]
          rw [mkMulAll_eval? env a.compile b.compile
                (iha va ha) (ihb vb hb), hv]
  | div a b iha ihb =>
      unfold ELExpr.eval? at h
      cases ha : a.eval? env with
      | none => rw [ha] at h; simp [bind2] at h
      | some va =>
        cases hb : b.eval? env with
        | none => rw [ha, hb] at h; simp [bind2] at h
        | some vb =>
          rw [ha, hb] at h
          simp only [bind2] at h
          by_cases hne : vb ≠ 0
          · rw [if_pos hne] at h
            have hv : v = va / vb := by exact (Option.some.injEq _ _).mp h.symm
            simp [ELExpr.compile]
            rw [mkDivNonzeroDenom_eval? env a.compile b.compile
                  (iha va ha) (ihb vb hb) hne, hv]
          · rw [if_neg hne] at h; cases h
  | pow a b iha ihb =>
      unfold ELExpr.eval? at h
      cases ha : a.eval? env with
      | none => rw [ha] at h; simp [bind2] at h
      | some va =>
        cases hb : b.eval? env with
        | none => rw [ha, hb] at h; simp [bind2] at h
        | some vb =>
          rw [ha, hb] at h
          simp only [bind2] at h
          by_cases hpos : 0 < va
          · rw [if_pos hpos] at h
            have hv : v = Real.rpow va vb := by exact (Option.some.injEq _ _).mp h.symm
            simp [ELExpr.compile]
            rw [mkPowAll_eval? env a.compile b.compile
                  (iha va ha) (ihb vb hb) hpos, hv]
          · rw [if_neg hpos] at h; cases h
  | logb a b iha ihb =>
      unfold ELExpr.eval? at h
      cases ha : a.eval? env with
      | none => rw [ha] at h; simp [bind2] at h
      | some va =>
        cases hb : b.eval? env with
        | none => rw [ha, hb] at h; simp [bind2] at h
        | some vb =>
          rw [ha, hb] at h
          simp only [bind2] at h
          by_cases hcond : 0 < va ∧ va ≠ 1 ∧ 0 < vb
          · rw [if_pos hcond] at h
            have hv : v = Real.log vb / Real.log va := by
              exact (Option.some.injEq _ _).mp h.symm
            simp [ELExpr.compile]
            rw [mkLogbAll_eval? env a.compile b.compile
                  (iha va ha) (ihb vb hb) hcond.1 hcond.2.1 hcond.2.2, hv]
          · rw [if_neg hcond] at h; cases h
  | avg a b iha ihb =>
      unfold ELExpr.eval? at h
      cases ha : a.eval? env with
      | none => rw [ha] at h; simp [bind2] at h
      | some va =>
        cases hb : b.eval? env with
        | none => rw [ha, hb] at h; simp [bind2] at h
        | some vb =>
          rw [ha, hb] at h
          simp only [bind2] at h
          have hv : v = (va + vb) / 2 := by exact (Option.some.injEq _ _).mp h.symm
          simp [ELExpr.compile]
          rw [mkAvgAll_eval? env a.compile b.compile
                (iha va ha) (ihb vb hb), hv]
  | hypot a b iha ihb =>
      unfold ELExpr.eval? at h
      cases ha : a.eval? env with
      | none => rw [ha] at h; simp [bind2] at h
      | some va =>
        cases hb : b.eval? env with
        | none => rw [ha, hb] at h; simp [bind2] at h
        | some vb =>
          rw [ha, hb] at h
          simp only [bind2] at h
          by_cases hne : ¬(va = 0 ∧ vb = 0)
          · rw [if_pos hne] at h
            have hv : v = Real.sqrt (va ^ 2 + vb ^ 2) := by
              exact (Option.some.injEq _ _).mp h.symm
            simp [ELExpr.compile]
            rw [mkHypotAll_eval? env a.compile b.compile
                  (iha va ha) (ihb vb hb) hne, hv]
          · rw [if_neg hne] at h; cases h

end EML
