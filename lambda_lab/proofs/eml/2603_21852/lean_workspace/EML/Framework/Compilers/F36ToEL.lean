import EML.Framework.F36Expr
import EML.Framework.Compilers.ELToEML

/-!
# F36 → EL structural translator

A simple syntactic translation from the paper's `F36Expr` to the
intermediate `ELExpr`. After Phase D widening of `ELExpr.eval?` (the
sister file), most paper primitives now translate directly. The
remaining `none` cases are those whose F36 domain is strictly wider
than the corresponding EL domain (e.g. `sqrt` allows `va = 0` but
EL still needs `0 < va`).

## Constructors that translate (`some`) and why

| F36 | EL | Reason |
|---|---|---|
| `var n`, `one`, `negOne`, `two`, `half_const`, `e_const` | direct | atom |
| `exp a` | `exp (translate a)` | EL `exp` unconditional |
| `log a` | `log (translate a)` | both narrow to `> 0` |
| `inv a` | `inv (translate a)` | both require `va ≠ 0` |
| `half a` | `halve (translate a)` | EL `halve` unconditional |
| `minus a` | `neg (translate a)` | EL `neg` unconditional |
| `sqr a` | `sq (translate a)` | EL `sq` unconditional |
| `sigma a` | `inv (add one (exp (neg ea)))` | denominator ≥ 1 ≠ 0 |
| `cosh a` | `halve (add (exp ea) (exp (neg ea)))` | EL `halve` unconditional |
| `sinh a` | `halve (sub (exp ea) (exp (neg ea)))` | EL `halve` unconditional |
| `tanh a` | `div (sinh ea) (cosh ea)` | cosh > 0 always |
| `artanh a` | `halve (sub (log (add one ea)) (log (sub one ea)))` | F36 spec gives `-1 < a < 1` |
| `add a b` | `add ea eb` | EL `add` unconditional |
| `sub a b` | `sub ea eb` | EL `sub` unconditional |
| `mul a b` | `mul ea eb` | EL `mul` unconditional |
| `div a b` | `div ea eb` | both require `vb ≠ 0` |
| `avg a b` | `avg ea eb` | EL `avg` unconditional |

## Constructors kept as `none` and why

| F36 | reason |
|---|---|
| `pi` | needs complex EL layer |
| `sqrt a` | F36 admits `0 ≤ va`, EL still needs `0 < va`. TODO `mkSqrtNonneg`. |
| `hypot a b` | F36 unconditional, EL needs `(va,vb) ≠ (0,0)`. F36 hypot of `(0,0) = some 0`, EL gives `none` — soundness keeps this `none`. |
| `sin/cos/tan/arcsin/arccos/arctan` | needs complex EL layer |

## Phase B+ widenings (this iteration)

| F36 | EL | Reason |
|---|---|---|
| `arsinh a` | `log (add ea (sqrt (add (sq ea) one)))` | sqrt arg ≥ 1 > 0; outer arg > 0 always |
| `arcosh a` | `log (add ea (sqrt (sub (sq ea) one)))` | requires `1 < va` (boundary excluded) |
| `pow a b` | `pow ea eb` (any `vb` ∈ ℝ) | EL `pow` widened to `0 < va` |
| `logb a b` | `logb ea eb` | EL `logb` widened to `0 < va, va ≠ 1, 0 < vb` |
-/

namespace EML

/-- Partial structural translator from `F36Expr` to `ELExpr`.

Returns `none` for constructors that either need the complex EL
layer (Phase B+ work) **or** whose EL semantics would be strictly
narrower than F36's. Returns `some <EL term>` for constructors whose
EL evaluation provably agrees with F36's wherever F36 is defined. -/
noncomputable def F36Expr.translate? : F36Expr → Option ELExpr
  -- Atoms
  | .var n        => some (.var n)
  | .one          => some .one
  | .negOne       => some .negOne
  | .two          => some .two
  | .half_const   => some .half_const
  | .e_const      => some .e_const
  | .pi           => none  -- TODO Phase B+ : needs complex EL layer
  -- Real-valued unary
  | .exp a        => (translate? a).map .exp
  | .log a        => (translate? a).map .log
  | .inv a        => (translate? a).map .inv
  | .half a       => (translate? a).map .halve
  | .minus a      => (translate? a).map .neg
  | .sqrt _       => none  -- TODO : F36 admits `0 ≤ va`, EL still needs `0 < va`. Add `mkSqrtNonneg`.
  | .sqr a        => (translate? a).map .sq
  | .sigma a      => (translate? a).map (fun ea =>
                       -- σ(x) = 1/(1 + exp(-x)); denominator ≥ 1 ≠ 0
                       ELExpr.inv (.add .one (.exp (.neg ea))))
  -- Trig family — needs complex layer
  | .sin _        => none  -- TODO Phase B+ : needs complex EL layer
  | .cos _        => none  -- TODO Phase B+ : needs complex EL layer
  | .tan _        => none  -- TODO Phase B+ : needs complex EL layer
  | .arcsin _     => none  -- TODO Phase B+ : needs complex EL layer
  | .arccos _     => none  -- TODO Phase B+ : needs complex EL layer
  | .arctan _     => none  -- TODO Phase B+ : needs complex EL layer
  -- Hyperbolic family
  | .sinh a       => (translate? a).map (fun ea =>
                       -- sinh(x) = (exp(x) − exp(−x)) / 2
                       ELExpr.halve (.sub (.exp ea) (.exp (.neg ea))))
  | .cosh a       => (translate? a).map (fun ea =>
                       -- cosh(x) = (exp(x) + exp(−x)) / 2
                       ELExpr.halve (.add (.exp ea) (.exp (.neg ea))))
  | .tanh a       => (translate? a).map (fun ea =>
                       -- tanh(x) = sinh(x) / cosh(x); cosh > 0 always
                       ELExpr.div
                         (.halve (.sub (.exp ea) (.exp (.neg ea))))
                         (.halve (.add (.exp ea) (.exp (.neg ea)))))
  | .arsinh a     => (translate? a).map (fun ea =>
                       -- arsinh(x) = log(x + sqrt(x²+1)); x²+1 ≥ 1 > 0 always,
                       -- and x + sqrt(x²+1) ≥ 1 > 0 always (since sqrt(x²+1) ≥ |x| ≥ -x).
                       ELExpr.log (.add ea (.sqrt (.add (.sq ea) .one))))
  | .arcosh a     => (translate? a).map (fun ea =>
                       -- arcosh(x) = log(x + sqrt(x²−1)); for `1 < x` both sqrt arg
                       -- and outer arg are strictly positive. x = 1 boundary
                       -- excluded by tightening F36Expr.eval? to `1 < va`.
                       ELExpr.log (.add ea (.sqrt (.sub (.sq ea) .one))))
  | .artanh a     => (translate? a).map (fun ea =>
                       -- artanh(x) = (log(1+x) − log(1−x)) / 2;
                       -- F36 spec restricts to `−1 < a < 1`, so both logs are defined.
                       ELExpr.halve
                         (.sub (.log (.add .one ea)) (.log (.sub .one ea))))
  -- Binary
  | .add a b      => match translate? a, translate? b with
                     | some ea, some eb => some (.add ea eb)
                     | _, _ => none
  | .sub a b      => match translate? a, translate? b with
                     | some ea, some eb => some (.sub ea eb)
                     | _, _ => none
  | .mul a b      => match translate? a, translate? b with
                     | some ea, some eb => some (.mul ea eb)
                     | _, _ => none
  | .div a b      => match translate? a, translate? b with
                     | some ea, some eb => some (.div ea eb)
                     | _, _ => none
  | .logb a b     => match translate? a, translate? b with
                     | some ea, some eb => some (.logb ea eb)
                     | _, _ => none
  | .pow a b      => match translate? a, translate? b with
                     | some ea, some eb => some (.pow ea eb)
                     | _, _ => none
  | .avg a b      => match translate? a, translate? b with
                     | some ea, some eb => some (.avg ea eb)
                     | _, _ => none
  -- F36's hypot is now tightened to `(va, vb) ≠ (0, 0)` (the boundary
  -- `(0, 0)` hits §G); EL hypot accepts the same domain, so direct dispatch.
  | .hypot a b    => match translate? a, translate? b with
                     | some ea, some eb => some (.hypot ea eb)
                     | _, _ => none

/-- **Bridging lemma:** structural correctness of the F36 → EL
translator on the constructors it supports.

If `e.translate? = some et` and F36 evaluation yields `some v`,
then EL evaluation of `et` also yields `some v`. -/
theorem F36Expr.translate_correct (e : F36Expr) (et : ELExpr)
    (htrans : e.translate? = some et) (env : Nat → ℝ) (v : ℝ)
    (hev : e.eval? env = some v) :
    et.eval? env = some v := by
  induction e generalizing et v with
  | var n =>
      -- translate? returns `some (.var n)`, eval? returns `some (env n)`
      simp [F36Expr.translate?] at htrans
      subst htrans
      simp [F36Expr.eval?] at hev
      simp [ELExpr.eval?, hev]
  | one =>
      simp [F36Expr.translate?] at htrans
      subst htrans
      simp [F36Expr.eval?] at hev
      simp [ELExpr.eval?, hev]
  | negOne =>
      simp [F36Expr.translate?] at htrans
      subst htrans
      simp [F36Expr.eval?] at hev
      simp [ELExpr.eval?, hev]
  | two =>
      simp [F36Expr.translate?] at htrans
      subst htrans
      simp [F36Expr.eval?] at hev
      simp [ELExpr.eval?, hev]
  | half_const =>
      simp [F36Expr.translate?] at htrans
      subst htrans
      simp [F36Expr.eval?] at hev
      simp [ELExpr.eval?, hev]
  | e_const =>
      simp [F36Expr.translate?] at htrans
      subst htrans
      simp [F36Expr.eval?] at hev
      simp [ELExpr.eval?, hev]
  | pi =>
      -- translate? .pi = none, so htrans : none = some et is impossible
      simp [F36Expr.translate?] at htrans
  | exp a iha =>
      -- translate? returns (translate? a).map .exp
      unfold F36Expr.translate? at htrans
      rw [Option.map_eq_some_iff] at htrans
      obtain ⟨ea, hea, het⟩ := htrans
      subst het
      unfold F36Expr.eval? at hev
      cases ha : a.eval? env with
      | none => rw [ha] at hev; simp at hev
      | some va =>
        rw [ha, Option.map_some] at hev
        have hv : v = Real.exp va := (Option.some.injEq _ _).mp hev.symm
        have ihaev := iha ea hea va ha
        unfold ELExpr.eval?
        rw [ihaev, Option.map_some, hv]
  | log a iha =>
      unfold F36Expr.translate? at htrans
      rw [Option.map_eq_some_iff] at htrans
      obtain ⟨ea, hea, het⟩ := htrans
      subst het
      unfold F36Expr.eval? at hev
      cases ha : a.eval? env with
      | none => rw [ha] at hev; simp at hev
      | some va =>
        rw [ha] at hev
        simp only [Option.bind_some] at hev
        by_cases hpos : 0 < va
        · rw [if_pos hpos] at hev
          have hv : v = Real.log va := (Option.some.injEq _ _).mp hev.symm
          have ihaev := iha ea hea va ha
          unfold ELExpr.eval?
          rw [ihaev]
          simp only [Option.bind_some]
          rw [if_pos hpos, hv]
        · rw [if_neg hpos] at hev; cases hev
  | inv a iha =>
      -- translate? returns (translate? a).map .inv
      unfold F36Expr.translate? at htrans
      rw [Option.map_eq_some_iff] at htrans
      obtain ⟨ea, hea, het⟩ := htrans
      subst het
      unfold F36Expr.eval? at hev
      cases ha : a.eval? env with
      | none => rw [ha] at hev; simp at hev
      | some va =>
        rw [ha] at hev
        simp only [Option.bind_some] at hev
        by_cases hne : va ≠ 0
        · rw [if_pos hne] at hev
          have hv : v = va⁻¹ := (Option.some.injEq _ _).mp hev.symm
          have ihaev := iha ea hea va ha
          unfold ELExpr.eval?
          rw [ihaev]
          simp only [Option.bind_some]
          rw [if_pos hne, hv]
        · rw [if_neg hne] at hev; cases hev
  | half a iha =>
      -- translate? returns (translate? a).map .halve (now unconditional in EL)
      unfold F36Expr.translate? at htrans
      rw [Option.map_eq_some_iff] at htrans
      obtain ⟨ea, hea, het⟩ := htrans
      subst het
      unfold F36Expr.eval? at hev
      cases ha : a.eval? env with
      | none => rw [ha] at hev; simp at hev
      | some va =>
        rw [ha, Option.map_some] at hev
        have hv : v = va / 2 := (Option.some.injEq _ _).mp hev.symm
        have ihaev := iha ea hea va ha
        unfold ELExpr.eval?
        rw [ihaev, Option.map_some, hv]
  | minus a iha =>
      unfold F36Expr.translate? at htrans
      rw [Option.map_eq_some_iff] at htrans
      obtain ⟨ea, hea, het⟩ := htrans
      subst het
      unfold F36Expr.eval? at hev
      cases ha : a.eval? env with
      | none => rw [ha] at hev; simp at hev
      | some va =>
        rw [ha, Option.map_some] at hev
        have hv : v = -va := (Option.some.injEq _ _).mp hev.symm
        have ihaev := iha ea hea va ha
        unfold ELExpr.eval?
        rw [ihaev, Option.map_some, hv]
  | sqrt _ _ =>
      simp [F36Expr.translate?] at htrans
  | sqr a iha =>
      -- translate? returns (translate? a).map .sq (now unconditional in EL)
      unfold F36Expr.translate? at htrans
      rw [Option.map_eq_some_iff] at htrans
      obtain ⟨ea, hea, het⟩ := htrans
      subst het
      unfold F36Expr.eval? at hev
      cases ha : a.eval? env with
      | none => rw [ha] at hev; simp at hev
      | some va =>
        rw [ha, Option.map_some] at hev
        have hv : v = va ^ 2 := (Option.some.injEq _ _).mp hev.symm
        have ihaev := iha ea hea va ha
        unfold ELExpr.eval?
        rw [ihaev, Option.map_some, hv]
  | sigma a iha =>
      -- translate? returns (translate? a).map (fun ea => inv (add one (exp (neg ea))))
      unfold F36Expr.translate? at htrans
      rw [Option.map_eq_some_iff] at htrans
      obtain ⟨ea, hea, het⟩ := htrans
      subst het
      unfold F36Expr.eval? at hev
      cases ha : a.eval? env with
      | none => rw [ha] at hev; simp at hev
      | some va =>
        rw [ha, Option.map_some] at hev
        have hv : v = 1 / (1 + Real.exp (-va)) :=
          (Option.some.injEq _ _).mp hev.symm
        have ihaev := iha ea hea va ha
        -- Now compute EL eval of `inv (add one (exp (neg ea)))`
        -- Inside: exp(neg ea) = Real.exp (-va)
        -- add one (...) = 1 + Real.exp(-va) ≠ 0 (it's ≥ 1)
        have hExpPos : 0 < Real.exp (-va) := Real.exp_pos _
        have hSumPos : 0 < 1 + Real.exp (-va) := by linarith
        have hSumNe : (1 + Real.exp (-va)) ≠ 0 := ne_of_gt hSumPos
        unfold ELExpr.eval?
        -- Inner eval: inv arg = (1 + exp(-va)) wrapped in Option
        show (((ELExpr.add .one (.exp (.neg ea))).eval? env).bind
              fun va' => if va' ≠ 0 then some va'⁻¹ else none) = some v
        -- Compute add one (exp (neg ea))
        have hNeg : (ELExpr.neg ea).eval? env = some (-va) := by
          show (ea.eval? env).map (-·) = _
          rw [ihaev]; rfl
        have hExp : (ELExpr.exp (.neg ea)).eval? env = some (Real.exp (-va)) := by
          show ((ELExpr.neg ea).eval? env).map Real.exp = _
          rw [hNeg]; rfl
        have hInner : (ELExpr.add .one (.exp (.neg ea))).eval? env =
                       some (1 + Real.exp (-va)) := by
          show bind2 ((ELExpr.one).eval? env) ((ELExpr.exp (.neg ea)).eval? env)
                (fun va_ vb_ => some (va_ + vb_)) = _
          rw [hExp]
          rfl
        rw [hInner]
        simp only [Option.bind_some]
        rw [if_pos hSumNe, hv, one_div]
  | sin _ _ => simp [F36Expr.translate?] at htrans
  | cos _ _ => simp [F36Expr.translate?] at htrans
  | tan _ _ => simp [F36Expr.translate?] at htrans
  | arcsin _ _ => simp [F36Expr.translate?] at htrans
  | arccos _ _ => simp [F36Expr.translate?] at htrans
  | arctan _ _ => simp [F36Expr.translate?] at htrans
  | sinh a iha =>
      -- translate? returns (translate? a).map (fun ea => halve (sub (exp ea) (exp (neg ea))))
      unfold F36Expr.translate? at htrans
      rw [Option.map_eq_some_iff] at htrans
      obtain ⟨ea, hea, het⟩ := htrans
      subst het
      unfold F36Expr.eval? at hev
      cases ha : a.eval? env with
      | none => rw [ha] at hev; simp at hev
      | some va =>
        rw [ha, Option.map_some] at hev
        have hv : v = Real.sinh va := (Option.some.injEq _ _).mp hev.symm
        have ihaev := iha ea hea va ha
        unfold ELExpr.eval?
        have hExp1 : (ELExpr.exp ea).eval? env = some (Real.exp va) := by
          show (ea.eval? env).map Real.exp = _
          rw [ihaev]; rfl
        have hNeg : (ELExpr.neg ea).eval? env = some (-va) := by
          show (ea.eval? env).map (-·) = _
          rw [ihaev]; rfl
        have hExp2 : (ELExpr.exp (.neg ea)).eval? env = some (Real.exp (-va)) := by
          show ((ELExpr.neg ea).eval? env).map Real.exp = _
          rw [hNeg]; rfl
        have hInner : (ELExpr.sub (.exp ea) (.exp (.neg ea))).eval? env =
                       some (Real.exp va - Real.exp (-va)) := by
          show bind2 ((ELExpr.exp ea).eval? env) ((ELExpr.exp (.neg ea)).eval? env)
                (fun va_ vb_ => some (va_ - vb_)) = _
          rw [hExp1, hExp2]
          rfl
        rw [hInner]
        simp only [Option.map_some]
        rw [hv, Real.sinh_eq]
  | cosh a iha =>
      -- translate? returns (translate? a).map (fun ea => halve (add (exp ea) (exp (neg ea))))
      unfold F36Expr.translate? at htrans
      rw [Option.map_eq_some_iff] at htrans
      obtain ⟨ea, hea, het⟩ := htrans
      subst het
      unfold F36Expr.eval? at hev
      cases ha : a.eval? env with
      | none => rw [ha] at hev; simp at hev
      | some va =>
        rw [ha, Option.map_some] at hev
        have hv : v = Real.cosh va := (Option.some.injEq _ _).mp hev.symm
        have ihaev := iha ea hea va ha
        unfold ELExpr.eval?
        have hExp1 : (ELExpr.exp ea).eval? env = some (Real.exp va) := by
          show (ea.eval? env).map Real.exp = _
          rw [ihaev]; rfl
        have hNeg : (ELExpr.neg ea).eval? env = some (-va) := by
          show (ea.eval? env).map (-·) = _
          rw [ihaev]; rfl
        have hExp2 : (ELExpr.exp (.neg ea)).eval? env = some (Real.exp (-va)) := by
          show ((ELExpr.neg ea).eval? env).map Real.exp = _
          rw [hNeg]; rfl
        have hInner : (ELExpr.add (.exp ea) (.exp (.neg ea))).eval? env =
                       some (Real.exp va + Real.exp (-va)) := by
          show bind2 ((ELExpr.exp ea).eval? env) ((ELExpr.exp (.neg ea)).eval? env)
                (fun va_ vb_ => some (va_ + vb_)) = _
          rw [hExp1, hExp2]
          rfl
        rw [hInner]
        simp only [Option.map_some]
        rw [hv, Real.cosh_eq]
  | tanh a iha =>
      -- translate? returns (translate? a).map (fun ea =>
      --   div (halve (sub (exp ea) (exp (neg ea))))
      --       (halve (add (exp ea) (exp (neg ea)))))
      unfold F36Expr.translate? at htrans
      rw [Option.map_eq_some_iff] at htrans
      obtain ⟨ea, hea, het⟩ := htrans
      subst het
      unfold F36Expr.eval? at hev
      cases ha : a.eval? env with
      | none => rw [ha] at hev; simp at hev
      | some va =>
        rw [ha, Option.map_some] at hev
        have hv : v = Real.tanh va := (Option.some.injEq _ _).mp hev.symm
        have ihaev := iha ea hea va ha
        have hExp1 : (ELExpr.exp ea).eval? env = some (Real.exp va) := by
          show (ea.eval? env).map Real.exp = _
          rw [ihaev]; rfl
        have hNeg : (ELExpr.neg ea).eval? env = some (-va) := by
          show (ea.eval? env).map (-·) = _
          rw [ihaev]; rfl
        have hExp2 : (ELExpr.exp (.neg ea)).eval? env = some (Real.exp (-va)) := by
          show ((ELExpr.neg ea).eval? env).map Real.exp = _
          rw [hNeg]; rfl
        have hSub : (ELExpr.sub (.exp ea) (.exp (.neg ea))).eval? env =
                     some (Real.exp va - Real.exp (-va)) := by
          show bind2 ((ELExpr.exp ea).eval? env) ((ELExpr.exp (.neg ea)).eval? env)
                (fun va_ vb_ => some (va_ - vb_)) = _
          rw [hExp1, hExp2]; rfl
        have hAdd : (ELExpr.add (.exp ea) (.exp (.neg ea))).eval? env =
                     some (Real.exp va + Real.exp (-va)) := by
          show bind2 ((ELExpr.exp ea).eval? env) ((ELExpr.exp (.neg ea)).eval? env)
                (fun va_ vb_ => some (va_ + vb_)) = _
          rw [hExp1, hExp2]; rfl
        have hHalveSub : (ELExpr.halve (.sub (.exp ea) (.exp (.neg ea)))).eval? env =
                          some ((Real.exp va - Real.exp (-va)) / 2) := by
          show ((ELExpr.sub (.exp ea) (.exp (.neg ea))).eval? env).map (· / 2) = _
          rw [hSub]; rfl
        have hHalveAdd : (ELExpr.halve (.add (.exp ea) (.exp (.neg ea)))).eval? env =
                          some ((Real.exp va + Real.exp (-va)) / 2) := by
          show ((ELExpr.add (.exp ea) (.exp (.neg ea))).eval? env).map (· / 2) = _
          rw [hAdd]; rfl
        -- denominator (Real.exp va + Real.exp (-va)) / 2 ≠ 0
        have hExpVaPos : 0 < Real.exp va := Real.exp_pos _
        have hExpNegVaPos : 0 < Real.exp (-va) := Real.exp_pos _
        have hSumPos : 0 < Real.exp va + Real.exp (-va) := by linarith
        have hDenomPos : 0 < (Real.exp va + Real.exp (-va)) / 2 := by linarith
        have hDenomNe : (Real.exp va + Real.exp (-va)) / 2 ≠ 0 := ne_of_gt hDenomPos
        unfold ELExpr.eval?
        show bind2
              ((ELExpr.halve (.sub (.exp ea) (.exp (.neg ea)))).eval? env)
              ((ELExpr.halve (.add (.exp ea) (.exp (.neg ea)))).eval? env)
              (fun va_ vb_ => if vb_ ≠ 0 then some (va_ / vb_) else none) = some v
        rw [hHalveSub, hHalveAdd]
        simp only [bind2]
        rw [if_pos hDenomNe, hv, Real.tanh_eq_sinh_div_cosh,
            Real.sinh_eq, Real.cosh_eq]
  | arsinh a iha =>
      -- translate? returns (translate? a).map (fun ea =>
      --   log (add ea (sqrt (add (sq ea) one))))
      unfold F36Expr.translate? at htrans
      rw [Option.map_eq_some_iff] at htrans
      obtain ⟨ea, hea, het⟩ := htrans
      subst het
      unfold F36Expr.eval? at hev
      cases ha : a.eval? env with
      | none => rw [ha] at hev; simp at hev
      | some va =>
        rw [ha, Option.map_some] at hev
        have hv : v = Real.arsinh va := (Option.some.injEq _ _).mp hev.symm
        have ihaev := iha ea hea va ha
        -- Build up the EL evaluation step-by-step
        have hSq : (ELExpr.sq ea).eval? env = some (va ^ 2) := by
          show (ea.eval? env).map (fun va => va ^ 2) = _
          rw [ihaev]; rfl
        have hSqAddOne : (ELExpr.add (.sq ea) .one).eval? env =
            some (va ^ 2 + 1) := by
          show bind2 ((ELExpr.sq ea).eval? env) ((ELExpr.one).eval? env)
                (fun va_ vb_ => some (va_ + vb_)) = _
          rw [hSq]; rfl
        have hSqAddOnePos : 0 < va ^ 2 + 1 := by positivity
        have hSqrt : (ELExpr.sqrt (.add (.sq ea) .one)).eval? env =
            some (Real.sqrt (va ^ 2 + 1)) := by
          show ((ELExpr.add (.sq ea) .one).eval? env).bind
                (fun va_ => if 0 < va_ then some (Real.sqrt va_) else none) = _
          rw [hSqAddOne]
          simp only [Option.bind_some]
          rw [if_pos hSqAddOnePos]
        have hSumPos : 0 < va + Real.sqrt (va ^ 2 + 1) := by
          -- sqrt(va^2+1) > sqrt(va^2) = |va| ≥ -va, so va + sqrt(va²+1) > 0.
          have h_abs_le : -va ≤ |va| := neg_le_abs va
          have h_sqrt_eq : Real.sqrt (va ^ 2) = |va| := Real.sqrt_sq_eq_abs va
          have h_sqrt_lt : Real.sqrt (va ^ 2) < Real.sqrt (va ^ 2 + 1) := by
            apply Real.sqrt_lt_sqrt (sq_nonneg va)
            linarith
          rw [h_sqrt_eq] at h_sqrt_lt
          linarith
        have hAddSqrt : (ELExpr.add ea (.sqrt (.add (.sq ea) .one))).eval? env =
            some (va + Real.sqrt (va ^ 2 + 1)) := by
          show bind2 (ea.eval? env)
                ((ELExpr.sqrt (.add (.sq ea) .one)).eval? env)
                (fun va_ vb_ => some (va_ + vb_)) = _
          rw [ihaev, hSqrt]; rfl
        unfold ELExpr.eval?
        show ((ELExpr.add ea (.sqrt (.add (.sq ea) .one))).eval? env).bind
              (fun va_ => if 0 < va_ then some (Real.log va_) else none) = some v
        rw [hAddSqrt]
        simp only [Option.bind_some]
        rw [if_pos hSumPos, hv]
        -- Real.arsinh va = Real.log (va + Real.sqrt (1 + va^2))
        unfold Real.arsinh
        rw [show va ^ 2 + 1 = 1 + va ^ 2 from by ring]
  | arcosh a iha =>
      -- translate? returns (translate? a).map (fun ea =>
      --   log (add ea (sqrt (sub (sq ea) one))))
      unfold F36Expr.translate? at htrans
      rw [Option.map_eq_some_iff] at htrans
      obtain ⟨ea, hea, het⟩ := htrans
      subst het
      unfold F36Expr.eval? at hev
      cases ha : a.eval? env with
      | none => rw [ha] at hev; simp at hev
      | some va =>
        rw [ha] at hev
        simp only [Option.bind_some] at hev
        by_cases hgt : 1 < va
        · rw [if_pos hgt] at hev
          have hv : v = Real.arcosh va := (Option.some.injEq _ _).mp hev.symm
          have ihaev := iha ea hea va ha
          have hva_pos : 0 < va := lt_trans zero_lt_one hgt
          have hSq : (ELExpr.sq ea).eval? env = some (va ^ 2) := by
            show (ea.eval? env).map (fun va => va ^ 2) = _
            rw [ihaev]; rfl
          have hSqSubOne : (ELExpr.sub (.sq ea) .one).eval? env =
              some (va ^ 2 - 1) := by
            show bind2 ((ELExpr.sq ea).eval? env) ((ELExpr.one).eval? env)
                  (fun va_ vb_ => some (va_ - vb_)) = _
            rw [hSq]; rfl
          have hSqSubOnePos : 0 < va ^ 2 - 1 := by nlinarith
          have hSqrt : (ELExpr.sqrt (.sub (.sq ea) .one)).eval? env =
              some (Real.sqrt (va ^ 2 - 1)) := by
            show ((ELExpr.sub (.sq ea) .one).eval? env).bind
                  (fun va_ => if 0 < va_ then some (Real.sqrt va_) else none) = _
            rw [hSqSubOne]
            simp only [Option.bind_some]
            rw [if_pos hSqSubOnePos]
          have hSqrtNonneg : 0 ≤ Real.sqrt (va ^ 2 - 1) := Real.sqrt_nonneg _
          have hSumPos : 0 < va + Real.sqrt (va ^ 2 - 1) := by
            linarith
          have hAddSqrt : (ELExpr.add ea (.sqrt (.sub (.sq ea) .one))).eval? env =
              some (va + Real.sqrt (va ^ 2 - 1)) := by
            show bind2 (ea.eval? env)
                  ((ELExpr.sqrt (.sub (.sq ea) .one)).eval? env)
                  (fun va_ vb_ => some (va_ + vb_)) = _
            rw [ihaev, hSqrt]; rfl
          unfold ELExpr.eval?
          show ((ELExpr.add ea (.sqrt (.sub (.sq ea) .one))).eval? env).bind
                (fun va_ => if 0 < va_ then some (Real.log va_) else none) = some v
          rw [hAddSqrt]
          simp only [Option.bind_some]
          rw [if_pos hSumPos, hv]
          -- Real.arcosh va = Real.log (va + Real.sqrt (va^2 - 1))
          unfold Real.arcosh
          rfl
        · rw [if_neg hgt] at hev; cases hev
  | artanh a iha =>
      -- translate? returns (translate? a).map (fun ea =>
      --   halve (sub (log (add one ea)) (log (sub one ea))))
      unfold F36Expr.translate? at htrans
      rw [Option.map_eq_some_iff] at htrans
      obtain ⟨ea, hea, het⟩ := htrans
      subst het
      unfold F36Expr.eval? at hev
      cases ha : a.eval? env with
      | none => rw [ha] at hev; simp at hev
      | some va =>
        rw [ha] at hev
        simp only [Option.bind_some] at hev
        by_cases hcond : -1 < va ∧ va < 1
        · rw [if_pos hcond] at hev
          have hv : v = Real.artanh va := (Option.some.injEq _ _).mp hev.symm
          have ihaev := iha ea hea va ha
          have h1pa_pos : 0 < 1 + va := by linarith [hcond.1]
          have h1ma_pos : 0 < 1 - va := by linarith [hcond.2]
          have hAdd : (ELExpr.add .one ea).eval? env = some (1 + va) := by
            show bind2 ((ELExpr.one).eval? env) (ea.eval? env)
                  (fun va_ vb_ => some (va_ + vb_)) = _
            rw [ihaev]; rfl
          have hSub : (ELExpr.sub .one ea).eval? env = some (1 - va) := by
            show bind2 ((ELExpr.one).eval? env) (ea.eval? env)
                  (fun va_ vb_ => some (va_ - vb_)) = _
            rw [ihaev]; rfl
          have hLogAdd : (ELExpr.log (.add .one ea)).eval? env = some (Real.log (1 + va)) := by
            show ((ELExpr.add .one ea).eval? env).bind
                  (fun va' => if 0 < va' then some (Real.log va') else none) = _
            rw [hAdd]
            simp only [Option.bind_some]
            rw [if_pos h1pa_pos]
          have hLogSub : (ELExpr.log (.sub .one ea)).eval? env = some (Real.log (1 - va)) := by
            show ((ELExpr.sub .one ea).eval? env).bind
                  (fun va' => if 0 < va' then some (Real.log va') else none) = _
            rw [hSub]
            simp only [Option.bind_some]
            rw [if_pos h1ma_pos]
          have hSubLog : (ELExpr.sub (.log (.add .one ea)) (.log (.sub .one ea))).eval? env =
                          some (Real.log (1 + va) - Real.log (1 - va)) := by
            show bind2 ((ELExpr.log (.add .one ea)).eval? env)
                  ((ELExpr.log (.sub .one ea)).eval? env)
                  (fun va_ vb_ => some (va_ - vb_)) = _
            rw [hLogAdd, hLogSub]; rfl
          unfold ELExpr.eval?
          show ((ELExpr.sub (.log (.add .one ea)) (.log (.sub .one ea))).eval? env).map (· / 2)
                 = some v
          rw [hSubLog, Option.map_some, hv]
          -- Goal: some ((log(1+va) - log(1-va)) / 2) = some (Real.artanh va)
          have hxIcc : va ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_of_lt hcond.1, le_of_lt hcond.2⟩
          rw [Real.artanh_eq_half_log hxIcc,
              Real.log_div (ne_of_gt h1pa_pos) (ne_of_gt h1ma_pos)]
          ring_nf
        · rw [if_neg hcond] at hev; cases hev
  | add a b iha ihb =>
      unfold F36Expr.translate? at htrans
      cases hta : a.translate? with
      | none => rw [hta] at htrans; simp at htrans
      | some ea =>
        cases htb : b.translate? with
        | none => rw [hta, htb] at htrans; simp at htrans
        | some eb =>
          rw [hta, htb] at htrans
          simp only at htrans
          have het : et = ELExpr.add ea eb := by
            exact (Option.some.injEq _ _).mp htrans.symm
          subst het
          unfold F36Expr.eval? at hev
          cases haev : a.eval? env with
          | none => rw [haev] at hev; simp [bind2] at hev
          | some va =>
            cases hbev : b.eval? env with
            | none => rw [haev, hbev] at hev; simp [bind2] at hev
            | some vb =>
              rw [haev, hbev] at hev
              simp [bind2] at hev
              have hv : v = va + vb := hev.symm
              have ihaev := iha ea hta va haev
              have ihbev := ihb eb htb vb hbev
              unfold ELExpr.eval?
              rw [ihaev, ihbev]
              simp [bind2, hv]
  | sub a b iha ihb =>
      unfold F36Expr.translate? at htrans
      cases hta : a.translate? with
      | none => rw [hta] at htrans; simp at htrans
      | some ea =>
        cases htb : b.translate? with
        | none => rw [hta, htb] at htrans; simp at htrans
        | some eb =>
          rw [hta, htb] at htrans
          simp only at htrans
          have het : et = ELExpr.sub ea eb := by
            exact (Option.some.injEq _ _).mp htrans.symm
          subst het
          unfold F36Expr.eval? at hev
          cases haev : a.eval? env with
          | none => rw [haev] at hev; simp [bind2] at hev
          | some va =>
            cases hbev : b.eval? env with
            | none => rw [haev, hbev] at hev; simp [bind2] at hev
            | some vb =>
              rw [haev, hbev] at hev
              simp [bind2] at hev
              have hv : v = va - vb := hev.symm
              have ihaev := iha ea hta va haev
              have ihbev := ihb eb htb vb hbev
              unfold ELExpr.eval?
              rw [ihaev, ihbev]
              simp [bind2, hv]
  | mul a b iha ihb =>
      unfold F36Expr.translate? at htrans
      cases hta : a.translate? with
      | none => rw [hta] at htrans; simp at htrans
      | some ea =>
        cases htb : b.translate? with
        | none => rw [hta, htb] at htrans; simp at htrans
        | some eb =>
          rw [hta, htb] at htrans
          simp only at htrans
          have het : et = ELExpr.mul ea eb :=
            (Option.some.injEq _ _).mp htrans.symm
          subst het
          unfold F36Expr.eval? at hev
          cases haev : a.eval? env with
          | none => rw [haev] at hev; simp [bind2] at hev
          | some va =>
            cases hbev : b.eval? env with
            | none => rw [haev, hbev] at hev; simp [bind2] at hev
            | some vb =>
              rw [haev, hbev] at hev
              simp [bind2] at hev
              have hv : v = va * vb := hev.symm
              have ihaev := iha ea hta va haev
              have ihbev := ihb eb htb vb hbev
              unfold ELExpr.eval?
              rw [ihaev, ihbev]
              simp [bind2, hv]
  | div a b iha ihb =>
      unfold F36Expr.translate? at htrans
      cases hta : a.translate? with
      | none => rw [hta] at htrans; simp at htrans
      | some ea =>
        cases htb : b.translate? with
        | none => rw [hta, htb] at htrans; simp at htrans
        | some eb =>
          rw [hta, htb] at htrans
          simp only at htrans
          have het : et = ELExpr.div ea eb :=
            (Option.some.injEq _ _).mp htrans.symm
          subst het
          unfold F36Expr.eval? at hev
          cases haev : a.eval? env with
          | none => rw [haev] at hev; simp [bind2] at hev
          | some va =>
            cases hbev : b.eval? env with
            | none => rw [haev, hbev] at hev; simp [bind2] at hev
            | some vb =>
              rw [haev, hbev] at hev
              simp only [bind2] at hev
              by_cases hne : vb ≠ 0
              · rw [if_pos hne] at hev
                have hv : v = va / vb := (Option.some.injEq _ _).mp hev.symm
                have ihaev := iha ea hta va haev
                have ihbev := ihb eb htb vb hbev
                unfold ELExpr.eval?
                rw [ihaev, ihbev]
                simp only [bind2]
                rw [if_pos hne, hv]
              · rw [if_neg hne] at hev; cases hev
  | logb a b iha ihb =>
      -- translate? returns `some (.logb ea eb)` when both sub-translations succeed
      unfold F36Expr.translate? at htrans
      cases hta : a.translate? with
      | none => rw [hta] at htrans; simp at htrans
      | some ea =>
        cases htb : b.translate? with
        | none => rw [hta, htb] at htrans; simp at htrans
        | some eb =>
          rw [hta, htb] at htrans
          simp only at htrans
          have het : et = ELExpr.logb ea eb :=
            (Option.some.injEq _ _).mp htrans.symm
          subst het
          unfold F36Expr.eval? at hev
          cases haev : a.eval? env with
          | none => rw [haev] at hev; simp [bind2] at hev
          | some va =>
            cases hbev : b.eval? env with
            | none => rw [haev, hbev] at hev; simp [bind2] at hev
            | some vb =>
              rw [haev, hbev] at hev
              simp only [bind2] at hev
              by_cases hcond : 0 < va ∧ va ≠ 1 ∧ 0 < vb
              · rw [if_pos hcond] at hev
                have hv : v = Real.log vb / Real.log va :=
                  (Option.some.injEq _ _).mp hev.symm
                have ihaev := iha ea hta va haev
                have ihbev := ihb eb htb vb hbev
                unfold ELExpr.eval?
                rw [ihaev, ihbev]
                simp only [bind2]
                rw [if_pos hcond, hv]
              · rw [if_neg hcond] at hev; cases hev
  | pow a b iha ihb =>
      -- translate? returns `some (.pow ea eb)` when both sub-translations succeed
      unfold F36Expr.translate? at htrans
      cases hta : a.translate? with
      | none => rw [hta] at htrans; simp at htrans
      | some ea =>
        cases htb : b.translate? with
        | none => rw [hta, htb] at htrans; simp at htrans
        | some eb =>
          rw [hta, htb] at htrans
          simp only at htrans
          have het : et = ELExpr.pow ea eb :=
            (Option.some.injEq _ _).mp htrans.symm
          subst het
          unfold F36Expr.eval? at hev
          cases haev : a.eval? env with
          | none => rw [haev] at hev; simp [bind2] at hev
          | some va =>
            cases hbev : b.eval? env with
            | none => rw [haev, hbev] at hev; simp [bind2] at hev
            | some vb =>
              rw [haev, hbev] at hev
              simp only [bind2] at hev
              by_cases hpos : 0 < va
              · rw [if_pos hpos] at hev
                have hv : v = Real.rpow va vb :=
                  (Option.some.injEq _ _).mp hev.symm
                have ihaev := iha ea hta va haev
                have ihbev := ihb eb htb vb hbev
                unfold ELExpr.eval?
                rw [ihaev, ihbev]
                simp only [bind2]
                rw [if_pos hpos, hv]
              · rw [if_neg hpos] at hev; cases hev
  | avg a b iha ihb =>
      unfold F36Expr.translate? at htrans
      cases hta : a.translate? with
      | none => rw [hta] at htrans; simp at htrans
      | some ea =>
        cases htb : b.translate? with
        | none => rw [hta, htb] at htrans; simp at htrans
        | some eb =>
          rw [hta, htb] at htrans
          simp only at htrans
          have het : et = ELExpr.avg ea eb :=
            (Option.some.injEq _ _).mp htrans.symm
          subst het
          unfold F36Expr.eval? at hev
          cases haev : a.eval? env with
          | none => rw [haev] at hev; simp [bind2] at hev
          | some va =>
            cases hbev : b.eval? env with
            | none => rw [haev, hbev] at hev; simp [bind2] at hev
            | some vb =>
              rw [haev, hbev] at hev
              simp [bind2] at hev
              have hv : v = (va + vb) / 2 := hev.symm
              have ihaev := iha ea hta va haev
              have ihbev := ihb eb htb vb hbev
              unfold ELExpr.eval?
              rw [ihaev, ihbev]
              simp [bind2, hv]
  | hypot a b iha ihb =>
      unfold F36Expr.translate? at htrans
      cases hta : a.translate? with
      | none => rw [hta] at htrans; simp at htrans
      | some ea =>
        cases htb : b.translate? with
        | none => rw [hta, htb] at htrans; simp at htrans
        | some eb =>
          rw [hta, htb] at htrans
          simp only at htrans
          have het : et = ELExpr.hypot ea eb :=
            (Option.some.injEq _ _).mp htrans.symm
          subst het
          unfold F36Expr.eval? at hev
          cases haev : a.eval? env with
          | none => rw [haev] at hev; simp [bind2] at hev
          | some va =>
            cases hbev : b.eval? env with
            | none => rw [haev, hbev] at hev; simp [bind2] at hev
            | some vb =>
              rw [haev, hbev] at hev
              simp only [bind2] at hev
              by_cases hne : ¬(va = 0 ∧ vb = 0)
              · rw [if_pos hne] at hev
                have hv : v = Real.sqrt (va ^ 2 + vb ^ 2) :=
                  (Option.some.injEq _ _).mp hev.symm
                have ihaev := iha ea hta va haev
                have ihbev := ihb eb htb vb hbev
                unfold ELExpr.eval?
                rw [ihaev, ihbev]
                simp only [bind2]
                rw [if_pos hne, hv]
              · rw [if_neg hne] at hev; cases hev

/-- **Final structural completeness theorem (real-grammar fragment).**

For every `F36Expr` `e` whose `translate?` succeeds (i.e. doesn't
require the complex EL layer or an unconditional EL builder), there
exists an `EMLTerm` whose partial evaluation agrees with `e.eval?`
wherever `e.eval?` is defined.

This is the paper's Theorem 5, restricted to the real-grammar
fragment of F36 covered by the unconditional Phase B builders. The
full theorem (unconditional over all of F36) lands when:
* the complex layer wires in `pi`, `sin`, `cos`, `tan`, `arcsin`,
  `arccos`, `arctan`;
* Phase B+ delivers unconditional builders for `inv`, `half`,
  `sqrt`, `sq`, `mul`, `div`, `pow`, `avg`, `hypot`, `logb`, plus
  the hyperbolic chain (`sinh`, `tanh`, `arsinh`, `arcosh`,
  `artanh`). -/
theorem F36Expr.real_complete (e : F36Expr) (et : ELExpr)
    (htrans : e.translate? = some et) :
    ∃ t : EMLTerm, ∀ env v, e.eval? env = some v →
      t.eval? env = some v := by
  refine ⟨et.compile, ?_⟩
  intro env v hev
  exact ELExpr.compile_correct et env v (translate_correct e et htrans env v hev)

end EML
