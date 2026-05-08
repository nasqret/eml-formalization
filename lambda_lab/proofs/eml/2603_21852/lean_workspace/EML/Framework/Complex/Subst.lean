import EML.Framework.Complex.Term

/-!
# Variable substitution on `EMLTermℂ`

`t.subst0 s` replaces every occurrence of `.var 0` in `t` with the term
`s`, leaving all other variables (`.var (n+1)`) unchanged.

This is the foundational operation for **Plan C** in
`OPEN_QUESTIONS.md` — full-real-domain trig via multi-witness
periodicity. To prove `Real.sin x` is realised by some EML term for
`|x| ≥ π`, we take an existing witness `t_base` that handles `x` in the
fundamental domain `(-π, π) \ {0}` and *substitute* `.var 0` with a
"shift" term `s_k` whose evaluation is `((x − 2πk : ℝ) : ℂ)`. The
composite witness `t_base.subst0 s_k` evaluates correctly via
`Real.sin_periodic`.

The same machinery applies to `sin`, `cos`, `tan` (with period `π`),
and `arctan` (with period `π` after appropriate identity rewriting).

## Eval bridge

The key lemma is `eval?_subst0`: substitution at the term level is
equivalent to environment shifting at the eval level. If
`s.eval? env = some s_val`, then for any `t`,

```
(t.subst0 s).eval? env  =  t.eval? (env[0 ↦ s_val])
```

This lets us reduce *"prove the substituted witness's eval matches f x"*
to *"prove the base witness's eval matches f y"* where `y = (eval of s)`,
and finally apply Mathlib's periodicity lemmas.
-/

namespace EML
namespace EMLTermℂ

/-- Substitute `.var 0` in `t` with `s`. Higher-indexed variables are
left untouched. Argument order is target-first so dot notation
`t.subst0 s` reads naturally as "substitute `s` into `t`". -/
def subst0 : EMLTermℂ → EMLTermℂ → EMLTermℂ
  | .one,       _ => .one
  | .var 0,     s => s
  | .var (n+1), _ => .var (n+1)
  | .eml a b,   s => .eml (a.subst0 s) (b.subst0 s)

@[simp] lemma subst0_one (s : EMLTermℂ) : (EMLTermℂ.one).subst0 s = .one := rfl

@[simp] lemma subst0_var_zero (s : EMLTermℂ) :
    (EMLTermℂ.var 0).subst0 s = s := rfl

@[simp] lemma subst0_var_succ (s : EMLTermℂ) (n : Nat) :
    (EMLTermℂ.var (n + 1)).subst0 s = .var (n + 1) := rfl

@[simp] lemma subst0_eml (s a b : EMLTermℂ) :
    (EMLTermℂ.eml a b).subst0 s = .eml (a.subst0 s) (b.subst0 s) := rfl

/-- The "shifted environment": replaces `env 0` with `s_val`, leaves
the rest. Helper for stating `eval?_subst0` cleanly. -/
def envShift0 (s_val : ℂ) (env : Nat → ℂ) : Nat → ℂ :=
  fun n => if n = 0 then s_val else env n

@[simp] lemma envShift0_zero (s_val : ℂ) (env : Nat → ℂ) :
    envShift0 s_val env 0 = s_val := by simp [envShift0]

@[simp] lemma envShift0_succ (s_val : ℂ) (env : Nat → ℂ) (n : Nat) :
    envShift0 s_val env (n + 1) = env (n + 1) := by simp [envShift0]

/-- **Substitution-environment correspondence.** Substituting `.var 0`
with `s` at the term level is equivalent to shifting the environment
at index 0 to `s.eval? env`. -/
lemma eval?_subst0 {env : Nat → ℂ} {s : EMLTermℂ} {s_val : ℂ}
    (hs : s.eval? env = some s_val)
    (t : EMLTermℂ) :
    (t.subst0 s).eval? env = t.eval? (envShift0 s_val env) := by
  induction t with
  | one => rfl
  | var n =>
    match n with
    | 0 =>
      rw [subst0_var_zero, hs]
      rw [EMLTermℂ.eval?_var, envShift0_zero]
    | n + 1 =>
      rw [subst0_var_succ]
      rw [EMLTermℂ.eval?_var, EMLTermℂ.eval?_var, envShift0_succ]
  | eml a b iha ihb =>
    rw [subst0_eml]
    unfold EMLTermℂ.eval?
    rw [iha, ihb]

/-- Useful corollary: when `s.eval? env = some s_val`, the substituted
term's eval is determined entirely by `t`'s eval at the shifted env. -/
lemma eval?_subst0_some_iff {env : Nat → ℂ} {s : EMLTermℂ} {s_val : ℂ}
    (hs : s.eval? env = some s_val) (t : EMLTermℂ) (v : ℂ) :
    (t.subst0 s).eval? env = some v ↔
      t.eval? (envShift0 s_val env) = some v := by
  rw [eval?_subst0 hs]

end EMLTermℂ
end EML
