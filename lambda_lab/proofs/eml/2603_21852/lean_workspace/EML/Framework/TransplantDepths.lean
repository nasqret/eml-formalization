import EML.Framework.Builders
import EML.Framework.EMLPartial

/-!
# Variable-transplant depths — Lean answer to SI §1.5 question #5

The source paper's Supplementary Information lists, on page 8 of the
SI, seven explicit open questions. Question #5 reads:

> *"Known identity function has depth four, allowing for transplanting
> variables down the tree by multiples of 4. Are there other of this
> kind, with various depths?"*

This module gives a Lean-checkable affirmative answer for the
multiples-of-4 part. We:

1. Define `EMLTerm.depth` and `EMLTerm.subst0` (variable-zero
   substitution on the real fragment, mirroring the complex variant in
   `Framework/Complex/Subst.lean`).
2. Prove the eval bridge `eval?_subst0`: term-level substitution
   matches environment-level shifting at index 0.
3. Define `id4 : EMLTerm` as `mkLog (mkExp (.var 0))` — the
   length-4 identity built from one `exp/log` pair. Verify
   `id4.depth = 4` and `id4` evaluates to `env 0` on **every** real
   environment (no positivity restriction needed).
4. Promote `id4` to the substitution combinator `transplant4`. The
   eval bridge `transplant4_eval` says: substituting an arbitrary
   sub-term `t` for `var 0` in the depth-4 identity preserves `t`'s
   evaluation. This is the formal version of "variables can be
   transplanted down the tree by 4 layers without changing semantics".
5. Iterate: `idMulFour k` is the identity of depth `4 * k`, given
   by `k` nested copies of the `mkLog ∘ mkExp` pair. Theorem
   `idMulFour_depth` and `idMulFour_eval` confirm this.

Structurally, this turns the paper's prose remark into a concrete
generative result: **for every multiple of 4, there is a literal EML
term of that depth that computes the identity function.**

The recommendation came from a 2026-05-10 GPT Pro consult; the bundle
lives at `gpt_pro_bundle/frontier_questions/`.
-/

namespace EML
namespace EMLTerm

/-! ## Tree depth -/

/-- Number of nested `eml` constructors on the longest root-to-leaf
path. Atoms have depth 0; `eml a b` has depth one greater than the
deeper child. -/
def depth : EMLTerm → Nat
  | .one     => 0
  | .var _   => 0
  | .eml a b => 1 + max a.depth b.depth

@[simp] lemma depth_one : (EMLTerm.one).depth = 0 := rfl
@[simp] lemma depth_var (n : Nat) : (EMLTerm.var n).depth = 0 := rfl
@[simp] lemma depth_eml (a b : EMLTerm) :
    (EMLTerm.eml a b).depth = 1 + max a.depth b.depth := rfl

/-! ## Variable-zero substitution

The real-fragment counterpart of `EMLTermℂ.subst0` from
`Framework/Complex/Subst.lean`. Replaces every `.var 0` with `s`,
leaves `.var (n+1)` untouched. -/

/-- Replace every `.var 0` in `t` with `s`. -/
def subst0 : EMLTerm → EMLTerm → EMLTerm
  | .one,       _ => .one
  | .var 0,     s => s
  | .var (n+1), _ => .var (n+1)
  | .eml a b,   s => .eml (a.subst0 s) (b.subst0 s)

@[simp] lemma subst0_one (s : EMLTerm) :
    (EMLTerm.one).subst0 s = .one := rfl

@[simp] lemma subst0_var_zero (s : EMLTerm) :
    (EMLTerm.var 0).subst0 s = s := rfl

@[simp] lemma subst0_var_succ (s : EMLTerm) (n : Nat) :
    (EMLTerm.var (n + 1)).subst0 s = .var (n + 1) := rfl

@[simp] lemma subst0_eml (s a b : EMLTerm) :
    (EMLTerm.eml a b).subst0 s = .eml (a.subst0 s) (b.subst0 s) := rfl

/-- The "shifted environment": replaces `env 0` with `s_val`, leaves
the rest unchanged. -/
def envShift0 (s_val : ℝ) (env : Nat → ℝ) : Nat → ℝ :=
  fun n => if n = 0 then s_val else env n

@[simp] lemma envShift0_zero (s_val : ℝ) (env : Nat → ℝ) :
    envShift0 s_val env 0 = s_val := by simp [envShift0]

@[simp] lemma envShift0_succ (s_val : ℝ) (env : Nat → ℝ) (n : Nat) :
    envShift0 s_val env (n + 1) = env (n + 1) := by simp [envShift0]

/-- **Substitution-environment correspondence.** Substituting `.var 0`
with `s` at the term level is equivalent to shifting the environment
at index 0 to `s.eval? env`. -/
lemma eval?_subst0 {env : Nat → ℝ} {s : EMLTerm} {s_val : ℝ}
    (hs : s.eval? env = some s_val)
    (t : EMLTerm) :
    (t.subst0 s).eval? env = t.eval? (envShift0 s_val env) := by
  induction t with
  | one => rfl
  | var n =>
    match n with
    | 0 =>
      rw [subst0_var_zero, hs]
      rw [EMLTerm.eval?_var, envShift0_zero]
    | n + 1 =>
      rw [subst0_var_succ]
      rw [EMLTerm.eval?_var, EMLTerm.eval?_var, envShift0_succ]
  | eml a b iha ihb =>
    rw [subst0_eml]
    unfold EMLTerm.eval?
    rw [iha, ihb]

/-! ## The depth-4 identity -/

/-- The depth-4 identity term `mkLog (mkExp (var 0))`.
Evaluates to `env 0` for every real environment, since
`log (exp x) = x` is unconditional in real partial semantics
(`exp x > 0` always, so `log` always fires). -/
def id4 : EMLTerm := mkLog (mkExp (.var 0))

/-- The identity term has depth exactly 4. Machine-checked by `rfl`. -/
theorem id4_depth : id4.depth = 4 := rfl

/-- The identity term evaluates to `env 0` for every real environment.
No positivity restriction on `env 0` — `mkExp` always succeeds (`1 > 0`),
and the resulting `exp (env 0) > 0` is what `mkLog` consumes. -/
theorem id4_eval (env : Nat → ℝ) :
    id4.eval? env = some (env 0) := by
  unfold id4
  -- mkExp (.var 0) evaluates to some (exp (env 0)).
  have h_exp : (mkExp (.var 0)).eval? env = some (Real.exp (env 0)) :=
    mkExp_eval? env _ (by simp)
  -- exp(env 0) > 0 always.
  have h_exp_pos : 0 < Real.exp (env 0) := Real.exp_pos _
  -- mkLog of a positive value gives log of that value.
  rw [mkLog_eval? env _ h_exp h_exp_pos, Real.log_exp]

/-! ## The transplant-4 combinator

Substituting an arbitrary term `t` for `.var 0` in the depth-4
identity preserves `t`'s evaluation. This is the formal version of
the SI's "transplanting variables down the tree by multiples of 4".
-/

/-- Build a depth-4 wrapper around `t` that evaluates the same as `t`. -/
def transplant4 (t : EMLTerm) : EMLTerm := id4.subst0 t

/-- The transplanted term has depth exactly 4 more than `t`'s depth. -/
theorem transplant4_depth (t : EMLTerm) :
    (transplant4 t).depth = t.depth + 4 := by
  -- Unfold the macros so the explicit tree shape is visible, then
  -- distribute `subst0` over each `eml` constructor (replacing the
  -- single `.var 0` leaf with `t`), and finally compute the depth.
  -- Linter complains some `depth_*` simp lemmas are unused, but
  -- removing them makes `omega` fail to close. Keep them.
  set_option linter.unusedSimpArgs false in
  unfold transplant4 id4 mkLog mkExp
  simp only [subst0_eml, subst0_one, subst0_var_zero,
             depth_eml, depth_one, depth_var]
  omega

/-- **Transplant-4 evaluation.** If `t` evaluates to `v`, then so does
`transplant4 t`. This is the SI #5 affirmative result: variable
positions can be replaced by arbitrary sub-terms, and the wrapping
depth-4 tree preserves the value. -/
theorem transplant4_eval {t : EMLTerm} {env : Nat → ℝ} {v : ℝ}
    (ht : t.eval? env = some v) :
    (transplant4 t).eval? env = some v := by
  unfold transplant4
  -- subst0 + eval?_subst0: evaluating the substituted term equals
  -- evaluating id4 in an env where `env 0` is replaced by `v`.
  rw [eval?_subst0 ht]
  -- id4 evaluates to whatever the modified env says at index 0, namely v.
  rw [id4_eval]
  simp [envShift0_zero]

/-! ## The depth-`4k` identity family

Iterating the `mkLog ∘ mkExp` pair gives identities of every depth
`4 * k`. We define the family recursively and prove its depth and
eval properties. -/

/-- `idMulFour k` is the identity term `(mkLog ∘ mkExp)^k applied to
.var 0` — depth `4 * k`, evaluates to `env 0` everywhere. -/
def idMulFour : Nat → EMLTerm
  | 0     => .var 0
  | k + 1 => mkLog (mkExp (idMulFour k))

@[simp] lemma idMulFour_zero : idMulFour 0 = .var 0 := rfl

lemma idMulFour_succ (k : Nat) :
    idMulFour (k + 1) = mkLog (mkExp (idMulFour k)) := rfl

/-- The iterated identity has depth exactly `4 * k`. -/
theorem idMulFour_depth (k : Nat) : (idMulFour k).depth = 4 * k := by
  induction k with
  | zero => simp [idMulFour]
  | succ k ih =>
    rw [idMulFour_succ]
    -- Each `mkLog ∘ mkExp` adds 4 to the depth.
    unfold mkLog mkExp
    simp only [depth_eml, depth_one]
    omega

/-- The iterated identity evaluates to `env 0` for every `k` and every
real environment. -/
theorem idMulFour_eval (k : Nat) (env : Nat → ℝ) :
    (idMulFour k).eval? env = some (env 0) := by
  induction k with
  | zero => simp [idMulFour]
  | succ k ih =>
    rw [idMulFour_succ]
    have h_exp : (mkExp (idMulFour k)).eval? env = some (Real.exp (env 0)) :=
      mkExp_eval? env _ ih
    have h_exp_pos : 0 < Real.exp (env 0) := Real.exp_pos _
    rw [mkLog_eval? env _ h_exp h_exp_pos, Real.log_exp]

/-- **SI §1.5 #5 — affirmative result for the multiples-of-4 case.**
For every `k : Nat`, there exists an `EMLTerm` of depth exactly `4 * k`
that evaluates to the identity function on every real environment. -/
theorem identity_terms_at_depth_multiples_of_four (k : Nat) :
    ∃ t : EMLTerm, t.depth = 4 * k ∧
      ∀ env : Nat → ℝ, t.eval? env = some (env 0) :=
  ⟨idMulFour k, idMulFour_depth k, idMulFour_eval k⟩

/-! ## Bounded-depth nonexistence companion

The affirmative result above shows identity terms exist at every depth
that is a multiple of 4. The natural converse asks whether identity
terms can exist at depths that are *not* multiples of 4 — in
particular at the smallest non-trivial depth, 1.

Here we prove the smallest such negative case: **no `EMLTerm` of depth
exactly 1 evaluates to the identity on every real environment.**
The argument is finite case analysis: an `EMLTerm` of depth 1 is
necessarily of the shape `eml a b` with both children atoms, and each
of the four leaf-atom shapes can be ruled out by exhibiting a single
counterexample environment.

Larger non-multiples of 4 (depths 2, 3, 5, 6, 7, …) remain paper-open
in our artefact; Pro flagged the depth-2 and depth-3 cases as bounded
finite-search problems that could be discharged similarly.
-/

/-- Helper: a term of depth 0 evaluated on the all-ones environment
returns `some 1`, regardless of whether the atom is `.one` or `.var n`. -/
private lemma eval_one_of_depth_zero {t : EMLTerm} (h : t.depth = 0) :
    t.eval? (fun _ : Nat => (1 : ℝ)) = some 1 := by
  cases t with
  | one => rfl
  | var _ => rfl
  | eml _ _ => simp [depth] at h

/-- Helper: a term of depth 1 evaluated on the all-ones environment
returns `some (Real.exp 1)` (i.e. `e`). -/
private lemma eval_one_of_depth_one {t : EMLTerm} (h : t.depth = 1) :
    t.eval? (fun _ : Nat => (1 : ℝ)) = some (Real.exp 1) := by
  match t with
  | .one => simp [depth] at h
  | .var _ => simp [depth] at h
  | .eml a b =>
    have ha : a.depth = 0 := by simp [depth] at h; omega
    have hb : b.depth = 0 := by simp [depth] at h; omega
    have ha_eval := eval_one_of_depth_zero ha
    have hb_eval := eval_one_of_depth_zero hb
    rw [EMLTerm.eval?_eml_of_pos ha_eval hb_eval zero_lt_one,
        Real.log_one, sub_zero]

/-- Helper: a term of depth 2 evaluated on the all-ones environment
returns one of three specific values: `e-1`, `exp e`, or `exp e - 1`. -/
private lemma eval_one_of_depth_two {t : EMLTerm} (h : t.depth = 2) :
    t.eval? (fun _ : Nat => (1 : ℝ)) = some (Real.exp 1 - 1) ∨
    t.eval? (fun _ : Nat => (1 : ℝ)) = some (Real.exp (Real.exp 1)) ∨
    t.eval? (fun _ : Nat => (1 : ℝ)) = some (Real.exp (Real.exp 1) - 1) := by
  match t with
  | .one => simp [depth] at h
  | .var _ => simp [depth] at h
  | .eml a b =>
    have hmax : max a.depth b.depth = 1 := by simp [depth] at h; omega
    have ha_le : a.depth ≤ 1 := le_of_max_le_left (le_of_eq hmax)
    have hb_le : b.depth ≤ 1 := le_of_max_le_right (le_of_eq hmax)
    have h_a0_or_a1 : a.depth = 0 ∨ a.depth = 1 := by omega
    have h_b0_or_b1 : b.depth = 0 ∨ b.depth = 1 := by omega
    let env : Nat → ℝ := fun _ => 1
    rcases h_a0_or_a1 with ha0 | ha1
    · rcases h_b0_or_b1 with hb0 | hb1
      · rw [ha0, hb0] at hmax; simp at hmax
      · -- (0, 1): eval = e - 1
        have ha_eval : a.eval? env = some 1 := eval_one_of_depth_zero ha0
        have hb_eval : b.eval? env = some (Real.exp 1) := eval_one_of_depth_one hb1
        left
        rw [show (EMLTerm.eml a b).eval? env = some (Real.exp 1 - Real.log (Real.exp 1))
              from EMLTerm.eval?_eml_of_pos ha_eval hb_eval (Real.exp_pos _),
            Real.log_exp]
    · rcases h_b0_or_b1 with hb0 | hb1
      · -- (1, 0): eval = exp e
        have ha_eval : a.eval? env = some (Real.exp 1) := eval_one_of_depth_one ha1
        have hb_eval : b.eval? env = some 1 := eval_one_of_depth_zero hb0
        right; left
        rw [EMLTerm.eval?_eml_of_pos ha_eval hb_eval zero_lt_one,
            Real.log_one, sub_zero]
      · -- (1, 1): eval = exp e - 1
        have ha_eval : a.eval? env = some (Real.exp 1) := eval_one_of_depth_one ha1
        have hb_eval : b.eval? env = some (Real.exp 1) := eval_one_of_depth_one hb1
        right; right
        rw [EMLTerm.eval?_eml_of_pos ha_eval hb_eval (Real.exp_pos _),
            Real.log_exp]

/-- **No identity term at depth 1.** No `EMLTerm` of depth exactly 1
evaluates to the identity on every real environment. -/
theorem no_identity_at_depth_one :
    ¬ ∃ t : EMLTerm, t.depth = 1 ∧
      ∀ env : Nat → ℝ, t.eval? env = some (env 0) := by
  rintro ⟨t, hd, hev⟩
  -- A depth-1 term is `eml a b` with both children atomic. The
  -- key fact: on the all-ones environment, every depth-0 child
  -- evaluates to `some 1` (whether it's `.one` or `.var n`), so
  -- `eml a b` evaluates to `some (exp 1 - log 1) = some e`.
  -- The identity hypothesis demands `some 1`. But `e ≠ 1`.
  match t with
  | .one => simp [depth] at hd
  | .var _ => simp [depth] at hd
  | .eml a b =>
    have ha : a.depth = 0 := by
      simp [depth] at hd; omega
    have hb : b.depth = 0 := by
      simp [depth] at hd; omega
    let env : Nat → ℝ := fun _ => 1
    have ha_eval : a.eval? env = some 1 := eval_one_of_depth_zero ha
    have hb_eval : b.eval? env = some 1 := eval_one_of_depth_zero hb
    have h_eval : (EMLTerm.eml a b).eval? env = some (Real.exp 1) := by
      rw [EMLTerm.eval?_eml_of_pos ha_eval hb_eval zero_lt_one,
          Real.log_one, sub_zero]
    have h_id : (EMLTerm.eml a b).eval? env = some 1 := hev env
    -- Combining: some (exp 1) = some 1, so exp 1 = 1. But exp 1 ≥ 2.
    rw [h_eval] at h_id
    have h_eq : Real.exp 1 = 1 := Option.some.inj h_id
    have h_ge : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    linarith

/-- **No identity term at depth 2.** No `EMLTerm` of depth exactly 2
evaluates to the identity on every real environment.

Proof strategy: a depth-2 term is `eml a b` with
`max(a.depth, b.depth) = 1`. On the all-ones environment, depth-0
children evaluate to `1` and depth-1 children to `e`. The three
non-trivial sub-cases give eval values `e - 1`, `e^e`, and `e^e - 1`
respectively. Each is bounded away from `1` using `exp 1 ≥ 2` and
`Real.add_one_le_exp`. -/
theorem no_identity_at_depth_two :
    ¬ ∃ t : EMLTerm, t.depth = 2 ∧
      ∀ env : Nat → ℝ, t.eval? env = some (env 0) := by
  rintro ⟨t, hd, hev⟩
  match t with
  | .one => simp [depth] at hd
  | .var _ => simp [depth] at hd
  | .eml a b =>
    have hmax : max a.depth b.depth = 1 := by simp [depth] at hd; omega
    have ha_le : a.depth ≤ 1 := le_of_max_le_left (le_of_eq hmax)
    have hb_le : b.depth ≤ 1 := le_of_max_le_right (le_of_eq hmax)
    let env : Nat → ℝ := fun _ => 1
    have h_id : (EMLTerm.eml a b).eval? env = some 1 := hev env
    -- exp 1 > 2 (strict; needed to rule out exp 1 = 2 in the (0,1) case).
    have h_e_gt_two : (2 : ℝ) < Real.exp 1 := by
      have := Real.add_one_lt_exp (one_ne_zero); linarith
    -- exp(exp 1) > exp 1 + 1 > 3.
    have h_ee_gt_three : (3 : ℝ) < Real.exp (Real.exp 1) := by
      have h1 := Real.add_one_lt_exp (Real.exp_pos 1).ne'; linarith
    -- Case split on (a.depth, b.depth).
    have h_a0_or_a1 : a.depth = 0 ∨ a.depth = 1 := by omega
    have h_b0_or_b1 : b.depth = 0 ∨ b.depth = 1 := by omega
    -- (0, 0) is incompatible with max = 1.
    rcases h_a0_or_a1 with ha0 | ha1
    · rcases h_b0_or_b1 with hb0 | hb1
      · -- (a.depth = 0, b.depth = 0): max = 0 ≠ 1, contradiction.
        rw [ha0, hb0] at hmax; simp at hmax
      · -- (a.depth = 0, b.depth = 1): eval = exp 1 - log (exp 1) = e - 1.
        have ha_eval : a.eval? env = some 1 := eval_one_of_depth_zero ha0
        have hb_eval : b.eval? env = some (Real.exp 1) :=
          eval_one_of_depth_one hb1
        rw [EMLTerm.eval?_eml_of_pos ha_eval hb_eval (Real.exp_pos _),
            Real.log_exp] at h_id
        have h_eq : Real.exp 1 - 1 = 1 := Option.some.inj h_id
        linarith
    · rcases h_b0_or_b1 with hb0 | hb1
      · -- (a.depth = 1, b.depth = 0): eval = exp(exp 1) - log 1 = e^e.
        have ha_eval : a.eval? env = some (Real.exp 1) :=
          eval_one_of_depth_one ha1
        have hb_eval : b.eval? env = some 1 := eval_one_of_depth_zero hb0
        rw [EMLTerm.eval?_eml_of_pos ha_eval hb_eval zero_lt_one,
            Real.log_one, sub_zero] at h_id
        have h_eq : Real.exp (Real.exp 1) = 1 := Option.some.inj h_id
        linarith
      · -- (a.depth = 1, b.depth = 1): eval = exp(exp 1) - log(exp 1) = e^e - 1.
        have ha_eval : a.eval? env = some (Real.exp 1) :=
          eval_one_of_depth_one ha1
        have hb_eval : b.eval? env = some (Real.exp 1) :=
          eval_one_of_depth_one hb1
        rw [EMLTerm.eval?_eml_of_pos ha_eval hb_eval (Real.exp_pos _),
            Real.log_exp] at h_id
        have h_eq : Real.exp (Real.exp 1) - 1 = 1 := Option.some.inj h_id
        linarith

end EMLTerm
end EML
