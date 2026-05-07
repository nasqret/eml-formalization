import EML.Framework.EMLPartial
import EML.Framework.Complex.Term

/-!
# Real-to-complex term lift

`EMLTerm.toComplex : EMLTerm → EMLTermℂ` syntactically embeds the real EML
grammar into the complex grammar (same constructor shape). Together with
`EMLTerm.eval?_toComplex_of_real`, this lets arcsin/arccos/tan witnesses
reuse the sealed real `sqrt`/`pow`/etc. compositions from
`EML.Framework.Compilers.ELToEML` instead of inventing brittle complex
analogues.

Phase B++ II §A architectural cleanup, per GPT Pro's review.
-/

namespace EML

/-- Homomorphic embedding of real EML syntax into complex EML syntax. -/
def EMLTerm.toComplex : EMLTerm → EMLTermℂ
  | .one     => .one
  | .var n   => .var n
  | .eml a b => .eml a.toComplex b.toComplex

/-- Bridge: a real partial-eval result lifts to a complex partial-eval
result over the canonical real-cast environment.

If `t.eval? env = some v` with the real semantics (which requires
`0 < vb` at every nested `eml(_, b)`), then the lifted term evaluates
to `((v : ℝ) : ℂ)` — note the strict-positive ⇒ nonzero direction in
the precondition cascade. -/
lemma EMLTerm.eval?_toComplex_of_real
    {t : EMLTerm} {env : Nat → ℝ} {v : ℝ}
    (h : t.eval? env = some v) :
    t.toComplex.eval? (fun n => ((env n : ℝ) : ℂ)) = some ((v : ℝ) : ℂ) := by
  induction t generalizing v with
  | one =>
      simp [EMLTerm.eval?] at h
      subst h
      simp [EMLTerm.toComplex]
  | var n =>
      simp [EMLTerm.eval?] at h
      subst h
      simp [EMLTerm.toComplex]
  | eml a b iha ihb =>
      unfold EMLTerm.eval? at h
      cases ha : a.eval? env with
      | none => rw [ha] at h; simp at h
      | some va =>
          cases hb : b.eval? env with
          | none => rw [ha, hb] at h; simp at h
          | some vb =>
              rw [ha, hb] at h
              simp only at h
              by_cases hpos : 0 < vb
              · rw [if_pos hpos] at h
                have hca := iha ha
                have hcb := ihb hb
                have hne : ((vb : ℝ) : ℂ) ≠ 0 := by
                  exact_mod_cast hpos.ne'
                have hc :=
                  EMLTermℂ.eval?_eml_of_ne hca hcb hne
                show (EMLTermℂ.eml a.toComplex b.toComplex).eval? _ = _
                rw [hc]
                congr 1
                have hv : v = Real.exp va - Real.log vb :=
                  (Option.some.inj h).symm
                rw [hv, Complex.ofReal_sub, Complex.ofReal_exp,
                    ← Complex.ofReal_log hpos.le]
              · rw [if_neg hpos] at h; cases h

end EML
