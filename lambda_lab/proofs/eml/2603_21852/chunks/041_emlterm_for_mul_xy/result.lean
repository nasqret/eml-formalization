import Mathlib

namespace EML

inductive EMLTerm₂ : Type
  | one : EMLTerm₂
  | varX : EMLTerm₂
  | varY : EMLTerm₂
  | eml : EMLTerm₂ → EMLTerm₂ → EMLTerm₂
  deriving Repr

noncomputable def EMLTerm₂.eval (x y : ℝ) : EMLTerm₂ → ℝ
  | .one => 1
  | .varX => x
  | .varY => y
  | .eml t u => Real.exp (EMLTerm₂.eval x y t) - Real.log (EMLTerm₂.eval x y u)

/-
For x > 0, x - log x > 0
-/
lemma sub_log_pos {x : ℝ} (hx : 0 < x) : 0 < x - Real.log x := by
  linarith [ Real.log_le_sub_one_of_pos hx ]

theorem emlterm2_for_mul :
    ∃ t : EMLTerm₂, ∀ x y : ℝ, 0 < x → 0 < y → EMLTerm₂.eval x y t = x * y := by
  refine ⟨?_, fun x y hx hy => ?_⟩
  · exact .eml (.eml (.eml .one (.eml (.eml .one .varX) .one))
      (.eml (.eml (.eml .one (.eml (.eml .one
        (.eml (.eml .one (.eml (.eml .one .varX) .one))
          (.eml (.eml .one (.eml (.eml .one .varX) .one)) .one))) .one)) .varY) .one)) .one
  · simp only [EMLTerm₂.eval, Real.log_one, sub_zero, Real.log_exp]
    -- Goal has e - (e - log x) patterns where e = exp 1
    set e := Real.exp 1
    -- Step 1: simplify e - (e - log x) to log x
    have h1 : e - (e - Real.log x) = Real.log x := by ring
    rw [h1]
    -- Step 2: exp(log x) = x
    rw [Real.exp_log hx]
    -- Step 3: simplify e - (e - log(x - log x)) to log(x - log x)
    have h3 : e - (e - Real.log (x - Real.log x)) = Real.log (x - Real.log x) := by ring
    rw [h3]
    -- Step 4: exp(log(x - log x)) = x - log x
    rw [Real.exp_log (sub_log_pos hx)]
    -- Step 5 & 6: exp(x - (x - log x - log y)) = exp(log x + log y) = x * y
    have h5 : x - (x - Real.log x - Real.log y) = Real.log x + Real.log y := by ring
    rw [h5, Real.exp_add, Real.exp_log hx, Real.exp_log hy]

end EML
