import Mathlib

namespace EML

inductive EMLTerm : Type
  | one : EMLTerm
  | eml : EMLTerm → EMLTerm → EMLTerm
  deriving Repr

noncomputable def EMLTerm.eval : EMLTerm → ℝ
  | .one => 1
  | .eml t u => Real.exp (EMLTerm.eval t) - Real.log (EMLTerm.eval u)

theorem emlterm_for_neg_one : ∃ t : EMLTerm, EMLTerm.eval t = -1 := by
  -- Let's choose the term $t = .eml (.eml .one (.eml (.eml .one (.eml .one (.eml .one .one))) .one)) (.eml (.eml .one .one) .one)$.
  use .eml (.eml .one (.eml (.eml .one (.eml .one (.eml .one .one))) .one)) (.eml (.eml .one .one) .one);
  -- Let's simplify the expression step by step.
  simp [EMLTerm.eval];
  rw [ Real.exp_log ] <;> linarith [ Real.add_one_le_exp 1 ]

end EML
