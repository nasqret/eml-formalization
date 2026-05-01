import Mathlib

namespace EML

inductive EMLTerm : Type
  | one : EMLTerm
  | eml : EMLTerm → EMLTerm → EMLTerm
  deriving Repr

def EMLTerm.size : EMLTerm → ℕ
  | .one => 1
  | .eml t u => 1 + EMLTerm.size t + EMLTerm.size u

theorem EMLTerm.size_pos (t : EMLTerm) : 1 ≤ EMLTerm.size t := by
  induction' t using EMLTerm.recOn with t ih <;> norm_num [ EMLTerm.size ];
  grind

end EML
