namespace EML

inductive EMLTerm : Type
  | one : EMLTerm
  | eml : EMLTerm → EMLTerm → EMLTerm
  deriving Repr

/-- Number of nodes in an EML term. -/
def EMLTerm.size : EMLTerm → ℕ
  | .one => 1
  | .eml t u => 1 + EMLTerm.size t + EMLTerm.size u

end EML
