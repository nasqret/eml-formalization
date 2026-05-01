namespace EML

/-- Constant-only EML term grammar from §4.2:
    `S → 1 | eml(S, S)`. -/
inductive EMLTerm : Type
  | one : EMLTerm
  | eml : EMLTerm → EMLTerm → EMLTerm
  deriving Repr

end EML
