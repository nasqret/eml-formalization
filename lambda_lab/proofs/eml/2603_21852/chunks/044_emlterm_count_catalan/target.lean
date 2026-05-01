import Mathlib.Combinatorics.Catalan

namespace EML

inductive EMLTerm : Type
  | one : EMLTerm
  | eml : EMLTerm → EMLTerm → EMLTerm
  deriving Repr

def EMLTerm.size : EMLTerm → ℕ
  | .one => 1
  | .eml t u => 1 + EMLTerm.size t + EMLTerm.size u

/-- Number of EML terms of size `2k + 1` equals the Catalan number `Cₖ`.
The set of EMLTerms of bounded size is finite; we phrase the count via
a finset cardinality (Fintype instance left as `sorry` machinery). -/
theorem emlterm_count_catalan (k : ℕ) :
    ∃ (S : Finset EMLTerm), (∀ t ∈ S, EMLTerm.size t = 2 * k + 1) ∧
      (∀ t : EMLTerm, EMLTerm.size t = 2 * k + 1 → t ∈ S) ∧
      S.card = Nat.catalan k := by
  sorry

end EML
