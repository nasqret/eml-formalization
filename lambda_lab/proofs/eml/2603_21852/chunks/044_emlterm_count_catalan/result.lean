import Mathlib

namespace EML

inductive EMLTerm : Type
  | one : EMLTerm
  | eml : EMLTerm → EMLTerm → EMLTerm
  deriving Repr, DecidableEq

def EMLTerm.size : EMLTerm → ℕ
  | .one => 1
  | .eml t u => 1 + EMLTerm.size t + EMLTerm.size u

lemma EMLTerm.size_odd : ∀ t : EMLTerm, ∃ k, t.size = 2 * k + 1
  | .one => ⟨0, by simp [EMLTerm.size]⟩
  | .eml a b => by
    obtain ⟨i, hi⟩ := EMLTerm.size_odd a
    obtain ⟨j, hj⟩ := EMLTerm.size_odd b
    exact ⟨i + j + 1, by simp only [EMLTerm.size, hi, hj]; omega⟩

lemma EMLTerm.size_pos : ∀ t : EMLTerm, 0 < t.size
  | .one => by simp [EMLTerm.size]
  | .eml a b => by simp [EMLTerm.size]

def termsOfInternalNodes : ℕ → Finset EMLTerm
  | 0 => {.one}
  | k + 1 =>
    ((Finset.range (k + 1)).attach).biUnion fun ⟨i, hi⟩ =>
      have h1 : i < k + 1 := Finset.mem_range.mp hi
      have h2 : k - i < k + 1 := by omega
      ((termsOfInternalNodes i) ×ˢ (termsOfInternalNodes (k - i))).image
        fun p => EMLTerm.eml p.1 p.2
termination_by k => k
decreasing_by all_goals omega

@[simp] lemma termsOfInternalNodes_zero : termsOfInternalNodes 0 = {.one} := by
  simp [termsOfInternalNodes]

lemma size_eq_of_mem_termsOfInternalNodes (k : ℕ) (t : EMLTerm)
    (ht : t ∈ termsOfInternalNodes k) : EMLTerm.size t = 2 * k + 1 := by
  induction' k using Nat.strong_induction_on with k ih generalizing t
  unfold termsOfInternalNodes at ht
  rcases k with ( _ | k ) <;> simp_all +decide
  rcases ht with ⟨ a, ha, b, c, ⟨ hb, hc ⟩, rfl ⟩
  simp +arith +decide [ *, EMLTerm.size ]
  grind

lemma mem_termsOfInternalNodes_of_size (k : ℕ) (t : EMLTerm)
    (ht : t.size = 2 * k + 1) : t ∈ termsOfInternalNodes k := by
  induction' k using Nat.strong_induction_on with k ih generalizing t
  rcases k with ( _ | k ) <;> simp_all +decide
  · cases t
    · rfl
    · exact absurd ht (by erw [show (_ : EMLTerm).size = 1 + (_ : EMLTerm).size + (_ : EMLTerm).size from rfl]; linarith [EMLTerm.size_pos ‹_›, EMLTerm.size_pos ‹_›])
  · rcases t with ( _ | ⟨ a, b ⟩ )
    · cases ht
    · obtain ⟨i, hi⟩ : ∃ i, i ≤ k ∧ a.size = 2 * i + 1 ∧ b.size = 2 * (k - i) + 1 := by
        obtain ⟨ i, hi ⟩ := EMLTerm.size_odd a
        obtain ⟨ j, hj ⟩ := EMLTerm.size_odd b
        use i
        simp_all +decide [ EMLTerm.size ]
        omega
      unfold termsOfInternalNodes; aesop

/-
Helper: eml is injective as a function on pairs
-/
lemma eml_pair_injective : Function.Injective (fun p : EMLTerm × EMLTerm => EMLTerm.eml p.1 p.2) := by
  -- To prove injectivity, assume that eml p1 p2 = eml q1 q2. By the definition of eml, this implies that p1 = q1 and p2 = q2.
  intro p1 p2 h_eq
  simp [EMLTerm.eml] at h_eq
  aesop

/-
Helper: the image of eml on a product has card = card A * card B
-/
lemma card_eml_image (A B : Finset EMLTerm) :
    ((A ×ˢ B).image fun p => EMLTerm.eml p.1 p.2).card = A.card * B.card := by
  rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective, eml_pair_injective ]

/-
Helper: disjointness of images for different i
-/
lemma eml_images_pairwise_disjoint (k : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.range (k + 1)).attach)
      (fun (x : { x // x ∈ Finset.range (k + 1) }) =>
        ((termsOfInternalNodes x.1) ×ˢ (termsOfInternalNodes (k - x.1))).image
          fun p => EMLTerm.eml p.1 p.2) := by
  intro x hx y hy hxy; simp_all +decide [ Finset.disjoint_left ] ;
  rintro a u v hu hv rfl w z hw hz; contrapose! hxy;
  have := size_eq_of_mem_termsOfInternalNodes x.val u hu; have := size_eq_of_mem_termsOfInternalNodes y.val w hw; aesop;

/-
The cardinality proof using the helpers
-/
lemma card_termsOfInternalNodes (k : ℕ) :
    (termsOfInternalNodes k).card = catalan k := by
  induction' k using Nat.case_strong_induction_on with k ih;
  · -- The base case when $k = 0$ follows directly from the definition of `termsOfInternalNodes`.
    simp [termsOfInternalNodes];
  · have h_card : (termsOfInternalNodes (k + 1)).card = ∑ i ∈ Finset.range (k + 1), (termsOfInternalNodes i).card * (termsOfInternalNodes (k - i)).card := by
      rw [ termsOfInternalNodes, Finset.card_biUnion ];
      · refine' Finset.sum_bij ( fun x hx => x.val ) _ _ _ _ <;> simp +decide [ card_eml_image ];
      · convert eml_images_pairwise_disjoint k using 1;
    simp_all +decide [ catalan_succ' ];
    rw [ Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun i j => catalan i * catalan j ];
    exact Finset.sum_congr rfl fun x hx => by rw [ ih x ( Finset.mem_range_succ_iff.mp hx ) ] ;

/-- Number of EML terms of size `2k + 1` equals the Catalan number `Cₖ`. -/
theorem emlterm_count_catalan (k : ℕ) :
    ∃ (S : Finset EMLTerm), (∀ t ∈ S, EMLTerm.size t = 2 * k + 1) ∧
      (∀ t : EMLTerm, EMLTerm.size t = 2 * k + 1 → t ∈ S) ∧
      S.card = catalan k :=
  ⟨termsOfInternalNodes k,
    fun t ht => size_eq_of_mem_termsOfInternalNodes k t ht,
    fun t ht => mem_termsOfInternalNodes_of_size k t ht,
    card_termsOfInternalNodes k⟩

end EML
