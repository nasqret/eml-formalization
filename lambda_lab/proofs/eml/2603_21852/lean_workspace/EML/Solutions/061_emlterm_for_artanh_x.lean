import Mathlib

namespace EML

inductive EMLTerm₁ : Type
  | one : EMLTerm₁
  | var : EMLTerm₁
  | eml : EMLTerm₁ → EMLTerm₁ → EMLTerm₁
  deriving Repr

noncomputable def EMLTerm₁.eval (x : ℝ) : EMLTerm₁ → ℝ
  | .one      => 1
  | .var      => x
  | .eml t u  => Real.exp (EMLTerm₁.eval x t) - Real.log (EMLTerm₁.eval x u)

/-! ## Helper constructors

These follow the paper's canonical Identity 4 (`exp z = eml(z, 1)`) and
Identity 5 (`log z = eml(1, eml(eml(1, z), 1))`). No `Real.log 0 = 0`
junk value is used: every `eml(_, y)` subterm has `y > 0` on the
artanh domain `|x| < 1`.

The earlier version of this chunk routed `expT` and `logT` through a
constant-`0` term `zT` and relied on Lean's total `Real.log 0 = 0` junk
value. That made the witness valid only under Lean's totalised `Real.log`
semantics, not under the paper's partial / extended-real convention
where `ln(0) = -∞`. The canonical forms below are paper-faithful.
-/

def expT (t : EMLTerm₁) : EMLTerm₁ := .eml t .one
def logT (t : EMLTerm₁) : EMLTerm₁ := .eml .one (.eml (.eml .one t) .one)
def subT (a b : EMLTerm₁) : EMLTerm₁ := .eml (logT a) (expT b)

/-! ## Witness sub-terms -/

def omxT : EMLTerm₁ := subT .one .var
def nxT  : EMLTerm₁ := subT omxT .one
def opxT : EMLTerm₁ := subT .one nxT
def fT   : EMLTerm₁ := .eml .one omxT
def gT   : EMLTerm₁ := .eml .one opxT
def emoT : EMLTerm₁ := .eml .one (.eml .one .one)
def emtT : EMLTerm₁ := subT emoT .one
def twoT : EMLTerm₁ := .eml .one (expT emtT)
def fHalfT : EMLTerm₁ := expT (subT (logT fT) (logT twoT))
def gHalfT : EMLTerm₁ := expT (subT (logT gT) (logT twoT))
def artanhT : EMLTerm₁ := subT fHalfT gHalfT

/-! ## Evaluation lemmas -/

lemma eval_expT (t : EMLTerm₁) (x : ℝ) :
    (expT t).eval x = Real.exp (t.eval x) := by
  -- expT t = .eml t .one; eval = exp(t) - log(1) = exp(t).
  show Real.exp (t.eval x) - Real.log 1 = Real.exp (t.eval x)
  rw [Real.log_one, sub_zero]

lemma eval_logT (t : EMLTerm₁) (x : ℝ) :
    (logT t).eval x = Real.log (t.eval x) := by
  -- logT t = .eml .one (.eml (.eml .one t) .one)
  -- inner   = .eml .one t           ↦ exp 1 - log(t.eval x)                  = e - log t
  -- middle  = .eml (.eml .one t) .one ↦ exp(e - log t) - log 1 = exp(e - log t)
  -- outer   = .eml .one middle      ↦ exp 1 - log(exp(e - log t)) = e - (e - log t) = log t
  show Real.exp 1
        - Real.log (Real.exp (Real.exp 1 - Real.log (t.eval x)) - Real.log 1)
      = Real.log (t.eval x)
  rw [Real.log_one, sub_zero, Real.log_exp]; ring

lemma eval_subT (a b : EMLTerm₁) (x : ℝ) (ha : 0 < a.eval x) :
    (subT a b).eval x = a.eval x - b.eval x := by
  -- subT a b = .eml (logT a) (expT b); eval = exp(log a) - log(exp b) = a - b.
  show Real.exp ((logT a).eval x) - Real.log ((expT b).eval x) = a.eval x - b.eval x
  rw [eval_logT, eval_expT, Real.exp_log ha, Real.log_exp]

lemma eval_omxT (x : ℝ) : omxT.eval x = 1 - x := by
  convert eval_subT .one .var x _;
  exact zero_lt_one

lemma eval_nxT (x : ℝ) (hx : x < 1) : nxT.eval x = -x := by
  rw [ show nxT = subT omxT .one from rfl, eval_subT ] <;> norm_num [ hx, eval_omxT ];
  erw [ show EMLTerm₁.eval x EMLTerm₁.one = 1 from rfl ] ; ring

lemma eval_opxT (x : ℝ) (hx : x < 1) : opxT.eval x = 1 + x := by
  -- Use the fact that $opxT = subT .one nxT$.
  have h_opxT : EMLTerm₁.eval x opxT = 1 - EMLTerm₁.eval x nxT := by
    apply eval_subT;
    exact zero_lt_one;
  linarith [ eval_nxT x hx ]

lemma eval_fT (x : ℝ) : fT.eval x = Real.exp 1 - Real.log (1 - x) := by
  rw [ ← eval_omxT ];
  rfl

lemma eval_gT (x : ℝ) (_hx1 : -1 < x) (hx2 : x < 1) :
    gT.eval x = Real.exp 1 - Real.log (1 + x) := by
  -- By definition of `gT`, we have `gT.eval x = EMLTerm₁.eval x (.eml .one opxT)`.
  simp [EMLTerm₁.eval, gT];
  rw [ eval_opxT x hx2 ]

lemma eval_emoT (x : ℝ) : emoT.eval x = Real.exp 1 - 1 := by
  simp [emoT, EMLTerm₁.eval]

lemma eval_emtT (x : ℝ) : emtT.eval x = Real.exp 1 - 2 := by
  rw [ show EMLTerm₁.eval x emtT = ( EMLTerm₁.eval x emoT ) - ( EMLTerm₁.eval x .one ) from ?_ ];
  · rw [ show emoT = .eml .one (.eml .one .one) from rfl ] ; norm_num [ EMLTerm₁.eval ] ; ring;
  · apply eval_subT;
    exact eval_emoT x ▸ sub_pos.mpr ( by norm_num )

lemma eval_twoT (x : ℝ) : twoT.eval x = 2 := by
  have h_eval_twoT : twoT.eval x = Real.exp 1 - Real.log (Real.exp (Real.exp 1 - 2)) := by
    have h_eval_twoT : twoT.eval x = Real.exp 1 - Real.log ((expT emtT).eval x) := by
      rfl;
    rw [ h_eval_twoT ];
    rw [ eval_expT, eval_emtT ];
  rw [ h_eval_twoT, Real.log_exp, sub_sub_cancel ]

/-! ## Bounds lemmas -/

lemma fT_gt_one (x : ℝ) (hx1 : -1 < x) (hx2 : x < 1) : 1 < fT.eval x := by
  -- By definition of $fT$, we have $fT.eval x = exp(1) - log(1-x)$.
  have h_fT_eval : fT.eval x = Real.exp 1 - Real.log (1 - x) := by
    exact eval_fT x;
  exact h_fT_eval ▸ by have := Real.exp_one_gt_d9.le; norm_num1 at *; linarith [ Real.log_le_sub_one_of_pos ( by linarith : 0 < 1 - x ) ] ;

lemma gT_gt_one (x : ℝ) (hx1 : -1 < x) (hx2 : x < 1) : 1 < gT.eval x := by
  -- Since $x \in (-1, 1)$, we have $0 < 1 + x < 2$, thus $\log(1 + x) < \log(2) < 1$.
  have h_log_bound : Real.log (1 + x) < 1 := by
    exact lt_of_le_of_lt ( Real.log_le_sub_one_of_pos ( by linarith ) ) ( by linarith );
  rw [ eval_gT x hx1 hx2 ] ; linarith [ Real.add_one_le_exp 1 ]

/-! ## Higher-level evaluation lemmas -/

lemma eval_fHalfT (x : ℝ) (hx1 : -1 < x) (hx2 : x < 1) :
    fHalfT.eval x = (Real.exp 1 - Real.log (1 - x)) / 2 := by
  convert eval_expT ( subT ( logT fT ) ( logT twoT ) ) x using 1;
  rw [ eval_subT, eval_logT, eval_logT ];
  · rw [ Real.exp_sub, Real.exp_log, Real.exp_log ];
    · rw [ eval_fT, eval_twoT ];
    · exact eval_twoT x ▸ by norm_num;
    · exact lt_trans zero_lt_one ( fT_gt_one x hx1 hx2 );
  · rw [ eval_logT ];
    exact Real.log_pos ( fT_gt_one x hx1 hx2 )

lemma eval_gHalfT (x : ℝ) (hx1 : -1 < x) (hx2 : x < 1) :
    gHalfT.eval x = (Real.exp 1 - Real.log (1 + x)) / 2 := by
  -- Use the definition of gHalfT to rewrite it in terms of logT and expT.
  unfold gHalfT;
  rw [ eval_expT, eval_subT ];
  · rw [ eval_logT, eval_logT, Real.exp_sub ];
    rw [ Real.exp_log, Real.exp_log, eval_gT ];
    · rw [ eval_twoT ];
    · linarith;
    · linarith;
    · exact eval_twoT x ▸ by norm_num;
    · exact lt_trans zero_lt_one ( gT_gt_one x hx1 hx2 );
  · rw [ eval_logT ];
    exact Real.log_pos ( gT_gt_one x hx1 hx2 )

lemma fHalfT_pos (x : ℝ) (hx1 : -1 < x) (hx2 : x < 1) :
    0 < fHalfT.eval x := by
  rw [ eval_fHalfT ] <;> try linarith [ fT_gt_one x hx1 hx2 ];
  exact div_pos ( sub_pos_of_lt ( lt_of_le_of_lt ( Real.log_le_sub_one_of_pos ( by linarith ) ) ( by linarith [ Real.add_one_le_exp 1 ] ) ) ) zero_lt_two

lemma eval_artanhT (x : ℝ) (hx1 : -1 < x) (hx2 : x < 1) :
    artanhT.eval x = (Real.log (1 + x) - Real.log (1 - x)) / 2 := by
  -- Apply the definition of subT to expand artanhT.
  have h_expand : EMLTerm₁.eval x artanhT = EMLTerm₁.eval x fHalfT - EMLTerm₁.eval x gHalfT := by
    apply eval_subT;
    exact fHalfT_pos x hx1 hx2
  rw [ h_expand, eval_fHalfT x hx1 hx2, eval_gHalfT x hx1 hx2 ] ; ring

/-! ## The artanh identity -/

lemma artanh_eq_half_log_diff (x : ℝ) (hx1 : -1 < x) (hx2 : x < 1) :
    Real.artanh x = (Real.log (1 + x) - Real.log (1 - x)) / 2 := by
  unfold Real.artanh;
  rw [ Real.log_sqrt ( div_nonneg ( by linarith ) ( by linarith ) ), Real.log_div ] <;> linarith

/-
Recipe (Table S2, step 30 — `artanh(x)`, K=5):
    artanh(x) = arsinh(1 / tan(arccos x))   (paper, complex chain)
              = (1/2) · ln((1 + x) / (1 - x))   (textbook real form)

Witness composes chunk 053 (log_x), chunk 052 (half), and the
arithmetic chunks 040/050. Domain: `|x| < 1`.
-/
theorem emlterm1_for_artanh :
    ∃ t : EMLTerm₁, ∀ x : ℝ, -1 < x → x < 1 →
      EMLTerm₁.eval x t = Real.artanh x := by
  exact ⟨artanhT, fun x hx1 hx2 => by
    rw [eval_artanhT x hx1 hx2, artanh_eq_half_log_diff x hx1 hx2]⟩

end EML
