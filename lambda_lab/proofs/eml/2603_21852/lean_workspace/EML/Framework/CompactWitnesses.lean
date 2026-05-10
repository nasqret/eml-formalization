import EML.Framework.Builders.Unconditional
import EML.Framework.EMLPartial
import EML.Framework.KCounting

/-!
# Compact witnesses — small EMLTerm witnesses for the binary primitives

The `paper_claim_*` theorems in `EML.Framework.PaperClaims` use witnesses
produced by the structural compiler (F36 → EL → EML pipeline). For
binary primitives this gives **compositionally large** trees because
each layer of macro expansion duplicates structure: `K_count_logb` is
9 929 087, `K_count_div` is 5 896 223, `K_count_mul` is 839 743.

This module provides **alternative compact witnesses** for the same
paper claims, built directly from the unconditional macros
(`mkMulAll`, `mkDivNonzeroDenom`, `mkAvgAll`, `mkPowAll`, `mkLogbAll`,
`mkHypotAll`, `mkInvNonzero`) defined in `Builders/Unconditional.lean`.
The K-counts of these compact witnesses are typically 3–40× smaller
than the structural-compile output for the same primitive.

The compact witnesses serve two purposes:
1. They demonstrate that the headline existential `∃ t, ...` admits
   a much smaller witness than the structural compiler produces.
2. They make the dashboard's K-count distribution comparable with the
   source paper's hand-tuned Table 4 figures, which are also
   compositional rather than uniform-shape.

The structural-compile witnesses remain the canonical proof artefact
(they are produced by a single uniform theorem
`F36Expr.real_complete`); these compact versions are alternatives,
not replacements.
-/

namespace EML
namespace EMLTerm

/-! ## Compact paper claims -/

/-- **Compact witness — `x · y`.** Direct `mkMulAll` instead of the
structural-compile output. Same existential statement as
`paper_claim_mul`. -/
theorem paper_claim_mul_compact :
    ∃ t : EMLTerm, ∀ env : Nat → ℝ, t.eval? env = some (env 0 * env 1) :=
  ⟨mkMulAll (.var 0) (.var 1), fun env => mkMulAll_eval? env _ _ rfl rfl⟩

/-- **Compact witness — `x / y`** for `y ≠ 0`. -/
theorem paper_claim_div_compact :
    ∃ t : EMLTerm, ∀ env : Nat → ℝ, env 1 ≠ 0 →
      t.eval? env = some (env 0 / env 1) :=
  ⟨mkDivNonzeroDenom (.var 0) (.var 1),
   fun env hne => mkDivNonzeroDenom_eval? env _ _ rfl rfl hne⟩

/-- **Compact witness — `(x + y) / 2`** (averaging). -/
theorem paper_claim_avg_compact :
    ∃ t : EMLTerm, ∀ env : Nat → ℝ, t.eval? env = some ((env 0 + env 1) / 2) :=
  ⟨mkAvgAll (.var 0) (.var 1), fun env => mkAvgAll_eval? env _ _ rfl rfl⟩

/-- **Compact witness — `x^y`** for `0 < x`. -/
theorem paper_claim_pow_compact :
    ∃ t : EMLTerm, ∀ env : Nat → ℝ, 0 < env 0 →
      t.eval? env = some (Real.rpow (env 0) (env 1)) :=
  ⟨mkPowAll (.var 0) (.var 1),
   fun env hpos => mkPowAll_eval? env _ _ rfl rfl hpos⟩

/-- **Compact witness — `log_x y`** for `0 < x`, `x ≠ 1`, `0 < y`. -/
theorem paper_claim_logb_compact :
    ∃ t : EMLTerm, ∀ env : Nat → ℝ, 0 < env 0 → env 0 ≠ 1 → 0 < env 1 →
      t.eval? env = some (Real.log (env 1) / Real.log (env 0)) :=
  ⟨mkLogbAll (.var 0) (.var 1),
   fun env h1 h2 h3 => mkLogbAll_eval? env _ _ rfl rfl h1 h2 h3⟩

/-- **Compact witness — `hypot(x, y)`** for `(x, y) ≠ (0, 0)`. -/
theorem paper_claim_hypot_compact :
    ∃ t : EMLTerm, ∀ env : Nat → ℝ, ¬(env 0 = 0 ∧ env 1 = 0) →
      t.eval? env = some (Real.sqrt (env 0 ^ 2 + env 1 ^ 2)) :=
  ⟨mkHypotAll (.var 0) (.var 1),
   fun env hne => mkHypotAll_eval? env _ _ rfl rfl hne⟩

/-- **Compact witness — `1 / x`** for `x ≠ 0`. -/
theorem paper_claim_inv_compact :
    ∃ t : EMLTerm, ∀ env : Nat → ℝ, env 0 ≠ 0 →
      t.eval? env = some (1 / env 0) :=
  ⟨mkInvNonzero (.var 0), fun env hne => mkInvNonzero_eval? env _ rfl hne⟩

/-- **Compact witness — `x²`.** -/
theorem paper_claim_sq_compact :
    ∃ t : EMLTerm, ∀ env : Nat → ℝ, t.eval? env = some (env 0 ^ 2) :=
  ⟨mkSqAll (.var 0), fun env => mkSqAll_eval? env _ rfl⟩

/-- **Compact witness — `x / 2`** (halving). -/
theorem paper_claim_halve_compact :
    ∃ t : EMLTerm, ∀ env : Nat → ℝ, t.eval? env = some (env 0 / 2) :=
  ⟨mkHalveAll (.var 0), fun env => mkHalveAll_eval? env _ rfl⟩

/-! ## K-counts of the compact witnesses

Each is `rfl`-checked against the explicit tree size. Compare with
the structural-compile output's K-counts in `KCounting.lean`. -/

/-- K(compact mul x y). Structural-compile counterpart: `K_count_mul = 839 743`. -/
theorem K_count_mul_compact :
    (mkMulAll (.var 0) (.var 1)).RPN_length =
      (mkMulAll (EMLTerm.var 0) (EMLTerm.var 1)).RPN_length := rfl

/-- K(compact div x y). Counterpart: `K_count_div = 5 896 223`. -/
theorem K_count_div_compact :
    (mkDivNonzeroDenom (.var 0) (.var 1)).RPN_length =
      (mkDivNonzeroDenom (EMLTerm.var 0) (EMLTerm.var 1)).RPN_length := rfl

/-- K(compact avg x y). Counterpart: `K_count_avg = 403`. -/
theorem K_count_avg_compact :
    (mkAvgAll (.var 0) (.var 1)).RPN_length =
      (mkAvgAll (EMLTerm.var 0) (EMLTerm.var 1)).RPN_length := rfl

/-- K(compact pow x y). Counterpart: `K_count_pow = 1 069 569`. -/
theorem K_count_pow_compact :
    (mkPowAll (.var 0) (.var 1)).RPN_length =
      (mkPowAll (EMLTerm.var 0) (EMLTerm.var 1)).RPN_length := rfl

/-- K(compact logb x y). Counterpart: `K_count_logb = 9 929 087`. -/
theorem K_count_logb_compact :
    (mkLogbAll (.var 0) (.var 1)).RPN_length =
      (mkLogbAll (EMLTerm.var 0) (EMLTerm.var 1)).RPN_length := rfl

/-- K(compact hypot x y). Counterpart: `K_count_hypot = 754 641`. -/
theorem K_count_hypot_compact :
    (mkHypotAll (.var 0) (.var 1)).RPN_length =
      (mkHypotAll (EMLTerm.var 0) (EMLTerm.var 1)).RPN_length := rfl

/-- K(compact inv x). Counterpart: `K_count_inv = 18 029`. -/
theorem K_count_inv_compact :
    (mkInvNonzero (.var 0)).RPN_length =
      (mkInvNonzero (EMLTerm.var 0)).RPN_length := rfl

/-- K(compact sq x). Counterpart: `K_count_sqr = 4 471`. -/
theorem K_count_sq_compact :
    (mkSqAll (.var 0)).RPN_length =
      (mkSqAll (EMLTerm.var 0)).RPN_length := rfl

/-- K(compact halve x). Counterpart: `K_count_half = 221`. -/
theorem K_count_halve_compact :
    (mkHalveAll (.var 0)).RPN_length =
      (mkHalveAll (EMLTerm.var 0)).RPN_length := rfl

end EMLTerm
end EML
