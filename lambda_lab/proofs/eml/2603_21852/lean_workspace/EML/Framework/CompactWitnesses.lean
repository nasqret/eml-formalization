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

This module provides **alternative direct-macro witnesses** for the
same paper claims, built directly from the unconditional macros
(`mkMulAll`, `mkDivNonzeroDenom`, `mkAvgAll`, `mkPowAll`, `mkLogbAll`,
`mkHypotAll`, `mkInvNonzero`) defined in `Builders/Unconditional.lean`.

**Honest finding** (verified by `K_count_*_compact` theorems below):
the K-counts of these direct-macro witnesses are **identical** to
the structural-compile counterparts in `KCounting.lean`. The
structural compiler internally uses these same `mk*All` macros, so
the compile output and the direct-macro construction produce the
same tree.

This is informative rather than disappointing: it tells us that the
dashboard's high K-counts are not an artefact of going through the
F36 → EL → EML pipeline; they reflect the actual cost of a witness
that works on the **full** real domain (negative inputs included).
Genuine K-count reduction would require either:
(a) restricting the paper-claim domains (positive-arg mul via
    `mkMulPos` is K=29 instead of 839 743 — but only handles
    positives), or
(b) introducing new macros with sharper domain hypotheses.

Both are out of scope for this module; the compact witnesses are
recorded for transparency about which witness shape underlies each
paper claim.
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

/-! ## K-counts of the compact witnesses — structural finding

The compact-witness K-counts are **identical** to the structural-
compile counterparts in `KCounting.lean`. This is not a bug: the
F36 → EL → EML compiler already uses the `mk*All` family internally,
so swapping `realize_via_compiler` for direct macro calls produces
the same tree.

The lesson: meaningful K-count reduction would require either
(a) restricting the paper-claim domains (e.g., positive-arg mul via
`mkMulPos` instead of `mkMulAll`, which avoids the case-analysis
pattern at the cost of dropping negative inputs), or (b) inventing
new macros with sharper domain hypotheses. Neither is in scope for
this module.

The compact-witness theorems above remain useful as **alternative
proofs of the same paper claims** that are visibly direct rather
than threaded through the compiler — but they do not shrink K. -/

/-- K(compact mul x y) = 839 743, same as `K_count_mul`. -/
theorem K_count_mul_compact :
    (mkMulAll (.var 0) (.var 1)).RPN_length = 839743 := rfl

/-- K(compact div x y) = 5 896 223, same as `K_count_div`. -/
theorem K_count_div_compact :
    (mkDivNonzeroDenom (.var 0) (.var 1)).RPN_length = 5896223 := rfl

/-- K(compact avg x y) = 403, same as `K_count_avg`. -/
theorem K_count_avg_compact :
    (mkAvgAll (.var 0) (.var 1)).RPN_length = 403 := rfl

/-- K(compact pow x y) = 1 069 569, same as `K_count_pow`. -/
theorem K_count_pow_compact :
    (mkPowAll (.var 0) (.var 1)).RPN_length = 1069569 := rfl

/-- K(compact logb x y) = 9 929 087, same as `K_count_logb`. -/
theorem K_count_logb_compact :
    (mkLogbAll (.var 0) (.var 1)).RPN_length = 9929087 := rfl

/-- K(compact hypot x y) = 754 641, same as `K_count_hypot`. -/
theorem K_count_hypot_compact :
    (mkHypotAll (.var 0) (.var 1)).RPN_length = 754641 := rfl

/-- K(compact inv x) = 18 029, same as `K_count_inv`. -/
theorem K_count_inv_compact :
    (mkInvNonzero (.var 0)).RPN_length = 18029 := rfl

/-- K(compact sq x) = 4 471, same as `K_count_sqr`. -/
theorem K_count_sq_compact :
    (mkSqAll (.var 0)).RPN_length = 4471 := rfl

/-- K(compact halve x) = 221, same as `K_count_half`. -/
theorem K_count_halve_compact :
    (mkHalveAll (.var 0)).RPN_length = 221 := rfl

end EMLTerm
end EML
