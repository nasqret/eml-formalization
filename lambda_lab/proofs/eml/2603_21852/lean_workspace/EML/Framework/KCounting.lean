import EML.Framework.Complex.Term
import EML.Framework.Complex.Closures.Constants
import EML.Framework.Compilers.F36ToEL
import EML.Framework.Compilers.ELToEML
import EML.Framework.Complex.Builders.Trig
import EML.Framework.Complex.Closures.Trig

/-!
# K-counting — RPN-length of public EML witness terms

`RPN_length : EMLTermℂ → ℕ` counts the number of `eml` constructors in
a term tree. This matches the paper's "K" figures in Supplementary
Table 4 (witness lengths in reverse-Polish notation, where each `eml`
node contributes one operator and atoms contribute one each).

For terms whose definitions are public (the closed numeric constants
exposed in `Closures/Constants.lean`), the K-count reduces by `decide`
to a numeric literal, giving a machine-checked counterpart to each row
of Table 4.

Atoms contribute 1 each; `eml(a, b)` contributes `1 + length(a) + length(b)`.
This matches the standard RPN convention (postfix: emit children, then
the operator).
-/

namespace EML

/-- Number of nodes (atoms + `eml` operators) in a complex EML term. -/
def EMLTermℂ.RPN_length : EMLTermℂ → ℕ
  | .one     => 1
  | .var _   => 1
  | .eml a b => 1 + a.RPN_length + b.RPN_length

@[simp] lemma EMLTermℂ.RPN_length_one : (EMLTermℂ.one).RPN_length = 1 := rfl
@[simp] lemma EMLTermℂ.RPN_length_var (n : Nat) : (EMLTermℂ.var n).RPN_length = 1 := rfl
@[simp] lemma EMLTermℂ.RPN_length_eml (a b : EMLTermℂ) :
    (EMLTermℂ.eml a b).RPN_length = 1 + a.RPN_length + b.RPN_length := rfl

/-- Number of nodes (atoms + `eml` operators) in a real EML term. -/
def EMLTerm.RPN_length : EMLTerm → ℕ
  | .one     => 1
  | .var _   => 1
  | .eml a b => 1 + a.RPN_length + b.RPN_length

@[simp] lemma EMLTerm.RPN_length_one : (EMLTerm.one).RPN_length = 1 := rfl
@[simp] lemma EMLTerm.RPN_length_var (n : Nat) : (EMLTerm.var n).RPN_length = 1 := rfl
@[simp] lemma EMLTerm.RPN_length_eml (a b : EMLTerm) :
    (EMLTerm.eml a b).RPN_length = 1 + a.RPN_length + b.RPN_length := rfl

/-! ## Machine-checked K-counts for the public closed witnesses

For each closed numeric/imaginary witness exposed in
`Closures/Constants.lean`, the K-count reduces by `rfl` to a concrete
numeric literal — i.e., we machine-check the witness tree's size against
the paper's Table 4 figures. -/

/-- Witness tree size for `0`. -/
theorem K_count_zero : EMLRealizationℂ.realizeℂ_zero.term.RPN_length = 7 := rfl

/-- Witness tree size for `2`. -/
theorem K_count_two : EMLRealizationℂ.realizeℂ_two.term.RPN_length = 19 := rfl

/-- Witness tree size for `−i`. -/
theorem K_count_negI :
    EMLRealizationℂ.realizeℂ_negI.term.RPN_length = 127 := rfl

/-- Witness tree size for `i`. Paper Table 4 reports K = 131; our
compiler-generated witness is structurally larger because it is
**built mechanically** from the reduction chain rather than hand-tuned. -/
theorem K_count_i :
    EMLRealizationℂ.realizeℂ_i.term.RPN_length = 407 := rfl

/-- Witness tree size for `π`. Paper Table 4 reports K = 193; our
compiler-generated witness is similarly larger. -/
theorem K_count_pi :
    EMLRealizationℂ.realizeℂ_pi.term.RPN_length = 233 := rfl

/-! ## K-counts for the F36 paper primitives (real fragment)

Each of these computes the size of the compiler-produced witness term
for the corresponding paper primitive. The witness comes from
`F36Expr.real_complete (.<f>) (.<f>) rfl` and equals
`((.<f>).compile : EMLTerm)` after the structural compiler lifts the
ELExpr to EMLTerm.

These are larger than the paper's hand-tuned figures because our
witnesses are produced by a single structural-compiler theorem rather
than per-primitive optimization. -/

/-- K(`var n`) — projection. The trivial atom. -/
theorem K_count_var (n : Nat) :
    ((ELExpr.var n).compile).RPN_length = 1 := rfl

/-- K(`one`) — the constant 1. -/
theorem K_count_one : ((ELExpr.one).compile).RPN_length = 1 := rfl

/-- K(`e_const`) — the constant `e = exp(1)`. -/
theorem K_count_e_const : ((ELExpr.e_const).compile).RPN_length = 3 := rfl

/-- K(`exp x`). -/
theorem K_count_exp :
    ((ELExpr.exp (.var 0)).compile).RPN_length = 3 := rfl

/-- K(`log x`). -/
theorem K_count_log :
    ((ELExpr.log (.var 0)).compile).RPN_length = 7 := rfl

/-- K(`negOne`). -/
theorem K_count_negOne :
    ((ELExpr.negOne).compile).RPN_length = 17 := rfl

/-- K(`two`). -/
theorem K_count_two_real :
    ((ELExpr.two).compile).RPN_length = 19 := rfl

/-- K(`half_const`). -/
theorem K_count_half_const :
    ((ELExpr.half_const).compile).RPN_length = 59 := rfl

/-- K(`half x`). -/
theorem K_count_half :
    ((ELExpr.halve (.var 0)).compile).RPN_length = 221 := rfl

/-- K(`minus x`). -/
theorem K_count_minus :
    ((ELExpr.neg (.var 0)).compile).RPN_length = 17 := rfl

/-- K(`sqr x`). -/
theorem K_count_sqr :
    ((ELExpr.sq (.var 0)).compile).RPN_length = 4471 := rfl

/-- K(`add x y`). The structurally-compiled add is much shorter than mul
because addition uses a chunk-040 ADDsafe pattern with bounded depth. -/
theorem K_count_add :
    ((ELExpr.add (.var 0) (.var 1)).compile).RPN_length = 27 := rfl

/-- K(`sub x y`). -/
theorem K_count_sub :
    ((ELExpr.sub (.var 0) (.var 1)).compile).RPN_length = 43 := rfl

/-- K(`mul x y`). The compositional multiply explodes — `mkMulAll` cascades
through sign cases and the universal-square Builder. -/
theorem K_count_mul :
    ((ELExpr.mul (.var 0) (.var 1)).compile).RPN_length = 839743 := rfl

/-- K(`avg x y`). -/
theorem K_count_avg :
    ((ELExpr.avg (.var 0) (.var 1)).compile).RPN_length = 403 := rfl

/-- K(`inv x`). The reciprocal builder cascades through sign-aware logic. -/
theorem K_count_inv :
    ((ELExpr.inv (.var 0)).compile).RPN_length = 18029 := rfl

/-- K(`sqrt x`). The structural sqrt uses `mkSqrtPos`. -/
theorem K_count_sqrt :
    ((ELExpr.sqrt (.var 0)).compile).RPN_length = 2589 := rfl

/-- K(`div x y`). Unrestricted-denominator division composes through `mkInv`. -/
theorem K_count_div :
    ((ELExpr.div (.var 0) (.var 1)).compile).RPN_length = 5896223 := rfl

/-- K(`pow x y`). Power via `exp(y · log x)`. -/
theorem K_count_pow :
    ((ELExpr.pow (.var 0) (.var 1)).compile).RPN_length = 1069569 := rfl

/-- K(`logb x y`). Change-of-base via `log y / log x`. -/
theorem K_count_logb :
    ((ELExpr.logb (.var 0) (.var 1)).compile).RPN_length = 9929087 := rfl

/-- K(`hypot x y`). -/
theorem K_count_hypot :
    ((ELExpr.hypot (.var 0) (.var 1)).compile).RPN_length = 754641 := rfl

/-! ## K-counts for compositionally-translated F36 primitives

The hyperbolic family and `sigma` are not native ELExpr constructors;
F36→EL expands them to compositions:

* `sigma a    ↦ inv (1 + exp(-a))`
* `sinh a     ↦ ((exp a - exp (-a)) / 2)`
* `cosh a     ↦ ((exp a + exp (-a)) / 2)`
* `tanh a     ↦ sinh a / cosh a`
* `arsinh a   ↦ log (a + √(a² + 1))`
* `arcosh a   ↦ log (a + √(a² − 1))`
* `artanh a   ↦ ((log (1 + a) − log (1 − a)) / 2)`

Each K-count below counts the compiled witness for the **expanded ELExpr**
that F36's `translate?` produces. -/

/-- K(`sigma x`) — `inv (1 + exp(-x))`. -/
theorem K_count_sigma :
    ((ELExpr.inv (.add .one (.exp (.neg (.var 0))))).compile).RPN_length = 98593 := rfl

/-- K(`sinh x`) — `(exp x − exp(−x)) / 2`. -/
theorem K_count_sinh :
    ((ELExpr.halve (.sub (.exp (.var 0)) (.exp (.neg (.var 0))))).compile).RPN_length
      = 935 := rfl

/-- K(`cosh x`) — `(exp x + exp(−x)) / 2`. -/
theorem K_count_cosh :
    ((ELExpr.halve (.add (.exp (.var 0)) (.exp (.neg (.var 0))))).compile).RPN_length
      = 571 := rfl

/-- K(`tanh x`) — `sinh x / cosh x`. -/
theorem K_count_tanh :
    ((ELExpr.div
      (.halve (.sub (.exp (.var 0)) (.exp (.neg (.var 0)))))
      (.halve (.add (.exp (.var 0)) (.exp (.neg (.var 0)))))).compile).RPN_length
      = 535416191 := rfl

/-- K(`arsinh x`) — `log (x + √(x² + 1))`. -/
theorem K_count_arsinh :
    ((ELExpr.log (.add (.var 0)
      (.sqrt (.add (.sq (.var 0)) .one)))).compile).RPN_length = 566933 := rfl

/-- K(`arcosh x`) — `log (x + √(x² − 1))` (sealed only on `1 < x`). -/
theorem K_count_arcosh :
    ((ELExpr.log (.add (.var 0)
      (.sqrt (.sub (.sq (.var 0)) .one)))).compile).RPN_length = 567605 := rfl

/-- K(`artanh x`) — `(log (1 + x) − log (1 − x)) / 2`. -/
theorem K_count_artanh :
    ((ELExpr.halve (.sub
      (.log (.add .one (.var 0)))
      (.log (.sub .one (.var 0))))).compile).RPN_length = 2195 := rfl

/-! ## K-counts for the four trig literal EMLTermℂ witnesses

These are the hand-built complex-fragment witnesses introduced in
`Complex/Builders/Trig.lean`. They are **literal**, not compiler-generated. -/

/-- K(`cos x`) — `cosTermℂ` (closure on `(0, ∞)`). -/
theorem K_count_cos : cosTermℂ.RPN_length = 1273 := rfl

/-- K(`sin x`) — `sinTermℂ` (closure on `(0, π)`). -/
theorem K_count_sin : sinTermℂ.RPN_length = 1703 := rfl

/-- K(`arctan x`) — `arctanTermℂ` (closure on `(0, π)`). -/
theorem K_count_arctan : arctanTermℂ.RPN_length = 1303 := rfl

/-- K(`arccos x`) — `arccosTermℂ` (closure on `(-1, 1)`). -/
theorem K_count_arccos : arccosTermℂ.RPN_length = 568875 := rfl

/-- K(`arcsin x`) — `arcsinTermℂ` (closure on `(0, 1)`). -/
theorem K_count_arcsin : arcsinTermℂ.RPN_length = 1704019 := rfl

/-- K(`tan x`) — `tanCoreTermℂ` Cayley quotient (closure on `(0, π/2)`). -/
theorem K_count_tan : tanCoreTermℂ.RPN_length = 2817 := rfl

/-! ## K-counts for the widening companions

These are the companion witnesses for the widened domains documented
in `paper_claim_arcsin_open`, `paper_claim_arctan_neg`,
`paper_claim_cos_neg`. -/

/-- K(`arcsin x`) on full `(-1, 1)` — wider witness via `iπ/2 − arccosTermℂ`. -/
theorem K_count_arcsin_open : arcsinTermℂ_open.RPN_length = 569297 := rfl

/-- K(`arctan x`) for `x < 0` — companion via `1 − i·(−x)`. -/
theorem K_count_arctan_neg : arctanTermℂ_neg.RPN_length = 1303 := rfl

/-- K(`cos x`) for `x < 0` — companion using `cos(−x) = cos(x)`. -/
theorem K_count_cos_neg : cosTermℂ_neg.RPN_length = 1289 := rfl

/-- K(`sin x`) for `-π < x < 0` — companion `mkExpℂ (mkSubℂ (mkLogℂ
cosTermℂ_neg) (mkLogℂ negIPubℂ))`. -/
theorem K_count_sin_neg : sinTermℂ_neg.RPN_length = 1439 := rfl

/-- K(`tan x`) for `-π/2 < x < 0` — swap-numerator Cayley companion. -/
theorem K_count_tan_neg : tanCoreTermℂ_neg.RPN_length = 2849 := rfl

end EML



