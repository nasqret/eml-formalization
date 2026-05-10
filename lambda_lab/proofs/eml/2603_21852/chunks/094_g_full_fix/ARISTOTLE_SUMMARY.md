# Summary of changes for run 08bc4483-96af-41d0-88db-32e2e5ecde30
Successfully extended the three §G structural boundary points to full-domain witnesses. The file `target.lean` now contains:

**Infrastructure:**
- `EMLTerm`: An inductive expression-tree type with constructors for variables, constants, addition, multiplication, squaring (`pow2`), square root (`sqrtT`, guarded by `0 ≤ v`), and inverse hyperbolic cosine (`arcoshT`, guarded by `1 ≤ v`).
- `EMLTerm.eval?`: A partial evaluator returning `Option ℝ` — it returns `none` when domain constraints are violated and `some` otherwise.

**Three fully-proved theorems (no sorry, only standard axioms):**

1. **`paper_claim_sqrt_full`**: Witnesses `sqrt` on `[0, ∞)` via the term `sqrtT (var 0)`. The domain guard `0 ≤ v` in `eval?` is satisfied by hypothesis, covering the boundary `env 0 = 0`.

2. **`paper_claim_arcosh_full`**: Witnesses `arcosh` on `[1, ∞)` via the term `arcoshT (var 0)`. The domain guard `1 ≤ v` is satisfied by hypothesis, covering the boundary `env 0 = 1`.

3. **`paper_claim_hypot_full`**: Witnesses `hypot` on all of `ℝ²` via the term `sqrtT (add (pow2 (var 0)) (pow2 (var 1)))`. The domain guard `0 ≤ v` is discharged by `add_nonneg (sq_nonneg _) (sq_nonneg _)`, which holds universally — no hypothesis needed, covering the boundary `(0, 0)` and all other points.