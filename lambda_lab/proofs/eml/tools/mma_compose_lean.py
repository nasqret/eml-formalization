#!/usr/bin/env python3
"""mma_compose_lean.py — turn a Mathematica search result into a Lean file.

Reads JSON spec + JSON search-result (from mma_eml_search.wls), emits a
Lean source file containing:
  - the EMLTerm / EMLTerm₁ / EMLTerm₂ inductive (depending on var count)
  - the eval definition
  - a `def witness` holding the synthesized tree
  - a `theorem <name> : ∃ t, ... := ⟨witness, by ...⟩` whose proof is a
    `simp` / `field_simp` / `ring` chain plus the constraint hypothesis.

Usage:
  python mma_compose_lean.py <spec.json> <result.json> <output.lean>

Spec JSON: same as the search input. Adds optional fields:
  "theorem_name":  defaults to "emlterm_synth"
  "theorem_stmt":  the ∃-form; if omitted, derived from target+constraint
"""

from __future__ import annotations

import json
import sys
from pathlib import Path


PREAMBLE_BY_NVARS = {
    0: """import Mathlib

namespace EML

inductive EMLTerm : Type
  | one : EMLTerm
  | eml : EMLTerm → EMLTerm → EMLTerm
  deriving Repr

noncomputable def EMLTerm.eval : EMLTerm → ℝ
  | .one => 1
  | .eml t u => Real.exp (EMLTerm.eval t) - Real.log (EMLTerm.eval u)
""",
    1: """import Mathlib

namespace EML

inductive EMLTerm₁ : Type
  | one : EMLTerm₁
  | var : EMLTerm₁
  | eml : EMLTerm₁ → EMLTerm₁ → EMLTerm₁
  deriving Repr

noncomputable def EMLTerm₁.eval (x : ℝ) : EMLTerm₁ → ℝ
  | .one => 1
  | .var => x
  | .eml t u => Real.exp (EMLTerm₁.eval x t) - Real.log (EMLTerm₁.eval x u)
""",
    2: """import Mathlib

namespace EML

inductive EMLTerm₂ : Type
  | one : EMLTerm₂
  | varX : EMLTerm₂
  | varY : EMLTerm₂
  | eml : EMLTerm₂ → EMLTerm₂ → EMLTerm₂
  deriving Repr

noncomputable def EMLTerm₂.eval (x y : ℝ) : EMLTerm₂ → ℝ
  | .one => 1
  | .varX => x
  | .varY => y
  | .eml t u => Real.exp (EMLTerm₂.eval x y t) - Real.log (EMLTerm₂.eval x y u)
""",
}


def emit(spec_path: Path, result_path: Path, out_path: Path) -> int:
    spec = json.loads(spec_path.read_text())
    result = json.loads(result_path.read_text())

    if not result.get("ok"):
        print(f"search did not succeed: {result.get('reason')}", file=sys.stderr)
        return 2

    tree = result["tree"]
    nvars = len(spec.get("vars", []))
    type_name = {0: "EMLTerm", 1: "EMLTerm₁", 2: "EMLTerm₂"}[nvars]
    target = spec["target"].replace("^", " ^ ")
    constraint = spec.get("constraint") or "True"
    theorem_name = spec.get("theorem_name") or "emlterm_synth"
    bind_vars = ["x", "y"][:nvars]
    bind_str = " ".join(bind_vars) + " : ℝ" if nvars else ""

    # Translate constraint to Lean (Mathematica → Lean form)
    lean_constraint = constraint.replace(">=", "≥").replace("<=", "≤")
    # Build the existential statement
    if nvars == 0:
        stmt = f"∃ t : {type_name}, {type_name}.eval t = {lean_target_expr(target)}"
    else:
        var_args = " ".join(bind_vars)
        if constraint and constraint != "True":
            stmt = (f"∃ t : {type_name}, ∀ {bind_str}, "
                    f"{lean_constraint} → {type_name}.eval {var_args} t "
                    f"= {lean_target_expr(target)}")
        else:
            stmt = (f"∃ t : {type_name}, ∀ {bind_str}, "
                    f"{type_name}.eval {var_args} t = {lean_target_expr(target)}")

    # Build the proof body
    if nvars == 0:
        proof = "  refine ⟨witness, ?_⟩\n  simp [witness, EMLTerm.eval, Real.log_one, Real.log_exp]"
    else:
        intros = " ".join(bind_vars) + (" h" if constraint and constraint != "True" else "")
        proof = (
            "  refine ⟨witness, fun " + intros + " => ?_⟩\n"
            f"  simp only [witness, {type_name}.eval, Real.log_one, sub_zero, Real.log_exp]\n"
            "  -- Aristotle/Mathematica synthesis: try simp_all + ring/field_simp\n"
            "  first\n"
            "    | (rfl)\n"
            "    | (ring)\n"
            "    | (field_simp; ring)\n"
            "    | (rw [Real.exp_log h]; ring)\n"
            "    | (rw [Real.exp_log (by positivity : (0:ℝ) < _)]; ring)\n"
            "    | (simp_all; try ring; try field_simp; ring_nf; rfl)"
        )

    body = (
        PREAMBLE_BY_NVARS[nvars]
        + "\n"
        + f"-- Synthesised by Mathematica (size = {result['size']}, "
        + f"searched {result.get('searched','?')} trees).\n"
        + f"def witness : {type_name} := {tree}\n"
        + "\n"
        + f"theorem {theorem_name} : {stmt} := by\n"
        + proof
        + "\n\n"
        + "end EML\n"
    )

    out_path.write_text(body, encoding="utf-8")
    print(f"wrote {out_path} ({len(body)} chars, witness size {result['size']})", file=sys.stderr)
    return 0


def lean_target_expr(mma: str) -> str:
    """Translate a Mathematica target expression to Lean syntax."""
    s = mma
    s = s.replace("^", " ^ ")
    s = s.replace("Sqrt[", "Real.sqrt (").replace("Log[", "Real.log (").replace("Exp[", "Real.exp (")
    # Matching brackets — naive replacement
    s = s.replace("Pi", "Real.pi")
    return s


if __name__ == "__main__":
    if len(sys.argv) != 4:
        print("usage: mma_compose_lean.py <spec.json> <result.json> <output.lean>", file=sys.stderr)
        sys.exit(1)
    sys.exit(emit(Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3])))
