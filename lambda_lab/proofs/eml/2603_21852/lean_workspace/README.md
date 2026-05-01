# EML Lean workspace

This is a self-contained Lean 4 library for the EML formalization
(Odrzywolek, arXiv:2603.21852, "All elementary functions from a single
binary operator"). The skeleton hosts the definitions, the syntactic
term language, and `sorry`-stubbed targets that the auto-formalization
pipeline will populate.

## Toolchain

- Lean 4.28.0
- Mathlib v4.28.0

Both pinned to match the existing `lambda_lab/proofs/lean_aristotle/`
workspace so cached `.olean` files can be reused on machines that have
already built Mathlib.

## Setup

```bash
lake exe cache get   # fetch precompiled Mathlib oleans
lake build           # compile the EML library
```

`lake build EML.Basic` is the smallest verification — that file has no
`sorry` and exercises the Mathlib imports that every other module
transitively depends on.

## Layout

| Path                                | Role                                                   |
|-------------------------------------|--------------------------------------------------------|
| `EML.lean`                          | Top-level umbrella; imports every submodule.           |
| `EML/Basic.lean`                    | The `eml`, `edl`, and `negEml` operator definitions.   |
| `EML/Term.lean`                     | `EMLTerm` syntax + `size` and `eval` functions.        |
| `EML/Functions/Constants.lean`      | EML representations of mathematical constants.         |
| `EML/Functions/Arithmetic.lean`     | Identity 1 (exp/log reduction of arithmetic).          |
| `EML/Functions/Transcendental.lean` | Identity 5 (the natural-log identity).                 |
| `EML/Solutions/`                    | Auto-populated; chunk results land here.               |

## Auto-population

The `EML.Solutions` namespace is auto-populated by `eml watch` when
Aristotle returns proofs for the chunks listed under
`lambda_lab/proofs/eml/2603_21852/chunks/`. Each completed chunk lands
as `EML/Solutions/<chunk_id>.lean`; the `.gitkeep` placeholder is just
to keep the empty directory tracked by git.
