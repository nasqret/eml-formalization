# Mathematica entry-point

The Mathematica side of the EML proof — the `VerifyBaseSet` procedure
that originally discovered the EML operator and has since been used as
a witness oracle for compositional identities — lives **upstream**, in
the public repository

> [`github.com/VA00/SymbolicRegressionPackage`](https://github.com/VA00/SymbolicRegressionPackage)

(archival snapshot: [`doi.org/10.5281/zenodo.19183008`](https://doi.org/10.5281/zenodo.19183008)).

## What this directory is for

A stub: it reserves the path for future Mathematica work that should
live alongside the Lean formalisation in this repository, rather than
upstream. Candidates include:

* notebooks that compile EML expressions for individual primitives,
  cross-checked against `eval?` of the corresponding `EMLTermℂ` term;
* scripts that enumerate candidate witnesses for the open Sheffer
  cousins (EDL, −EML), to be fed into the Lean closure machinery;
* arbitrary-precision verification of witness identities at high
  digit-count, complementing the structural Lean proof.

When such artefacts are added, this README should be expanded to point
at them.

## Reproducing the original Mathematica search

To re-run the discovery procedure locally:

```mathematica
Import["SymbolicRegression.m"]                  (* from upstream repo *)
EML[x_, y_] := Exp[x] - Log[y]
VerifyBaseSet[{1}, {}, {EML}]
```

This regenerates all 36 elementary operations from the paper's Table 4
in well under an hour on a modern CPU. See the upstream repository for
the package source and documentation.

## See also

* `paper/EML.tex` — the paper itself, Section 3 of which describes the
  discovery procedure.
* `paper/SupplementaryInformation.pdf` — Sections 1.1–1.4, which
  document the Rust reimplementation `rust_verify` and Profiles 0/A/B/C
  of the exhaustive Sheffer-operator search.
