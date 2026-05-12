# Licensing

This repository is **dual-licensed**.

| What | License | File |
|---|---|---|
| **Code** — Lean sources, Python sources, shell scripts, Makefiles, Lake configs, web tool, the LaTeX `.tex` machinery that *builds* the docs (preambles, custom macros, packages — but not the prose content of the documents) | Apache License 2.0 | [`LICENSE`](LICENSE) |
| **Documentation and narrative prose** — `README.md`, `DASHBOARD.md`, `CONTRIBUTING.md`, `LICENSING.md` (this file), `lambda_lab/.../AUTHOR_SUMMARY.md`, `lambda_lab/.../OPEN_QUESTIONS.md`, `lambda_lab/.../VERIFICATION_EVIDENCE.md`, `lambda_lab/.../README.md`, `lambda_lab/.../report/REPORT.tex` (the prose, not the LaTeX scaffolding), `lambda_lab/.../notes/proof_structure.tex` (same), slide-deck markdown under `slides/`, all `.md` files under `process_archive/` | Creative Commons Attribution-ShareAlike 4.0 International (CC BY-SA 4.0) | [`LICENSE-DOCS`](LICENSE-DOCS) |
| **The source paper** — `paper/EML.tex`, `paper/EML.bib`, `paper/Fig*.pdf`, `paper/anc/`, `paper/SupplementaryInformation.pdf` | Copyright © Andrzej Odrzywołek. **Neither license above applies.** | n/a |

## What this means in plain English

- **You can use the Lean code in any project, including commercial and closed-source ones**, as long as you preserve the copyright notice and the `NOTICE` file. You also get an explicit patent grant.
- **If you reuse the prose** (the narrative parts of READMEs, REPORT.pdf, AUTHOR_SUMMARY.md, etc.) in another work — for example, lifting paragraphs into a paper, a blog post, or a derivative report — you must **credit** the source AND **share-alike**: your derivative must also be CC BY-SA 4.0 (or compatible).
- **You may not relicense the paper LaTeX in `paper/`** under either of the licenses here. That content remains the author's; it is included for reference.

## Practical examples

| Scenario | OK? |
|---|---|
| You write a Lean tutorial library that imports a few theorems from `EML.Framework.PaperClaims` | Yes — Apache 2.0 |
| You build a commercial symbolic-regression tool that uses `EMLTerm.eval?` internally | Yes — Apache 2.0 (preserve NOTICE and copyright) |
| You copy paragraphs from `REPORT.pdf` or `AUTHOR_SUMMARY.md` into your own paper | Yes, with attribution and your derivative under CC BY-SA 4.0 |
| You fork the repo and keep all your changes private | Yes — Apache 2.0 doesn't require disclosure |
| You quote a Lean theorem statement (a few lines of code) inside a paper | Yes — *de minimis* code use; in any case Apache 2.0 permits this with attribution |
| You redistribute `paper/EML.tex` under a license of your choice | **No.** That file is not yours to relicense. |

## How to cite

See [`CITATION.cff`](CITATION.cff). The recommended attribution form is given there in machine-readable BibTeX-compatible form. Citing both the source paper (Odrzywołek, arXiv:2603.21852) and this formalisation is the expected practice.

## SPDX tags

For automated tools, the dual licensing is captured as:

```
SPDX-License-Identifier: Apache-2.0 AND CC-BY-SA-4.0
```

with the per-file split governed by the table above.

## Questions

If a specific use case is unclear from the rules above, open an issue at
<https://github.com/nasqret/eml-formalization/issues> and the maintainer
will clarify.
