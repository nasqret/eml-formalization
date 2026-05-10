# Repository audit report

> Date: 2026-05-10
> Branch: `feat/path-c-prime-and-plan-d` @ `5263518`
> Scope: full sweep — build state, git hygiene, chunk integrity,
> cross-document consistency, generated artefacts, external services,
> link resolution.
> Method: each finding has a re-runnable shell command in
> `## Evidence` so the user can verify independently.

## Headline

**Build is healthy** — `lake build` clean at 8056 jobs, sorry-free in
the public-API surface. **No silent regressions.** Ten anomalies
found, none of them block correctness; **most are documentation drift
or dead-code housekeeping** introduced incrementally over the past
~36 hours of fast iteration. Three are real engineering issues worth
addressing before public release.

| Severity | Count |
|---|---:|
| 🔴 Blocking-for-release | 0 |
| 🟠 Should-fix-before-release | 5 |
| 🟡 Nice-to-fix | 5 |
| ✅ Verified clean | 4 |

## Findings

### 🟠 Anomaly 1 — orphan `EML/Functions/*.lean` files contain stray `sorry`

**Files:**
- `EML/Functions/Constants.lean` — `theorem e_via_eml ... := by sorry`
- `EML/Functions/Arithmetic.lean` — two `sorry`s for `mul_via_exp_log`, `add_via_exp_log`
- `EML/Functions/Transcendental.lean` — one `sorry` for the structural log identity

**Why it matters.** These files are **not imported from `EML.lean` or
anywhere else in the workspace** (verified — see Evidence). They survive
because `lake build` only compiles reachable modules. A casual reader
running `grep -r sorry EML/` would see them and conclude the artefact
is incomplete; that conclusion would be false (the public API has zero
`sorry`), but the impression is bad on a first-look at GitHub.

**Fix.** Delete the three files (they're early-stage stubs supplanted
by `EML.Framework.PaperClaims` long ago).

**Evidence:**
```bash
$ grep -r 'EML.Functions' EML*/ --include="*.lean"
# (no output — confirms zero imports)
$ grep -E '\bsorry\b' EML/Functions/*.lean | head
EML/Functions/Constants.lean:theorem e_via_eml : Real.exp 1 = EML.eml 1 1 := by sorry
EML/Functions/Arithmetic.lean:    x * y = Real.exp (Real.log x + Real.log y) := by sorry
EML/Functions/Arithmetic.lean:    x + y = Real.log (Real.exp x * Real.exp y) := by sorry
EML/Functions/Transcendental.lean:    Real.log z = EML.eml 1 (EML.eml (EML.eml 1 z) 1) := by sorry
```

### 🟠 Anomaly 2 — three empty chunk directories

**Dirs:**
- `chunks/076_atan_arg_eval/`
- `chunks/084_edl_witness_exp/`
- `chunks/085_edl_witness_neg_one/`

**Why it matters.** Empty placeholders left over from earlier task
slating; readers browsing `chunks/` will see numbered directories
that contain nothing.

**Fix.** `rmdir` the three.

**Evidence:**
```bash
$ find lambda_lab/proofs/eml/2603_21852/chunks -type d -empty
lambda_lab/proofs/eml/2603_21852/chunks/076_atan_arg_eval
lambda_lab/proofs/eml/2603_21852/chunks/084_edl_witness_exp
lambda_lab/proofs/eml/2603_21852/chunks/085_edl_witness_neg_one
```

### 🟠 Anomaly 3 — paper-claim counts drift across docs

**Reality:** 48 EML + 8 EDL + **5** −EML = **61 total** (after the
EReal-grammar Plan E E3 lift in `a9381db`).

**Stale claims:**

| File | Says | Reality |
|---|---|---|
| `README.md` "At a glance" | EDL **5**, −EML **2** | EDL 8, −EML 5 |
| `README.md` "Quick start" line | `make scoreboard # lists 45 paper_claim theorems` | 48 (or 61 if Sheffer counted) |
| `DASHBOARD.md` | 58 (48 + 8 + 2) | 61 (48 + 8 + 5) |
| `slides/ghostday_post_submission` | "8 EDL + 2 −EML" / "58 paper claims" | 8 + 5 / 61 |
| `web/eml-tree-builder/index.html` | (no count claim — fine) | — |
| `notes/proof_structure.tex` | "$48$ paper_claim_*" + "$8$ edl + $2$ negEml" | 48 + 8 + 5 |

**Why it matters.** The Plan E E3 commit landed three new theorems
(`negEml_paper_claim_one_E`, `negEml_paper_claim_var_E`,
`negEml_paper_claim_minusInf`) but the docs sweep didn't bump the
counts everywhere.

**Fix.** Single-pass `sed`/edit to bump the four files.

**Evidence:**
```bash
$ grep -cE '^theorem (paper_claim|edl_paper_claim|negEml_paper_claim)' \
    EML/Framework/PaperClaims.lean EML/Framework/Sheffer.lean
EML/Framework/PaperClaims.lean:48
EML/Framework/Sheffer.lean:13   # 8 edl + 5 negEml = 13
```

### 🟠 Anomaly 4 — stale local `main` (7 commits behind origin)

**Symptom.** Local `main` is at `84682c7` (PR #1 merge); origin/main is
many commits ahead via PR #2 and PR #3 merges. Other local branches
(`feat/plan-a-...`, `feat/plan-bc-foundation`) are merged but never
deleted locally.

**Why it matters.** Anyone cloning fresh sees the right state. But the
**current development checkout** is in a state where `git switch main`
gives a 7-commits-behind starting point; easy to accidentally branch
off the wrong base.

**Fix.** `git switch main && git pull --ff-only`, then `git branch -d
feat/plan-a-... feat/plan-bc-foundation` for the merged feature
branches. Also delete on origin.

**Evidence:**
```bash
$ git branch -v | head -4
* feat/path-c-prime-and-plan-d                  5263518 web: complete...
  feat/plan-a-sheffer-cleanup-and-slides-rename 4c99d17 Slides: rename...
  feat/plan-bc-foundation                       ef291ee OPEN_QUESTIONS...
  main                                          84682c7 [behind 7] ...
```

### 🟠 Anomaly 5 — `.gitignore` doesn't catch sub-directory `build/` dirs

**Symptom.** `.gitignore` has `slides/build/` (top-level under slides)
and `build/` (top-level), but **NOT** `slides/*/build/`. The slide
deck builds produce
`slides/ghostday_post_submission/build/` — a 5.6 MB PDF + reveal.js
HTML — which isn't gitignored.

Currently nothing is staged because I haven't `git add`ed those build
dirs, but a casual `git add .` from the wrong directory could land
8 MB of generated artefacts.

**Fix.** Add the patterns:
```
slides/*/build/
slides/*/build.html.bak
```

**Evidence:**
```bash
$ ls -d slides/*/build/
slides/ghostday_post_submission/build/

$ git check-ignore slides/ghostday_post_submission/build/ghostday_post_submission.pdf
# (no output — file is NOT ignored)
```

### 🟡 Anomaly 6 — three `chunks/` claim status="complete" but lack `result.lean`

**Chunks:**
- `029_eml_minimality/` (complete, no result.lean)
- `034_emlterm_for_pi/` (complete, no result.lean)
- `035_emlterm_for_i/` (complete, no result.lean)

**Why it matters.** This is **expected behaviour** — these chunks were
sealed by hand-coded Lean (in `EML/Solutions/` or `EML/Framework/`),
not by Aristotle, so there's no "Aristotle returned a result.lean"
file. But the convention is currently undocumented; a new collaborator
would not know that absence-of-result.lean is fine for hand-coded
chunks.

**Fix.** Document the convention in `chunks/README.md` (one line:
"`result.lean` is the Aristotle-returned proof; hand-coded chunks
don't have one"), or add a `meta.json` field
`"completed_by": "hand"` vs `"aristotle"`.

**Evidence:** see `/tmp/audit_chunks.sh` output.

### 🟡 Anomaly 7 — README's "Quick start" mentions 45 paper claims (very stale)

**Line:** `README.md:179` —
```
make scoreboard           # lists 45 paper_claim theorems and 15 K_count theorems
```

**Reality:** 48 paper claims (50 if you count `paper_claim_sin_full`
etc., 61 if Sheffer is counted).

**Fix.** Bump to "48 paper claims (61 including Sheffer-cousin Plan D
+ Plan E)".

### 🟡 Anomaly 8 — `chunks/076_atan_arg_eval/` is referenced in `PATH_C_PRIME_TASKS.md` but empty

The task slate at line 44 lists chunk 076 as *"`atanArgELℝ` —
real-fragment compile of `x / √(1 + x²)`"* with status ✅. The
witness IS implemented in `Periodicity.lean` (commit `872797d`), but
the corresponding chunk dir was never populated with a target/result/
meta. The status mark is correct (the work IS done, just at the
framework level), but a reader following the chunk number into the
filesystem hits an empty dir.

**Fix.** Either populate the chunk with a placeholder doc pointing at
`Periodicity.lean`, or remove the entry from the task slate.

### 🟡 Anomaly 9 — paper claim listing in DASHBOARD shows old set of 48

`DASHBOARD.md:192` and the verbatim listing 191-205 still has the
exact 48-theorem dump from early May 8. With the 5 −EML and 8 EDL
added in Sheffer.lean, this listing is incomplete relative to "all
paper-claim theorems exposed." Strictly the listing IS accurate for
`PaperClaims.lean` alone (48 EML), but the `## Public API surface`
section header reads like it should cover everything.

**Fix.** Either rename the section to "Public API surface — EML
paper claims" or extend the listing with the EDL/−EML rows.

### 🟡 Anomaly 10 — no `web/eml-tree-builder/CONTRIBUTING.md` or licence note

The web tool has its own MIT licence (inherited from repo root) but
no `LICENSE` symlink and no contributor notes. For public release with
the site potentially deployed, that's a thin spot — anyone forking
might miss the licence inheritance.

**Fix.** Add a short note in `web/eml-tree-builder/README.md` clarifying
the inherited licence.

## ✅ Verified clean

| Item | Status |
|---|---|
| `lake build` | 8056 jobs, sorry-free |
| Public API `paper_claim_*` axiom-cleanliness | no project-specific axioms |
| Markdown link resolution (README, DASHBOARD, First_run) | no broken links |
| Eagle SSH key | present, 411 bytes ED25519 (fingerprint `tqXJ5...`) |
| Aristotle credentials | `~/.config/aristotle/env` populated |
| Git remote | tracking, in sync |
| No build artefacts tracked in git | confirmed (`git ls-files | grep build` empty) |

## Pre-release engineering punch list

Combining the audit findings with broader pre-public-release polish:

### Must-fix before release (estimated 1 hour total)

1. **Delete `EML/Functions/{Constants,Arithmetic,Transcendental}.lean`** — orphan stubs with stray `sorry`s (Anomaly 1, 5 min)
2. **`rmdir` the three empty chunk dirs** (Anomaly 2, 1 min)
3. **Bump paper-claim counts in 5 docs** to 48 EML + 8 EDL + 5 −EML = 61 (Anomaly 3, 15 min)
4. **Fix `.gitignore`** with `slides/*/build/` pattern (Anomaly 5, 1 min)
5. **Sync local main + delete merged branches** (Anomaly 4, 5 min)

### Should-do before release (estimated 2-3 hours)

6. **Add a CONTRIBUTING.md** at repo root: how to run `make build`, where chunks live, where to file issues, what's the PR review style, expected turnaround.
7. **Add a CITATION.cff** so `Cite this repository` shows up on GitHub: project name, authors (Bartosz Naskręcki + acknowledgements), version, DOI placeholder for the Zenodo deposit when available.
8. **Add CI** — minimal GitHub Actions workflow that runs `make prereqs && make build` on every PR. Mathlib's CI does this; we should mirror.
9. **Tag a release** `v1.0.0-rc.1` with the current state. Without a tag, GitHub Pages and Zenodo can't reference a stable point.
10. **Document `chunks/` convention** — one-page README in `chunks/` explaining numbering scheme, meta.json schema, status field meanings, when to expect result.lean.
11. **Pin the Aristotle CLI version** — currently `aristotle 1.0.1`; document in `Makefile` or `pyproject.toml` so reproducers know what they need.
12. **Remove or tag-archive the obsolete `Solutions/068_*` etc.** that cite removed `T1Term`/`T2Term` if any (need to grep).

### Nice-to-have polish (estimated 1 day)

13. **GitHub Pages config**: deploy `web/eml-tree-builder/` to gh-pages so people can use the interactive tool without cloning.
14. **README badges row**: Zenodo DOI, Lean version, Mathlib version, Build status. The DASHBOARD already has these; promote to README headline.
15. **Author homepage / contact**: README already has the email; consider adding ORCID and institutional affiliations as a `cv:` block.
16. **Clean up `slides/eml_presentation/` and `slides/ghostday/`** — `ghostday_post_submission` is the canonical version; the other two are pre-submission states. Either keep with a note ("preserved for historical comparison"), or move to an `archive/` subdirectory.
17. **Sample notebook / Jupyter / VS Code workspace** showing how to `#check paper_claim_<f>` interactively — lowers the bar for readers who have never used Lean.
18. **Pin the `lean4-v4.28.0-linux.tar.zst` URL** in the Eagle scripts in case the upstream URL changes — currently the `rebuild_cache.sbatch` assumes the local tarball is already present.
19. **A short paper-style PDF for the artefact itself** (1–2 pages): "*The Lean formalization of arXiv:2603.21852: a tour of the public API*" — could live alongside `proof_structure.pdf` in `notes/`.
20. **Generate a `K_count` summary table** as a `make k-table` target, automatically rendering all the K-counts as a markdown/HTML table in `DASHBOARD.md` rather than the current hand-curated bar chart.

### Out of scope for this release (research)

- Plan D's remaining 28 EDL primitives (structurally unreachable per Aristotle's analysis)
- Plan E's remaining 33 −EML primitives (same arithmetic obstruction)
- The seven open questions from SI §1.5 (paper-open by the author's own framing)
- §3.2 universal minimality conjecture
- §4.3 gradient-training formalization (needs Mathlib infrastructure that doesn't exist)

## Recommended release sequence

1. **Day 0** — apply must-fix items 1–5 (1 hour). Tag `v1.0.0-rc.1`.
2. **Day 1** — apply should-do items 6–10 (half day). Tag `v1.0.0-rc.2`.
3. **Day 2** — set up CI (item 8), Pages deployment for the web tool (item 13), Zenodo DOI minting via the GitHub release integration. Tag `v1.0.0`.
4. **Post-release** — items 11, 12, 14–20 as time/interest permits.

The repo is **structurally ready for public release today** modulo the
must-fix items, all of which are documentation/cleanup, not correctness
issues.
