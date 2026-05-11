# First_run.md — Claude bootstrap recipe

> **For a fresh Claude Code instance opened in a clone of this repository.**
>
> If a human user has just told you _"execute the instructions in
> First_run.md"_, follow the steps below in order. Each step is a
> shell command (run it via `Bash`) or a file you should `Read`.
> Stop at the end of Step 7 and present the summary to the user.

You are picking up a Lean 4 + Mathlib formalization of arXiv:2603.21852
(Andrzej Odrzywołek, *"All elementary functions from a single binary
operator"*). The previous Claude instance built the bulk of the proof;
your job is to get this fresh checkout into a verified, ready-to-work
state and to load enough context that the user can resume in a single
focused conversation rather than re-explaining the whole project.

---

## Step 1 — Read the orientation triple (do not skip)

In order, `Read` these three files. Each is short and gives you a
different layer of context.

1. `README.md` — the repo's project-level entry point.
2. `lambda_lab/proofs/eml/2603_21852/AUTHOR_SUMMARY.md` — author-facing
   synopsis: what is sealed, what surprised us, what remains open.
3. `lambda_lab/proofs/eml/2603_21852/OPEN_QUESTIONS.md` — concrete
   action plans for every feasible extension (Sheffer cleanup,
   full-real-domain trig, EDL / −EML completeness) plus paper-open
   conjectures and structural boundary points.

After reading these three files, you should be able to state in one
sentence (a) what the headline result is, (b) what is on this branch
versus what the user is hoping to extend, and (c) what the three §G
boundary points are.

## Step 2 — Check prerequisites

Run:

```bash
make prereqs
```

This verifies that `elan`, `lake`, `python3`, and `git` are on PATH.
If any are missing, **stop** and report to the user — they need to
install the missing tools before you proceed.

## Step 3 — Restore Claude auto-memory

Run:

```bash
make claude-memory-restore
```

This copies the `claude-memory/` folder out of the snapshot archive
(by default at `~/claude-archives/eml-formalization-2026-05-08/`) into
the current project's Claude memory directory, so any subsequent
session in this folder loads the same persistent context (user
identity, etc.).

If the archive is at a different path on this machine, the user can
override the location:

```bash
make claude-memory-restore ARCHIVE_DIR=/some/other/path
```

If the archive is unavailable (e.g.\ a clean machine without the
snapshot), the target prints a warning and exits 0; that is fine,
memory just starts empty.

## Step 4 — Install the Python CLI scaffold

Run:

```bash
make pip-install
```

This installs the slim Python package containing `aristotle.py` and
`eml.py` (the proof-tooling CLI) along with their three runtime
dependencies (`rich`, `prompt_toolkit`, `pyyaml`). The Lean artefact
itself does not need this; it is purely for invoking Aristotle
submissions and managing chunks.

## Step 5 — Verify the Lean build

Run:

```bash
make build
```

This is `lake build` inside `lambda_lab/proofs/eml/2603_21852/lean_workspace`.
On a cold Mathlib cache, the first build pulls ~6 GB of olean files
and takes 30–60 minutes. Subsequent builds are incremental and finish
in seconds.

When the build completes, the artefact is verified. The expected
output is `Build completed successfully (8062 jobs).` (the exact job
count may differ slightly with Mathlib version drift; the important
thing is `successfully` and no error lines).

If the build fails, **stop** and show the error to the user. Most
likely causes: (a) wrong Lean toolchain (check `lean-toolchain`
file), (b) Mathlib version skew, (c) network issue during cache
download.

## Step 6 — Run the sanity probe

Run:

```bash
make sanity
```

This `#check`s a handful of public paper-claim symbols (`paper_claim_pi`,
`paper_claim_sin`, `paper_claim_cos`, `K_count_pi`) to confirm that
the public API is accessible from outside the framework. The output
should show their type signatures.

## Step 7 — Print the scoreboard and report to the user

Run:

```bash
make scoreboard
make stats
```

Then read:

```bash
lambda_lab/proofs/eml/2603_21852/notes/proof_structure.pdf
```

(via `Read`; PDF reading is supported).

**Now stop and give the user a summary** with the following structure:

```
Setup complete. Status:

- Lean build:     {success/fail, with job count}
- Python CLI:     {installed/not}
- Claude memory:  {restored from <path> / unavailable}
- Paper claims:   {N theorems exposed in PaperClaims.lean}
- K-counts:       {N theorems in KCounting.lean}

Recent activity (from git log -5):
  {paste git log --oneline -5 output}

Plans status (from OPEN_QUESTIONS.md):
  - Plan A: Sheffer cleanup                                    ✅ DONE
  - Plan B: custom log branch                                  ❌ architecturally infeasible (see §B.0)
  - Plan C′: full-real-domain trig via range-reduction         ✅ DONE
            (GPT Pro recommendation; sin/arctan/tan covered)
  - Plan D: EDL per-primitive completeness                     🔄 8/36 sealed; 28 conjecturally unreachable
            (structural ceiling; closure thm + barrier typeclass
             in EML.Framework.EDLClosedVal — Pro #3)
  - Plan E: −EML per-primitive completeness                    🔄 5/36 sealed (2 ℝ + 3 EReal pilot);
            same structural ceiling as Plan D

Frontier work (GPT Pro consult 2026-05-10):
  - SI §1.5 #5 variable-transplant depths                      ✅ multiples-of-4 + d=1, 2 negative
            (in EML.Framework.TransplantDepths)
  - §G boundary points in EReal arithmetic                     ✅ all 3 templates sealed
            (in EML.Framework.StructuralLimitsEReal)
  - Polynomial-binary impossibility (paper §5)                 ✅ sealed
            (in EML.Framework.PolynomialBinary)

Ready to work. What would you like to tackle?
```

---

## Useful one-liners (for later in the session)

| Goal | Command |
|---|---|
| Incremental rebuild after edits | `make build` |
| Full clean re-verify | `make verify` |
| Print scoreboard | `make scoreboard` |
| Re-render the proof_structure paper | `make notes-pdf` |
| Re-render the GhostDay slide deck | `make slides-pdf` |
| Submit a chunk to Aristotle (after pip-install) | `python -m lambda_lab.lab.commands.eml submit <chunk-id>` |
| Inspect a chunk | `python -m lambda_lab.lab.commands.eml show <chunk-id>` |
| Look up a specific paper claim | `grep -r "paper_claim_<f>" lambda_lab/proofs/eml/2603_21852/lean_workspace/` |

## Key files for any follow-up

- `lambda_lab/proofs/eml/2603_21852/lean_workspace/EML/Framework/PaperClaims.lean`
  — the public scoreboard. `#check paper_claim_<f>` to inspect any
  primitive's seal.
- `lambda_lab/proofs/eml/2603_21852/lean_workspace/EML/Framework/KCounting.lean`
  — machine-checked tree sizes for all 36 primitives.
- `lambda_lab/proofs/eml/2603_21852/lean_workspace/EML/Framework/Sheffer.lean`
  — the EDL and −EML cousin scaffolding (post-Plan-A naming);
  hosts the 8 EDL + 5 −EML paper claims (Plans D and E).
- `lambda_lab/proofs/eml/2603_21852/notes/proof_structure.pdf` —
  11-page expository paper on the architecture. Branch-cut analysis
  in §10, open questions in §11.
- `paper/EML.tex` — the original paper source. Use when the user
  asks "what does the paper say about X" — search this rather than
  guessing.

## Who to mention by name

- The user is **Bartosz Naskręcki** (verify against
  `~/.claude/projects/<project-key>/memory/user_identity.md` after
  Step 3).
- The paper's author is **Andrzej Odrzywołek**. When writing anything
  the user might forward to him (an `AUTHOR_SUMMARY.md` revision, an
  email draft, etc.), be precise with paper-section citations:
  the open conjectures live in **paper §5** and **SI §1.5**, not in
  any §3.2.

## When in doubt

- Re-read `notes/proof_structure.pdf`. The paper-style writeup has a
  table of contents and is dense but accurate.
- The previous-session transcript and per-tool cache live at
  `~/claude-archives/eml-formalization-2026-05-08/session-state/`.
  You can `jq`-filter `transcript.jsonl.gz` if you need archaeological
  context, e.g.\ "what was the reasoning for deferring full-real-domain
  trig" — search for `branch` or `principal` keywords.

That's it. Welcome aboard.
