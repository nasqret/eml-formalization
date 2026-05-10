# Chunks — per-statement decomposition

Numbered subdirectories, each containing one atomic theorem statement
plus (where applicable) the Aristotle-returned proof.

## Numbering scheme

| Range | Topic |
|---|---|
| `001`–`068` | Original Round 1: per-primitive EML witnesses (atoms, real unaries, hyperbolic, binaries, trig). |
| `069` | Universal minimality (paper §5 conjecture; two concrete corollaries proved). |
| `070` | Main completeness wrap-up. |
| `071`–`083` | Path C′ — full-real-domain trig (post-submission). |
| `084`–`089` | Plan D / Plan E continuation chunks (Sheffer cousins). |

## Per-chunk file layout

```
<chunk-id>/
├── chunk.md        (human-readable: target, motivation, dependencies)
├── meta.json       (machine-readable metadata; see schema below)
├── target.lean     (theorem statement with `sorry`)
└── result.lean     (Aristotle-returned proof, if Aristotle-sealed)
```

**`result.lean` is conditional.** It exists when the chunk was sealed
by submitting `target.lean` to Aristotle and capturing the response.
Hand-coded chunks (where the witness was constructed directly in the
`EML/Framework/` layer) do **not** have a `result.lean` — the proof
lives in the framework module instead, with a docstring citing the
chunk number for traceability.

## `meta.json` schema

```json
{
  "id": "<chunk-id>",
  "title_en": "...",
  "title_pl": "...",                     // optional, if Polish title differs
  "paper_section": "§Sup. Table S2 step N",
  "paper_quote": "verbatim quote from paper",
  "informal_en": "1-line summary",
  "informal_pl": "...",                   // optional
  "kind": "theorem" | "theorem_pack" | "definition",
  "difficulty": 1-5,                      // subjective; 1=trivial, 5=research-grade
  "lean_imports": ["Mathlib", ...],
  "lean_target_signature": "theorem ... : ...",
  "depends_on": ["<earlier-chunk-id>", ...],
  "status": "pending" | "in_progress" | "complete" | "complete_partial",
  "aristotle_project_id": "<uuid>" | null,
  "submitted_at": "ISO-8601" | null,
  "completed_at": "ISO-8601" | null,
  "notes": "free-form annotations"
}
```

## Status field semantics

| Value | Meaning |
|---|---|
| `pending` | Chunk created, no submission attempted yet. |
| `in_progress` | Aristotle job submitted; awaiting result. |
| `complete` | Sealed (either by Aristotle's returned proof or by hand-coded lifting into the framework). |
| `complete_partial` | Some sub-theorems sealed, others left as `sorry` with analytical justification (typical for chunks attempting paper-open conjectures). |

## Submitting a chunk to Aristotle

```bash
cd <chunk-id>
aristotle submit "Prove <target>. <strategy hints>" --project-dir .
# returns a project_id; record it in meta.json
```

To poll / fetch:

```bash
aristotle list                                  # all your projects
aristotle result <project-id> --destination /tmp/result.tar.gz
tar -xzf /tmp/result.tar.gz -C /tmp/result/
cp /tmp/result/project_aristotle/target.lean ./result.lean
# then update meta.json: status=complete, aristotle_project_id=<uuid>,
# completed_at=<timestamp>
```

## Aristotle-vs-hand chunk reference list

| Chunk | Sealed by | Notes |
|---|---|---|
| `029_eml_minimality` | Hand | Two concrete corollaries proved; full universal claim is paper-open. No `result.lean`. |
| `034_emlterm_for_pi` | Hand | Closed numeric/imaginary constants packaged in `Realization.lean`. |
| `035_emlterm_for_i` | Hand | Same. |
| `077_atan_arg_in_ioo` | Aristotle | Pure Mathlib aux, ~6 min. |
| `079_tan_period_reduction` | Aristotle | Pure Mathlib aux, ~13 min. |
| `075_sin_via_cos` | Aristotle (with framework axioms) | ~21 min; lifted into `Periodicity.lean`. |
| `078_arctan_via_arcsin` | Aristotle (with framework axioms) | ~21 min; lifted. |
| `080_tan_full` | Aristotle (with framework axioms) | ~17 min; lifted. |
| `084_edl_atoms_pilot` | Aristotle | 4 trivial EDL atoms, ~28 min. |
| `085_edl_atoms_constants` | Aristotle (partial) | D8 / log x sealed; D5/D6/D7 conjecturally unreachable per Schanuel. |
| `086_edl_div` | Aristotle | D9 / division; Aristotle even corrected the statement. |
| `087_edl_compositions` | Aristotle | D10 / exp(exp x), D11 / log(log x). |
| `088_neg_eml_pilot` | Aristotle | Plan E E1/E2/E3 over EReal grammar. |
| `089_edl_wide_search` | Aristotle (partial) | D14/D15 trivial; D16/D17 unreachable + analyzed. |

See [`AUDIT_REPORT.md`](../../../../AUDIT_REPORT.md) for repo-wide hygiene status.
