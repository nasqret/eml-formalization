# GPT Pro consult bundle — full-real-domain trig

## What's in here

| File | Purpose |
|---|---|
| [`PROMPT.md`](PROMPT.md) | The actual prompt for GPT Pro. Self-contained problem statement, three candidate paths, six specific sub-questions, desired output format. |
| [`CODE_EXCERPTS.md`](CODE_EXCERPTS.md) | All Lean source Pro needs: the fixed `eval?` rule, every macro (`mkExpℂ`, `mkLogℂ`, `mkAddℂ`, `mkMulℂ`, `mkSubℂ`, `mkDivℂ`) with current closure lemmas, all four narrow trig witnesses (`cosTermℂ`, `sinTermℂ`, `arctanTermℂ`, `tanCoreTermℂ`), the substitution machinery (Plan C foundation), and the relevant Mathlib facts. |

## How to use

1. Open ChatGPT (Pro tier, GPT-5 or whichever Pro model is current).
2. Start a new conversation.
3. Paste the **contents** of `PROMPT.md` first, then immediately follow
   with the **contents** of `CODE_EXCERPTS.md`. (Two messages in one
   conversation, in that order.)
4. Pro will respond with a recommendation. Keep the response on file
   under `RESPONSE.md` for reference; if Pro suggests follow-up
   experiments, those become the next session's work.

## Why this consult

`OPEN_QUESTIONS.md` flagged the GPT Pro consult as a prerequisite for
**Plan B** (full-real-domain trig via custom branch). Our own
investigation found that Plan B as initially framed is not directly
implementable (the EML grammar's eval rule hard-codes Mathlib's
`Complex.log` — see PROMPT §"The fixed eval rule"), and that the
practical options are:
- **Path A** — boundary lemmas + `2πi` shift tracking (~50–80 new lemmas)
- **Path B'** — Euler-form witness reshaping if any exists with `mkExpℂ`
  outermost
- **Path C** — multi-witness periodicity (foundation already built in
  `Framework/Complex/Subst.lean`)

We want Pro's independent read on which is cleanest. If Path B' has a
clever Euler-form trick we missed, that would close the gap with no
boundary arithmetic; if not, Path C is the conservative implementation
target.

## What we expect back

A markdown reply (≤ 3 pages):
1. Headline recommendation in one sentence.
2. Why that path beats the others (1–3 paragraphs).
3. Concrete proof sketches for the 2–3 hardest lemmas of the
   recommended path.
4. What to skip (if any of A/B/C is a dead end, plainly say so).
5. Open questions back to us if our framings are wrong.

## After the consult

Drop Pro's response into `RESPONSE.md` in this directory and notify
the assistant. The next coding session will take Pro's recommendation
as the new plan-of-record (or update `OPEN_QUESTIONS.md` if Pro
identifies a path we hadn't considered).
