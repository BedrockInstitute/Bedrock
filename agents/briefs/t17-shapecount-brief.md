# [L3.32-T17] The shape-count probe (W7's un-itemized piece)
tier: codex (default)

GOAL: `[T9]` found that W7's cardinal payoff needs a piece nobody had
itemized: a SHAPE-COUNT, an injection of the constant-free formulas of each
arity into a natural-number-valued code, and thence into an infinite
ordinal's index. Every coding in this tree is SET-valued, so this is new
ground. Probe whether it is cheap or a chapter, before it becomes W7's third
up-price.

CWD: /Users/alsg/Agentic/Bedrock
SCOPE (write): `src/ProbeShapeCount.agda` (untracked) and
`_build/l3.32-t17-report.md` ONLY. No master, never `Everything`.
SCOPE (read): `_build/l3.32-t9-report.md` (target T3, where the piece is
named and why the probe stopped), `src/ProbeCard.agda` (the shape type it
needs: `Formula (⊥* {ℓ}) k`, and the exact place `shape↪` is consumed),
`src/FOL/Syntax.lagda.md` (the formula type, its twelve constructors and its
term type), `src/FOL/Coding.lagda.md` and `src/V/Coding.lagda.md` (the
delivered SET-valued codings: read them for the pattern and for what they
prove, then note that the target here is different in kind),
`dev/LESSONS.md` (binding: D-10, I-5, R-35, C-6).

THE TARGET: for each arity `k`, an injection from the constant-free formulas
of arity `k` into `ℕ`, with injectivity proved, in the shape `ProbeCard`'s
`shape↪` consumes. Then say what it takes to land that in an infinite
ordinal's index (the numerals' injection is delivered; check it).
D-10 FIRST: is the target TRUE at the delivered syntax? A formula type with
a term subtype and a truncation-free constructor set should be countable,
but check rather than assume, and say what the check rests on.

CONSTRAINTS: `GHCRTS=-M8g agda <file>`, ONE Agda process at a time. STOP-LINE
250 probe lines. No postulate, no hole, no TERMINATING. C-6 controls on any
refutation-shaped claim. Wall protocol per the law book. No git. Never touch
`.claude/`.

RETURN (`_build/l3.32-t17-report.md`; final message = compressed verdict):
GO or NO-GO with the measured size; the D-10 answer; whether it is a
subroutine or a chapter; the extrapolation to W7's cardinal row; and the
walls by LESSONS class.
