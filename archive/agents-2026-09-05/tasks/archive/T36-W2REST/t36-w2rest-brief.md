# [L3.32-T36] The level formula's remaining two clauses
tier: codex (default)

GOAL: `[T30]` delivered the level formula at 261 lines and stopped at its
stop-line with two clauses of the tower story outstanding, both already
measured or designed: the ordinal domain bound, WRITTEN AND TYPECHECKED at
about 160 lines in its intermediate build and then cut, and the limit clause,
designed at 140-190 and never typechecked. Deliver both, so W2 is a complete
object rather than a partial one.

CWD: /Users/alsg/Agentic/Bedrock
SCOPE (write): `src/L/LevelFormula.lagda.md` ONLY, plus
`_build/l3.32-t36-report.md`. Never `src/Everything.lagda.md`. **Do not touch
`src/L/Rud/`, `src/L/Ordinal/`, or `src/L/Condensation.lagda.md` (siblings own
those).**
SCOPE (read, in order): `_build/l3.32-t30-report.md` (**the per-piece table,
the two outstanding clauses, and what each was measured or designed at**);
`src/L/LevelFormula.lagda.md` itself (the delivered three clauses and their
decode discipline, which the two new ones follow); `src/L/InitialSegment.lagda.md`
and `src/L/PairAtoms.lagda.md`; `src/L/Rud/LevelSigma.lagda.md` READ-ONLY (the
sibling consumer at the other carrier: T32 reports the omitted clauses are
carrier-independent, so whatever you build here serves it too, and saying
precisely how is part of the report); `src/L/Constructible.lagda.md`,
`src/L/Ordinal.lagda.md`, `src/L/Ordinal/Stages.lagda.md`; `dev/LESSONS.md`
(binding; T30 hit I-5 and R-38's no-`with` rule and applied both preemptively).

CONTENT: the ordinal domain bound and the limit clause, with their decodes, in
the chapter's established style, so the five-clause tower story is complete and
the face's `Approx` entry at this carrier is the full story rather than the
pairhood fragment.

CONSTRAINTS: `GHCRTS=-M8g agda <file>`, ONE Agda process at a time (three
siblings run). STOP-LINE 400 non-blank in-fence lines of NEW content (T30's
measurement plus its design is about 300-350; the margin is for the seam). If a
clause cannot close, STOP and report what it needs. No postulate, no hole, no
TERMINATING. Prose in both languages for the new sections. Both linters clean.
Do NOT run `make check`. No git. Never touch `.claude/`.

RETURN (`_build/l3.32-t36-report.md`; final message = the summary): the
before-and-after size; each clause's measured cost against T30's 160 and
140-190; whether the five-clause story is now complete; exactly what the rud
consumer can reuse; the walls by LESSONS class; and W2's final funded number.
