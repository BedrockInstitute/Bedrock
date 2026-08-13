# [L3.32-T47] The truncated square law at the initial ordinals
tier: codex (default)

GOAL: `[T31]` hit a real obstruction (no canonical bijection to make the
least-of witness honest) and `[T43]` found the way past it: **do not fund the
extraction; truncate the bounds instead.** Every consumer goal in the counting
is a proposition, so the truncation is free on the consumer side, and the
order core's own induction hypothesis can be consumed truncated because every
elimination of it inside the core lands in the empty type. Deliver the
truncated law at the initial ordinals from omega up.

CWD: /Users/alsg/Agentic/Bedrock
SCOPE (write): `src/L/Ordinal/SquareLaw.lagda.md` **ADDITIVELY ONLY** (a new
module at the end; do NOT restructure or rename anything that exists, because
a sibling agent is READING this file right now and additive change is what
keeps that safe), plus `_build/l3.32-t47-report.md`. Never
`src/Everything.lagda.md`. **Do not touch `src/L/Ordinal/Pairing.lagda.md`,
`src/L/Rud/`, or any new module a sibling is writing**; the re-pointing of the
pairing chapter is the orchestrator's, afterwards.
SCOPE (read, in order): `_build/l3.32-t43-report.md` section 4 (**THE PLAN, and
it is the mandate**: truncate the bounds, consume the core's hypothesis
truncated, then run the induction over ordinals discharging the core's four
hypotheses at each cardinal, with the no-injection-down piece kept at the index
level as T31's own recorded cure); `_build/l3.32-t31-report.md` sections 3 and
5 (what is delivered, what the walls were, and the index-level cure);
`src/L/Ordinal/SquareLaw.lagda.md` (the delivered core, the finite base, the
cardinal, the shift, the successor step, and the base at the first limit);
`_build/l3.32-t21-report.md` sections 3 and 4 (the route and its pricing);
`src/L/Ordinal/Pairing.lagda.md` READ-ONLY (the consumer's hypothesis shape,
which the truncated form must still be able to feed); `dev/LESSONS.md`
(binding; T31 recorded a heap exhaustion in the core's instantiation, so keep
heavy objects at variables and seal at birth).

CONTENT: the truncated square law at every initial ordinal from the first limit
up, by induction over the ordinals, discharging the core's four hypotheses at
each cardinal. **State clearly, in the chapter's own prose, what the truncated
form does and does not give**, since the honest untruncated equivalence remains
unavailable and a reader must not mistake one for the other.

**D-10 first:** T43's plan rests on the claim that every elimination of the
core's induction hypothesis lands in a proposition. VERIFY that against the
delivered core before building on it, and if it is false anywhere, say so and
stop rather than working around it.

CONSTRAINTS: `GHCRTS=-M8g agda <file>`, ONE Agda process at a time (three
siblings run). This chapter cold-checks in about ten minutes; do not read that
as a wall. STOP-LINE 300 non-blank in-fence lines of NEW content. No postulate,
no hole, no TERMINATING. Prose in both languages for the new section. Both
linters clean. Do NOT run `make check`. No git. Never touch `.claude/`.

RETURN (`_build/l3.32-t47-report.md`; final message = the summary): the new
exports and their types; whether the pairing chapter's hypothesis can now be
fed in truncated form and at which ordinals; the D-10 verification of T43's
load-bearing claim; the measured size against T21's 130-220 for this layer;
walls by LESSONS class; and what remains before the counting can run.
