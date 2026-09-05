# [L3.32-T46] The cardinal chapter's counting side
tier: codex (default)

GOAL: W7's long pole is the cardinal chapter, and its two halves are now
supplied: the count layer is delivered, the predicates are delivered under
their binding design rulings, and the hull's own index is what the count runs
on. Build the counting side, and **stop exactly where it meets the square law**,
whose status above the first limit is open and is being checked in parallel.

CWD: /Users/alsg/Agentic/Bedrock
SCOPE (write): ONE new master under `src/L/` plus `_build/l3.32-t46-report.md`.
Never `src/Everything.lagda.md`. **Do not touch `src/L/Ordinal/`,
`src/L/Rud/`, or `src/L/Hull.lagda.md` (siblings own those or they are
settled).**
SCOPE (read, in order): `_build/l3.32-t5-report.md` (the W7 chapter split and
the cardinal row); `_build/l3.32-t18-report.md` (**the binding design rulings**:
equinumerosity is the bijection, the predicates are general, and the named list
of what defers); `src/L/CardinalPredicates.lagda.md` (the predicates and their
certificates, and its recorded correction that the inner and ambient readings
are NOT equivalent for equinumerosity); `src/FOL/Count.lagda.md` (**the count
your argument runs on**); `src/L/Hull.lagda.md` (the hull, whose `sett` index
the count applies to, per T40's closing note); `src/L/Ordinal/SquareLaw.lagda.md`
and `_build/l3.32-t31-report.md` (**what is available and what is not**: the
law holds at the finite base, the successor step and the first limit);
`_build/literature/dev2.txt` Devlin 5.4; `dev/LESSONS.md` (binding).

CONTENT: the counting from the hull's index to a cardinality bound, using the
delivered count and predicates. **Where the argument needs the square law at an
ordinal where it is not delivered, STOP AND NAME THE CALL SITE with its exact
ordinal and its goal type** (whether the goal is proposition-valued matters:
the obstruction is only about extracting an untruncated bijection). Do not
invent a workaround and do not postulate.

CONSTRAINTS: `GHCRTS=-M8g agda <file>`, ONE Agda process at a time (three
siblings run). STOP-LINE 400 non-blank in-fence lines. D-10 first on every
target. No postulate, no hole, no TERMINATING. Trilingual prose (en and zh), no
em dash. Both linters clean. **New terms NAMED in the report.** Do NOT run
`make check`. No git. Never touch `.claude/`.

RETURN (`_build/l3.32-t46-report.md`; final message = the summary): the exports
and types; the measured size against T5's cardinal row; **every call site of
the square law with its ordinal and goal type**, which is the datum the
parallel scope check needs; the D-10 record; walls by LESSONS class; and the
wiring note.
