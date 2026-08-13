# [L3.32-T40] The definable hull (W7's other half)
tier: codex (default)

GOAL: W7 splits into the counting side and the hull side. The counting side is
delivered (`FOL.Count`) and its predicates too (`L.CardinalPredicates`). The
hull side is scoped but unbuilt: `[T5]` priced elementarity with the
Tarski-Vaught criterion at 0.15-0.30k and the definable hull at 0.20-0.45k, and
flagged that the delivered reflection machinery's shape may force a different
formulation from the textbook's. Build it, and settle that flag.

CWD: /Users/alsg/Agentic/Bedrock
SCOPE (write): ONE new master under `src/L/` plus
`_build/l3.32-t40-report.md`. Never `src/Everything.lagda.md`. **Do not touch
`src/L/Ordinal/` or `src/L/Rud/Bridge.lagda.md` (siblings own those).**
SCOPE (read, in order): `_build/l3.32-t5-report.md` (**the scoping**: the
chapter split, the classical path with its citations, and the flagged
formulation risk, namely that the delivered reflection puts the formula outside
the quantifier so it cannot be iterated into a hull); `_build/literature/dev2.txt`
around Devlin II.5 sections 5.1 to 5.4 (the classical statements; cite what you
follow); `src/FOL/` (the reflection machinery as delivered, and
`FOL.Absoluteness`); `src/L/Condensation.lagda.md` (the consumer of the hull,
and the discipline it established); `src/L/CardinalPredicates.lagda.md` (NEW:
the predicates the counting side will pair with); `src/L/Rud/Order.lagda.md`
(the least-witness the hull's choice of witnesses uses, and note R-38's
appended rule about casing on it); `dev/LESSONS.md` (binding).

CONTENT: elementarity with the Tarski-Vaught criterion, and the definable hull
as the smallest elementary substructure containing a given set, in the shape
condensation consumes. **T5's flagged risk is the report's most important
question**: does the delivered reflection's shape force a different formulation,
and if so, what is it and what does it cost? Answer by building, not by
arguing.

CONSTRAINTS: `GHCRTS=-M8g agda <file>`, ONE Agda process at a time (two
siblings run). STOP-LINE 400 non-blank in-fence lines; if the criterion or the
hull cannot close inside it, STOP and report precisely what remains. D-10 first
on each target. No postulate, no hole, no TERMINATING. Trilingual prose (en and
zh), no em dash. Both linters clean. **New terms are NAMED in the report, never
added to the glossary yourself.** Do NOT run `make check`. No git. Never touch
`.claude/`.

RETURN (`_build/l3.32-t40-report.md`; final message = the summary): the exports
and their types; the measured size against T5's 0.35-0.75k for the two rows;
the verdict on the flagged formulation risk; what remains of W7's hull side;
the walls by LESSONS class; new terms named; and the wiring note.
