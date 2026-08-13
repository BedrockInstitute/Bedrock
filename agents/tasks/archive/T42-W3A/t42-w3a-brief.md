# [L3.32-T42] W3 chapter A: the order-family table
tier: codex (default)

GOAL: W3, the internal order, is the wing's largest unbuilt item at 1.1-2.7k
naive. `[T19]` ran its gate and found every materializing step walled;
`[T22]` then broke all three walls and left a first-formulation prescription,
measured at sixty times on the decisive arm. Build W3's first chapter under
that prescription.

CWD: /Users/alsg/Agentic/Bedrock
SCOPE (write): ONE new master under `src/L/` plus
`_build/l3.32-t42-report.md`. Never `src/Everything.lagda.md`. **Do not touch
`src/L/Ordinal/`, `src/L/Rud/Bridge.lagda.md`, or any file a sibling owns.**
SCOPE (read, in order): `_build/l3.32-t22-report.md` (**THE PRESCRIPTION, and
it is binding**: never case on a transparent least-witness term, use a named
helper whose written type carries the equation; seal consumer aliases of the
least-witness machinery opaque at their birth site with unfolding read lemmas
beside them; state memberships and comparisons at the small index with
presentation implicits pinned; take ordinals as variables with ordinality a
separate hypothesis; re-home truncated search results into proposition-valued
goals; write every branch type that reaches a comparison or a search);
`_build/l3.32-t19-report.md` (the three walls and their exact shapes, so you
recognise them if they reappear); `_build/l3.32-t14-report.md` (**the chapter
split**: build chapter A, the per-level order and the family table, and NOT
chapters B or C); `src/L/Rud/Order.lagda.md` (the delivered producer order,
and how it survives: read its seals); `src/L/WellOrder/Base.lagda.md`;
`src/L/CardinalPredicates.lagda.md` and `src/L/LevelFormula.lagda.md` (recent
chapters whose decode discipline is the house style now);
`src/L/PairAtoms.lagda.md` and `src/V/Presentation.lagda.md` (use the kits);
`dev/STYLE-agda.md`, `dev/STYLE-i18n.md`, `dev/LESSONS.md` (binding, and note
R-38's appended rule, which is T22's finding in law form).

CONTENT: chapter A only, per T14's split: the per-level order and the family
table that assembles the levels into one order. Chapters B (the order formula
and its adequacy) and C (the initial-segment facts) are NOT in this batch.

**D-10 first, and here it has teeth:** T19 found that the recorded targets were
not establishable as stated at the concrete level. State each target, check its
truth at the intended generality BEFORE proving it, and record any correction
beside the original.

CONSTRAINTS: `GHCRTS=-M8g agda <file>`, ONE Agda process at a time (three
siblings run). STOP-LINE 400 non-blank in-fence lines; if chapter A cannot
close inside it, STOP and report what is proved and what remains. No postulate,
no hole, no TERMINATING. Trilingual prose (en and zh), no em dash. Both linters
clean. **New terms are NAMED in the report, never added to the glossary
yourself.** Do NOT run `make check`. No git. Never touch `.claude/`.

RETURN (`_build/l3.32-t42-report.md`; final message = the summary): the exports
and their types; the measured size against T14's chapter-A band; **whether
T22's prescription held under real construction, cure by cure**, which is the
question this batch answers for the rest of W3; any wall that reappeared and
what it cost; the D-10 record; new terms named; and the wiring note.
