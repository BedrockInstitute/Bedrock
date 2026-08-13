# [L3.32-T43] Where does the counting actually call the square law?
tier: codex (default)

GOAL: `[T31]` delivered the square law at the finite base, the successor step
and the first limit, and hit a real obstruction above: the least-of search
gives equinumerosity only as a truncated existence and no canonical bijection
makes it honest. Before anyone attacks that obstruction, settle whether the
GCH argument ever needs the law where it fails. **If the counting only ever
calls it at initial ordinals, the wall is not on the critical path at all.**

CWD: /Users/alsg/Agentic/Bedrock
SCOPE (write): `_build/l3.32-t43-report.md` ONLY (deliver the full report as
your final message too). Zero Agda. Read-only everywhere else.
SCOPE (read): `_build/l3.32-t31-report.md` (**the obstruction, exactly**: what
is discharged, what is named, and at which ordinals); `src/L/Ordinal/SquareLaw
.lagda.md` and `src/L/Ordinal/Pairing.lagda.md` (the consumer's hypothesis
shape); `_build/literature/dev2.txt` Devlin II.5, especially 5.4 and 5.6 (**the
counting argument, step by step**: at which ordinals does it multiply, and are
they initial?); `_build/literature/jech13.txt`; `_build/l3.32-t5-report.md` and
`_build/l3.32-t18-report.md` (the W7 chapter split and the minimal vocabulary);
`_build/l3.32-t40-report.md` (the hull, whose `sett` index the count runs on);
`src/FOL/Count.lagda.md`, `src/L/CardinalPredicates.lagda.md`.

THE QUESTIONS:
1. Trace the classical counting from the hull to the GCH conclusion and list
   EVERY place a product or a square is taken, with the ordinal it is taken at
   and whether that ordinal is initial. Cite lines.
2. At the places that matter, is the truncated form of equinumerosity enough?
   The obstruction is only about extracting an untruncated bijection; a
   consumer whose goal is proposition-valued can absorb the truncation. Say
   for each call site whether its goal is proposition-valued.
3. If some call site genuinely needs the law at a non-initial ordinal, name it
   precisely and say what the alternatives cost: a choice principle from
   `src/Base/Choice.lagda.md` (and what that does to the tree's postulate-free
   claim), a restatement of the bound in truncated form, or a different route
   to the counting.
4. The verdict: is T31's obstruction on the critical path to `L ⊨ GCH`, yes or
   no, and what is the cheapest next action either way.

CONSTRAINTS: read-only; zero Agda; no git. Corpus citations `file:line` for
every classical claim, tree citations for every code claim. Adversarial
honesty: "the wall is on the path" is a valid and important answer. Never touch
`.claude/`.
