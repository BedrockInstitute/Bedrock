# [L3.32-T34] The DefInJ and SatTable re-type
tier: codex (default)

GOAL: `[T4]` walked these two chapters export by export and marked each
RETAINED, RE-TYPED or DEAD under the reshaped bridge; `[T25]` then measured the
re-stated interface at 52 lines and confirmed which parts survive; `[T28]` left
a template stating the target shape precisely. Execute the re-type: about 100
to 160 lines survive of the current 401, a standing reduction of about 141.

CWD: /Users/alsg/Agentic/Bedrock
SCOPE (write): `src/L/Rud/DefInJ.lagda.md` and `src/L/Rud/SatTable.lagda.md`
ONLY, plus `_build/l3.32-t34-report.md`. Never `src/Everything.lagda.md`.
**Do not touch `src/L/Ordinal/`, `src/L/LevelFormula.lagda.md`, or any other
`src/L/Rud/` file (siblings own those).**
SCOPE (read, in order): `_build/l3.32-t4-report.md` section 2 (**THE
SPECIFICATION**: the export-by-export table with its RETAINED, RE-TYPED and
DEAD verdicts and the reason for each); `_build/templates/CodeSetBlock.lagda.md`
(T28's template: it states the successor obligation precisely, which is the
shape you re-type toward); `_build/l3.32-t25-report.md` (what the re-stated
interface is and what it consumes, and the finding that the coded machinery
STAYS); `_build/l3.31-p1-report.md` sections 3 and 4 (why `BlockPow` becomes
`BlockPowLim`, and the eight-line proof that the corrected target is already
met); the two chapters themselves; `dev/LESSONS.md` (binding).

THE RE-TYPE: `BlockPow` gains its limit hypothesis and becomes `BlockPowLim`;
the exports T4 marked DEAD go with their prose; the surviving chain is re-typed
around them. **The false per-level identification is already recorded as false
in `Bridge`, so nothing here may reintroduce it.** Every deletion takes its
prose with it, in both languages, and no orphaned prose may remain.

METHOD: C-10 binds (mechanical multi-site edits are scripted, asserted and
typechecked). After the re-type, typecheck `DefInJ`, then `SatTable`, one Agda
process at a time. Both must be green before you report. If the chain cannot
close, say exactly where and stop rather than inventing a bridge.

CONSTRAINTS: `GHCRTS=-M8g agda <file>`, ONE Agda process at a time. No
postulate, no hole, no TERMINATING. Both linters clean on both files. Do NOT
run `make check`. No git. Never touch `.claude/`.

RETURN (`_build/l3.32-t34-report.md`; final message = the summary): the
before-and-after sizes of both chapters against T4's predicted 100-160
survivors; which exports died and which were re-typed; the two typecheck
results; the prose sections rewritten or deleted; and anything T4 marked DEAD
that turned out to be load-bearing, which would be the report's most important
finding.
