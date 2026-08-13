# [L3.32-T23] The bridge's remaining rows, gated
tier: codex (default)

GOAL: D22. The wing-time bridge is funded at 0.60-1.50k naive ex-P2 on four
machine-checked facts (`_build/l3.31-r2lever-report.md`), but its largest row
that is NOT yet measured is the limit case's assembly and the induction's
reshape. The face chapter now exists (`src/L/InitialSegment.lagda.md`) and its
instantiation cost is measured (`_build/l3.32-t20-report.md`), so the bridge's
sigma row is already priced; what remains survey-class is the INDEX TOWER, the
reshaped induction, and the limit-case assembly. Measure them.

CWD: /Users/alsg/Agentic/Bedrock
SCOPE (write): `src/ProbeBridgeRows.agda` (untracked) and
`_build/l3.32-t23-report.md` ONLY. No master, never `Everything`.
SCOPE (read, in order): `_build/l3.31-r2lever-report.md` (the composed design
and its four facts: the closed-form index tower, the element-level limit
statement, the direct membership step, and the fresh face), `_build/p2-fork-recon.md`
section 2.0 (the existential statement the induction proves and its three
clauses), `src/L/Rud/Bridge.lagda.md` (the DELIVERED reduction whose reshape is
being priced: read its telescope and its three clauses), `src/L/Rud/OrdBlocks.lagda.md`
(the extension family the tower is built from), `src/L/Rud/SatSets.lagda.md`
(the unconditional switch the limit case consumes), `src/L/InitialSegment.lagda.md`
and `_build/l3.32-t20-report.md` (the face and what instantiating it costs),
`dev/LESSONS.md` (binding; and note R-38's new appended rule about casing on
transparent search terms).

THE MINIATURE: the index tower in closed form with the two facts the induction
needs of it, and the reshaped induction's SUCCESSOR clause end to end at that
tower (the limit clause is the expensive one and may be stated and left, but
say so). D-10 first on every target. Measure the reshape against the delivered
reduction's own size, since the question is a DELTA, not an absolute.

CONSTRAINTS: `GHCRTS=-M8g agda <file>`, ONE Agda process at a time (siblings
run). STOP-LINE 350 probe lines. No postulate, no hole, no TERMINATING. C-6
controls. No git. Never touch `.claude/`.

RETURN (`_build/l3.32-t23-report.md`; final message = compressed verdict):
per-piece measurements; **what the bridge's non-face rows should be funded at
in both calibers**, against R2L's 0.60-1.50k ex-P2; which rows move to the
cheaper class; and the walls by LESSONS class.
