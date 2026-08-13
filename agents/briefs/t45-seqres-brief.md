# [L3.32-T45] The bridge's two sequence residues
tier: codex (default)

GOAL: `[T35]` reshaped the reduction and left the bridge's last named price as
two residues of one family: the induction's limit clause and the limit
membership the surviving direction needs. Both are the S-sequence definability.
Discharge them, or measure precisely why they cannot be.

CWD: /Users/alsg/Agentic/Bedrock
SCOPE (write): `src/L/Rud/Bridge.lagda.md` ONLY, plus
`_build/l3.32-t45-report.md`. Never `src/Everything.lagda.md`. **Do not touch
`src/L/Rud/SatTable.lagda.md`, `src/L/Ordinal/`, or any new module a sibling is
writing.**
SCOPE (read, in order): `_build/l3.32-t35-report.md` (**the two residues with
their exact statement types, and why the old proof of the surviving direction
was not what it claimed**); `src/L/Rud/Bridge.lagda.md` (the reshaped
reduction, the tower, and the two named statements); `src/L/Rud/LevelSigma.lagda.md`
(**the face at a rud carrier: this is the supplier the residues were designed
around**) and `_build/l3.32-t32-report.md`; `src/L/InitialSegment.lagda.md`,
`src/L/PairAtoms.lagda.md`; `src/L/Rud/SatSets.lagda.md` (the unconditional
switch, which the limit case's membership step consumes);
`_build/l3.31-r2lever-report.md` (the composed design and its four
machine-checked facts); `dev/LESSONS.md` (binding).

CONTENT: the two residues discharged from the delivered face at the rud
carrier plus the unconditional switch, so the bridge stands on nothing named.
**D-10 first, and it has teeth here**: this campaign has twice found a residue
whose recorded target was false or whose proof passed through a refuted object.
State each residue's target, check its truth at the intended generality, and
record any correction beside the original.

CONSTRAINTS: `GHCRTS=-M8g agda <file>`, ONE Agda process at a time (three
siblings run). Note that this chapter cold-checks slowly (about fifteen
minutes) and re-checks warm in seconds; budget accordingly and do not read a
slow cold check as a wall. STOP-LINE 350 non-blank in-fence lines of NEW
content. No postulate, no hole, no TERMINATING. Prose in both languages for
anything you change. Both linters clean. Do NOT run `make check`. No git.

RETURN (`_build/l3.32-t45-report.md`; final message = the summary): which
residues closed and which did not; for any that did not, the precise
obstruction and what it would cost; the chapter's before-and-after size; the
typecheck results; the D-10 record; and walls by LESSONS class.
