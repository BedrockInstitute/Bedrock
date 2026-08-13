# [L3.32-T35] The reshaped reduction (the bridge's critical-path deliverable)
tier: codex (default)

GOAL: `[T34]` re-typed the bridge's two supply chapters and stopped where it
had to: the landing module cannot close over a `Reduce` that still exposes the
per-level identification this campaign proved FALSE. `[T23]` measured the
replacement: the closed-form index tower at 141 lines with both facts the
induction needs, and the reshaped induction at 48 lines, which is 0.35 times
the delivered reduction it replaces. `[T32]` has since delivered the face at a
rud carrier, which is the limit clause's supplier. Build the reshaped
reduction.

CWD: /Users/alsg/Agentic/Bedrock
SCOPE (write): `src/L/Rud/Bridge.lagda.md` ONLY, plus
`_build/l3.32-t35-report.md`. Never `src/Everything.lagda.md`. **Do not touch
`src/L/LevelFormula.lagda.md`, `src/L/Ordinal/`, or any new module a sibling
may be writing.** `src/L/Rud/SatTable.lagda.md` is READ-ONLY for you.
SCOPE (read, in order): `_build/l3.32-t23-report.md` (**THE MEASUREMENT AND
THE DESIGN**: the closed-form tower, its two facts, the six-line successor
clause, and what it left stated-and-unbuilt); `src/ProbeBridgeRows.agda` if it
still exists, else the report; `_build/p2-fork-recon.md` section 2.0 (the
existential statement the induction proves and its three clauses);
`src/L/Rud/Bridge.lagda.md` (the delivered reduction being replaced, and the
already-recorded falsity of the per-level identification, which nothing may
reintroduce); `src/L/Rud/LevelSigma.lagda.md` (NEW: the face at the rud
carrier, the limit clause's supplier); `src/L/Rud/SatTable.lagda.md` (the
re-typed successor supply, `BlockPowLim` and the re-stated relation);
`src/L/Rud/SatSets.lagda.md` (`full-switch-⊇`); `src/L/Rud/OrdBlocks.lagda.md`;
`dev/LESSONS.md` (binding; D-8 fired on the tower's monotonicity in T23 and its
conditioned kit is part of the design).

CONTENT: the index tower and the reshaped induction, replacing the delivered
`Reduce`'s three clauses. The successor clause is T23's six-line composition.
The LIMIT clause is the expensive one T23 stated and left; build it if it fits,
and if it does not, deliver everything else and report precisely what the limit
clause needs, since that is then the bridge's last named residue.
**The false per-level identification stays recorded as false; the surviving
unconditional direction stays unconditional.**

METHOD: C-10 binds. Typecheck `Bridge`, then `SatTable`, then `StepInL`, one
Agda process at a time; all must be green before you report. Prose is part of
the job in both languages: the chapter's narrative describes a reduction that
is being replaced.

CONSTRAINTS: `GHCRTS=-M8g agda <file>`, ONE Agda process at a time (three
siblings run). STOP-LINE 400 non-blank in-fence lines of NEW content. No
postulate, no hole, no TERMINATING. Both linters clean. Do NOT run `make
check`. No git. Never touch `.claude/`.

RETURN (`_build/l3.32-t35-report.md`; final message = the summary): the
chapter's before-and-after size; whether the limit clause closed and if not
what it needs; the three typecheck results; whether `SatTable`'s landing can
now close, which is the question this unblocks; the walls by LESSONS class; and
the prose rewritten.
