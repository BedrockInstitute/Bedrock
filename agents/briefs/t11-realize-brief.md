# [L3.32-T11] The Realize-strip compile gate (confirms about 1,076 dead lines)
tier: codex (default)

GOAL: confirm that `L.Rud.Realize` (789 lines) and `L.Rud.Switch`'s
Realize-dependent modules (about 287: `Bs`, `Ev`, `Rl`, `Closure`,
`WalkCon`, `LimitSwitch`) are dead weight under the ruled configuration.
`_build/l3.32-t7-report.md` established by import analysis that `Bridge`
consumes only `Switch`'s `Descr` and `Hops`, that those two modules contain
zero references to any Realize machinery, and that the comprehension engine
was re-pointed to `SatSets`'s `full-switch-⊇` long ago. Its Gate 3 is the
compile test that turns that analysis into a fact.

CWD: /Users/alsg/Agentic/Bedrock
SCOPE (write): `_build/l3.32-t11-report.md` ONLY, plus TEMPORARY edits to
`src/L/Rud/Switch.lagda.md` that you MUST restore exactly (see below).
SCOPE (read): `_build/l3.32-t7-report.md` (the row and Gate 3),
`src/L/Rud/Switch.lagda.md`, `src/L/Rud/Realize.lagda.md`,
`src/L/Rud/Bridge.lagda.md` (READ-ONLY: a sibling recently edited it),
`src/L/Rud/SatSets.lagda.md`, `src/Everything.lagda.md` (READ-ONLY, never
write it).

THE TEST, in this order:
1. **Copy `src/L/Rud/Switch.lagda.md` to your scratch area FIRST.** You will
   restore from that copy, by writing the bytes back. **Do not use any git
   command to restore** (a sibling agent is editing other files in this same
   working tree and a git checkout would clobber its work).
2. Strip from `Switch` the Realize-dependent modules named above and the
   `open import L.Rud.Realize` line.
3. Typecheck `Switch`, then `Bridge`, then `SatTable` (the consumers) at
   `GHCRTS=-M8g agda <file>`, ONE process at a time.
4. GREEN means the strip is sound and about 1,076 lines are confirmed dead.
   RED means a consumed export hides in the stripped region: NAME the export,
   its consumer and the line, since that is the finding.
5. **Restore `Switch.lagda.md` byte for byte from your copy and verify by
   typechecking it once more.** The working tree must end exactly as it
   began. Say in your report that you verified this.

CONSTRAINTS: `GHCRTS=-M8g agda <file>`, ONE agda process at a time (three
siblings run concurrently). No git commands at all. Never touch `.claude/`,
`Everything.lagda.md`, generated files, or any file outside `src/L/Rud/Switch
.lagda.md`. `dev/LESSONS.md` binds.

RETURN (`_build/l3.32-t11-report.md`; final message = compressed verdict):
GREEN or RED with the three typecheck results and their wall times; the
measured line counts of what was stripped (non-blank in-fence); on RED the
hidden consumer named precisely; and confirmation that the working tree was
restored and re-verified.
