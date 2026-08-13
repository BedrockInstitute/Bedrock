# [L3.32-T32] The bridge's sigma at a rud carrier (the face's second consumer)
tier: codex (default)

GOAL: the face has three consumers; `[T30]` built the first and left the
recipe. Build the second: the bridge's sigma at a rud carrier, which is the row
`[R2L]` priced at 0.15-0.40k and `[T20]` measured the shared half of. This is
the row that makes the wing-time bridge a corollary rather than a rebuild.

CWD: /Users/alsg/Agentic/Bedrock
SCOPE (write): ONE new master under `src/L/Rud/` plus
`_build/l3.32-t32-report.md`. Never `src/Everything.lagda.md`. Do not edit any
existing master. **Do not touch `src/L/Ordinal/` (a sibling is building there),
`src/L/LevelFormula.lagda.md`, `src/L/Rud/DefInJ.lagda.md` or
`src/L/Rud/SatTable.lagda.md` (siblings own those).**
SCOPE (read, in order): `src/L/LevelFormula.lagda.md` (**THE RECIPE**: the
first consumer, its instantiation discipline and its decode style are what you
follow at a different carrier), `_build/l3.32-t30-report.md` (what each piece
cost and what it says the other consumers can reuse),
`src/L/InitialSegment.lagda.md` and `src/L/PairAtoms.lagda.md` (the face and
the kit: import, never re-derive), `_build/l3.31-r2lever-report.md` (why the
bridge's limit case wants this and what `full-switch-⊇` supplies),
`_build/l3.32-t23-report.md` (the reshaped induction that consumes it),
`src/L/Rud/SatSets.lagda.md`, `src/L/Rud/Hierarchy.lagda.md`,
`src/L/Rud/OrdBlocks.lagda.md`, `dev/STYLE-agda.md`, `dev/STYLE-i18n.md`,
`dev/LESSONS.md` (binding; R-38's no-`with` append and I-5 both fired for T30).

CONTENT: the face instantiated at a rud carrier, with its four telescope
entries supplied there and the consumer's two-way read-off obtained. T30's
per-piece table is your estimate: if a piece costs materially more at this
carrier than at the tower, that difference is the report's most valuable
number, so measure it piece by piece the same way.

CONSTRAINTS: `GHCRTS=-M8g agda <file>`, ONE Agda process at a time (three
siblings run). STOP-LINE 300 non-blank in-fence lines; if a piece pushes past
it, STOP and report what is delivered and what remains, as T30 did. No
postulate, no hole, no TERMINATING. Trilingual prose (en and zh), no em dash.
Both linters clean. Do NOT run `make check`. No git. Never touch `.claude/`.

RETURN (`_build/l3.32-t32-report.md`; final message = the summary): the exports
and their types; the per-piece table against T30's; what the rud carrier cost
that the tower did not, or the reverse; whether the 111-per-consumer rate
holds; the walls by LESSONS class; and the `Everything` wiring note.
