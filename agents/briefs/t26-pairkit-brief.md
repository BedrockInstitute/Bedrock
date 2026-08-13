# [L3.32-T26] The shared pair kit (face batch 2's shared half)
tier: codex (default)

GOAL: `[T20]` measured the face's instantiation and found the split that makes
batch 2 affordable: 111 per-consumer lines over a ONE-TIME 197-line shared kit,
the pair atoms with their decodes and the component recovery, written once
generic in the carrier and reused by all three consumers (the wing's level
formula, the bridge's sigma at a rud carrier, the condensation crossing). Its
gate passed, so under D22 it is funded. Build the shared half now: it unblocks
all three consumers and is charged once.

CWD: /Users/alsg/Agentic/Bedrock
SCOPE (write): ONE new master under `src/L/` (name it by subject: it is the
pair-atom kit for formulas over a carrier, not "the face's helpers"), plus
`_build/l3.32-t26-report.md`. Never `src/Everything.lagda.md` (the orchestrator
wires it). Do not edit any existing master; if you need a `private` export,
NAME it in the report rather than un-privating it.
SCOPE (read, in order): `src/ProbeLevelFormula.agda` (THE TEMPLATE: its shared
kit is exactly what you productionize; its per-consumer part is NOT in this
batch), `_build/l3.32-t20-report.md` (the split, and which lines it counted as
shared), `src/L/InitialSegment.lagda.md` (the face whose telescope the kit
serves), `src/V/Presentation.lagda.md` (use it, do not re-derive fiber facts),
`src/L/Definability.lagda.md` and `src/FOL/Syntax.lagda.md` (the formula and
definability faces), `dev/STYLE-agda.md`, `dev/STYLE-i18n.md`, `dev/LESSONS.md`
(binding: P-h at full strength since the kit must stay carrier-generic, I-4,
I-5, R-35, R-36, R-38 including its NEW appended rule about casing on
transparent search terms, C-11, C-14).

CONTENT: the pair atoms with their decodes and the pair-component recovery,
generic in the carrier and in its transitivity, in the shapes the face's
telescope entries consume. NOT in this batch: any per-consumer instantiation.

CONSTRAINTS: `GHCRTS=-M8g agda <file>`, ONE Agda process at a time (three
sibling probes are running). STOP-LINE 260 non-blank in-fence lines (T20
measured 193 code; the margin is for prose-driven restructuring, not scope
growth). No postulate, no hole, no TERMINATING. Trilingual prose (en and zh),
no em dash, English only inside fences. `lint-agda.py` and `lint-prose.py`
clean on your file. Do NOT run `make check`. No git. Never touch `.claude/`.

RETURN (`_build/l3.32-t26-report.md`; final message = the summary): the exports
with their types; the measured size against T20's 193; confirmation that every
export is carrier-generic (a kit that silently fixes a carrier defeats the
point); what the three consumers still owe; the walls by LESSONS class; and the
fact that the file needs `Everything` wiring.
