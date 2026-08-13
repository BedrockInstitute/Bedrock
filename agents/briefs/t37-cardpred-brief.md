# [L3.32-T37] The cardinal predicates, built generally
tier: codex (default)

GOAL: W7's cardinal chapter rests on three internal predicates, and `[T18]`
ruled their SHAPE before anyone builds them, precisely to prevent a rebuild.
The count layer they stand on is delivered (`FOL.Count`). Build the predicates.

CWD: /Users/alsg/Agentic/Bedrock
SCOPE (write): ONE new master under `src/L/` (named by subject) plus
`_build/l3.32-t37-report.md`. Never `src/Everything.lagda.md`. **Do not touch
`src/L/Ordinal/` (a sibling is building the square law there),
`src/L/LevelFormula.lagda.md`, or `src/L/Rud/` (siblings own those).**
SCOPE (read, in order): `_build/l3.32-t18-report.md` (**THE BINDING DESIGN
RULINGS, and they are not negotiable**: equinumerosity is defined as the
EXISTENCE OF A BIJECTION, never as injections both ways, because the latter
turns every equality into a per-consumer Cantor-Bernstein obligation and drags
the general theorem in anyway; and the predicates are built GENERALLY, not as
GCH-specific shims, because the fine-structure era's cardinal notion and the
geology era's internal cardinality function are extensions of exactly these);
also its section 1, the exact internal sentence, and its section 3, the minimal
vocabulary; `src/FOL/Count.lagda.md` (the delivered count layer);
`src/L/Ordinal/Stages.lagda.md` (`φ-ord` and its certificate: the house pattern
for a certified internal predicate, and the anchor T18 priced against);
`src/FOL/Syntax.lagda.md`, `src/L/Definability.lagda.md`,
`src/FOL/ZFModel.lagda.md`; `_build/literature/dev2.txt` and `jech13.txt` (cite
the classical definitions you follow); `dev/STYLE-agda.md`,
`dev/STYLE-i18n.md`, `dev/LESSONS.md` (binding).

CONTENT: equinumerosity, cardinal, and successor cardinal as internal formulas
with their certificates and their meta-level adequacy, built generally. NOT in
this batch: the aleph sequence, the cardinality function, general
Cantor-Bernstein, general cardinal arithmetic, cofinality, or anything about
GCH; T18 names all of those as genuinely deferrable.

CONSTRAINTS: `GHCRTS=-M8g agda <file>`, ONE Agda process at a time (three
siblings run). STOP-LINE 400 non-blank in-fence lines. D-10 first on each
predicate: state it, check its truth and its expressibility at the intended
generality, and record any correction. No postulate, no hole, no TERMINATING.
Trilingual prose (en and zh), no em dash. Both linters clean. Do NOT run `make
check`. No git. Never touch `.claude/`.

RETURN (`_build/l3.32-t37-report.md`; final message = the summary): the exports
with their types and certificates; the measured size against T18's anchored
estimate; confirmation that equinumerosity is the bijection form and that
nothing is a GCH-specific shim; what the later eras can extend rather than
rewrite; the walls by LESSONS class; and the `Everything` wiring note.
