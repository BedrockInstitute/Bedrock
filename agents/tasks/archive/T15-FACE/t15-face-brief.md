# [L3.32-T15] The face chapter, batch 1 (the wing's W1, productionized)
tier: codex (default)

GOAL: turn the measured probe into the wing's first delivered chapter. The
ruled architecture (PLAN D18) builds the GCH wing on a FRESH-GENERIC Sigma-1
face: the L-tower's initial-segment story written CARRIER-GENERIC once, then
instantiated by the wing's own W2, by the bridge's L-sigma, and by the
condensation chapter. `[T2]` probed it GO on both arms with the genericity
premium at the noise floor (`_build/l3.32-t2-report.md`, probe
`src/ProbeFace.agda`). Build the chapter's REUSABLE CORE now; the
instantiations belong to their consumers and are NOT in this batch.

CWD: /Users/alsg/Agentic/Bedrock
SCOPE (write): ONE new master under `src/L/` (name it by subject, not by
provenance, per the naming rule: the chapter is about the constructible
hierarchy's own story told inside a carrier) and `_build/l3.32-t15-report.md`.
Never `src/Everything.lagda.md` (the orchestrator wires it). Do not edit any
existing master; if you find you need an export that is `private`, NAME it in
the report rather than un-privating it.
SCOPE (read, in order): `src/ProbeFace.agda` (THE TEMPLATE: its generic
module shape, its two arms, and its C-6 controls are what you productionize),
`_build/l3.32-t2-report.md` (what was measured and what each hypothesis
means), `src/ProbeGenericRead.agda` and `_build/l3.31-ifip-report.md` (the
genericity discipline, measured at 1.36x amortizing to 1.0x),
`_build/l3.31-r2lever-report.md` facts 1 to 4 (why the face is built FRESH
rather than as a rewrite of the delivered graph, and what `full-switch-⊇`
gives the limit case), `_build/literature/dev6.txt` around the
initial-segment formula, `src/L/Definability.lagda.md`, `src/FOL/Absoluteness
.lagda.md`, `src/V/Presentation.lagda.md` (NEW, use its kit rather than
re-deriving fiber facts), `dev/STYLE-agda.md`, `dev/STYLE-i18n.md`,
`dev/LESSONS.md` (binding: P-h at full strength, D-16, D-21, I-4, I-5, R-35,
R-36, R-37, C-11, C-14).

THE CHAPTER'S CONTENT (batch 1, the core only):
1. The initial-segment story as an object-language formula, GENERIC in the
   carrier and structure (module parameters, P-h at full strength), covering
   the whole story rather than the probe's single clause: the approximation,
   the Def-step at each stage, and the range read.
2. Its two readings (in and out), stated at the generic carrier.
3. The adequacy interface: what a consumer must supply to instantiate, stated
   as the smallest honest telescope. The probe consumed exactly two
   hypotheses; if the full story needs more, each one is a named parameter
   and the report says why it is unavoidable.
4. NOT in this batch: the instantiations at any concrete carrier, the wing's
   W2, the bridge's L-sigma, the condensation crossing. Those are consumers.

CONSTRAINTS: `GHCRTS=-M8g agda <file>`, ONE Agda process at a time (a sibling
holds a heavy slot). STOP-LINE 450 non-blank in-fence lines; if the core
exceeds it, STOP, report what is built and what remains, and do not push on.
Trilingual prose per `dev/STYLE-i18n.md` (en and zh marker blocks, ja
optional), no em dash, English only inside fences. `python3
scripts/lint-agda.py` and `python3 scripts/lint-prose.py` clean on your file
before reporting. Do NOT run `make check`. No git commands. Never touch
`.claude/`.

RETURN (`_build/l3.32-t15-report.md`; final message = the summary): the
chapter's exports with their types; the measured size against the probe's
extrapolation and against the census's W1-fresh band of 1,185 to 2,300; every
hypothesis the telescope takes and why; the walls by LESSONS class; what
batch 2 owes; and the fact that the file needs `Everything` wiring.
