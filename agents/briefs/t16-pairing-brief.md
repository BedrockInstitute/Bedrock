# [L3.32-T16] The ordinal pairing chapter
tier: codex (default)

GOAL: build the chapter the W7 cardinal gate reduced to. `[T9]`
(`_build/l3.32-t9-report.md`, READ IT FIRST, target T2) proved the
product-bound core CONDITIONALLY: finite tuples over an infinite ordinal
inject into it GIVEN an injective pairing on its index. The pairing itself
has no raw material in the tree (no ordinal arithmetic, no order-type or
rank theory; the absence is grep-verified). Deliver it.

CWD: /Users/alsg/Agentic/Bedrock
SCOPE (write): ONE new master, `src/L/Ordinal/Pairing.lagda.md`, plus
`_build/l3.32-t16-report.md`. Never `src/Everything.lagda.md` (the
orchestrator wires it). Do not edit any existing master; if you need an
export that is `private`, NAME it in the report instead of un-privating it.
SCOPE (read, in order): `_build/l3.32-t9-report.md` (what exactly is needed,
in what shape, and what the probe already proves conditionally),
`src/ProbeCard.agda` (the probe: its `Product.TupleCode` is the consumer you
must satisfy, so match its expected interface exactly), `src/L/Ordinal.lagda.md`
and `src/L/Ordinal/Linear.lagda.md` and `src/L/Ordinal/Stages.lagda.md` (the
delivered ordinal material, the house idiom, and the 241-line comparable),
`src/V/Presentation.lagda.md` (use the kit rather than re-deriving fiber
facts), `_build/literature/` (the classical pairing: Devlin and Jech both
carry the canonical well-ordering of the product; cite what you use),
`dev/STYLE-agda.md`, `dev/STYLE-i18n.md`, `dev/LESSONS.md` (binding).

THE TARGET: for an infinite ordinal (`⟨ ω ∈ˢ α ⟩` in the probe's shape), an
injective `pair : ⟪ α ⟫ → ⟪ α ⟫ → ⟪ α ⟫`, with injectivity in the form the
probe's `TupleCode` consumes. Prove the mathematics honestly: the classical
route is the canonical (Gödel) well-ordering of the product, and its
order-type argument is real work, so do not shortcut it into a postulate or
a `TERMINATING` recursion. If the classical route needs a piece the tree
lacks, NAME that piece and price it rather than faking it.

CONSTRAINTS: `GHCRTS=-M8g agda <file>`, ONE Agda process at a time (siblings
run concurrently). STOP-LINE 400 non-blank in-fence lines: if the chapter
exceeds it, STOP, report exactly what is proved, what remains, and what the
remainder would cost. No postulate, no hole, no TERMINATING. Trilingual
prose per `dev/STYLE-i18n.md` (en and zh), no em dash, English only inside
fences. `python3 scripts/lint-agda.py` and `lint-prose.py` clean on your
file. Do NOT run `make check`. No git. Never touch `.claude/`.

RETURN (`_build/l3.32-t16-report.md`; final message = the summary): the
exports with their types, whether the probe's `TupleCode` interface is
satisfied exactly, the measured size against the 250-400 estimate and the
241-line comparable, the classical route taken with its citation, the walls
by LESSONS class, and the fact that the file needs `Everything` wiring.
