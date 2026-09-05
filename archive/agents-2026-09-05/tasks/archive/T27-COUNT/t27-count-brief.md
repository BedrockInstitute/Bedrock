# [L3.32-T27] The count layer, productionized (the cardinal chapter's first block)
tier: codex (default)

GOAL: two probes measured the cardinal chapter's combinatorial foundation and
both are green: `[T9]`'s count (every formula over a carrier is a constant-free
shape plus a finite tuple of constants, with decode and reconstruction, 448
probe lines) and `[T17]`'s shape-count (the constant-free formulas of each
arity inject into the naturals, about 200 lines, plus a natural-number pairing
this tree never had). Under D22 both are funded. Productionize them as the
cardinal chapter's first block.

CWD: /Users/alsg/Agentic/Bedrock
SCOPE (write): ONE new master under `src/FOL/` or `src/L/` (choose by subject
and say why: the content is about counting formulas, which is syntax, not
constructibility), plus `_build/l3.32-t27-report.md`. Never
`src/Everything.lagda.md`. Do not edit any existing master; NAME any `private`
export you need rather than un-privating it.
SCOPE (read, in order): `src/ProbeCard.agda` (T9's probe: the count, its decode
and its reconstruction are what you productionize) and `_build/l3.32-t9-report.md`;
`src/ProbeShapeCount.agda` (T17's probe: the shape-count and the natural-number
pairing) and `_build/l3.32-t17-report.md`; `src/FOL/Syntax.lagda.md` and
`src/FOL/Coding.lagda.md` (the delivered syntax and the set-valued coding whose
machinery T17 transplanted); `_build/l3.32-t18-report.md` (**BINDING DESIGN
RULINGS for everything in this cluster**: equinumerosity is the existence of a
BIJECTION, never injections both ways, and the cardinal predicates are built
GENERALLY rather than as GCH-specific shims, because the later eras extend
them); `dev/STYLE-agda.md`, `dev/STYLE-i18n.md`, `dev/LESSONS.md` (binding).

CONTENT: the count and the shape-count as one coherent chapter, with the
natural-number pairing they need. NOT in this batch: the cardinal predicates
themselves, the initial-ordinal layer, or anything about GCH. This block is the
combinatorics the cardinal chapter stands on.

CONSTRAINTS: `GHCRTS=-M8g agda <file>`, ONE Agda process at a time (three
sibling probes are running). STOP-LINE 700 non-blank in-fence lines (the two
probes measured about 650 together; the margin is for the seam, not for scope).
If the seam costs more than the margin, STOP and report rather than pushing on.
No postulate, no hole, no TERMINATING. Trilingual prose (en and zh), no em
dash, English only inside fences. Both linters clean. Do NOT run `make check`.
No git. Never touch `.claude/`.

RETURN (`_build/l3.32-t27-report.md`; final message = the summary): the exports
with their types; the measured size against the probes' 650 and against the
700 stop-line; what the seam between the two probes cost, since that is the
number neither probe could give; the walls by LESSONS class; and the fact that
the file needs `Everything` wiring.
