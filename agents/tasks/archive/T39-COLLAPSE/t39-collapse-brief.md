# [L3.32-T39] The Mostowski collapse (W5's other half)
tier: codex (default)

GOAL: W5 is collapse plus crossing. `[T33]` delivered the crossing; the
collapse was probed GO early and carrier-neutral, and has sat measured but
unbuilt since. Build it.

CWD: /Users/alsg/Agentic/Bedrock
SCOPE (write): ONE new master (choose `src/V/` or `src/L/` by subject and say
why: the collapse is a fact about well-founded extensional structures on the
hierarchy, not about constructibility) plus `_build/l3.32-t39-report.md`.
Never `src/Everything.lagda.md`. **Do not touch `src/L/Ordinal/` or
`src/L/Rud/Bridge.lagda.md` (siblings own those).**
SCOPE (read, in order): `_build/w5-probe-report.md` (**the measurements and the
route**: the set-valued recursion carried directly by the hierarchy's own
induction, the computation law as a read lemma, image transitivity, extensional
injectivity by double induction, and the iso reading both ways; also its honest
list of what the miniature did NOT exercise); `src/ProbeCollapse.agda` if it
still exists, else the report; `src/L/Condensation.lagda.md` (**THE CONSUMER**:
build what it needs, in the shape it needs); `src/V/Hierarchy.lagda.md` (the
induction principle the recursor rides), `src/V/Presentation.lagda.md` (use the
kit); `src/L/Constructible.lagda.md`; `dev/LESSONS.md` (binding: R-36 for the
computation law's read lemma, I-4, I-5, R-35, R-37, and R-38's appended
no-`with`-on-a-search rule).

CONTENT: the collapse of a transitive-carrier substructure, its transitivity,
its extensional injectivity, and the membership iso both ways, at the
generality the condensation chapter consumes. The probe measured the miniature
at 125 lines and extrapolated the full statement at 1.5 to 2.2 times; that is
your estimate, not your budget.

CONSTRAINTS: `GHCRTS=-M8g agda <file>`, ONE Agda process at a time (two
siblings run). STOP-LINE 400 non-blank in-fence lines. D-10 first on each
target. No postulate, no hole, no TERMINATING. Trilingual prose (en and zh), no
em dash. Both linters clean. **If your chapter needs a term the glossary does
not carry, use it consistently and NAME it in the report; do not add a glossary
entry yourself.** Do NOT run `make check`. No git. Never touch `.claude/`.

RETURN (`_build/l3.32-t39-report.md`; final message = the summary): the exports
and their types; the measured size against the probe's extrapolation; what the
condensation chapter can now discharge; which of the probe's not-exercised
items bit and which did not; the walls by LESSONS class; new terms named; and
the `Everything` wiring note.
