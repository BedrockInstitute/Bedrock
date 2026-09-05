# [L3.32-T31] The square law, discharged (the pairing chapter's named bound)
tier: codex (default)

GOAL: `[T16]` delivered the canonical well-ordering of a product and the
order-type collapse, bijectively, and left ONE named hypothesis: the square
law, an injection from the order type into the ordinal. `[T21]` then found the
route this tree can carry (the INITIAL-SEGMENT route, needing no ordinal
arithmetic at all), measured its decisive step green, and funded it at 480-610
naive. Its gate passed, so under D22 it is funded. Discharge the hypothesis.

CWD: /Users/alsg/Agentic/Bedrock
SCOPE (write): ONE new master under `src/L/Ordinal/` plus
`_build/l3.32-t31-report.md`. Never `src/Everything.lagda.md`. **Do not edit
`src/L/Ordinal/Pairing.lagda.md`**: your chapter supplies what its `Pairing`
module takes as `bound`/`bound-inj`, and the orchestrator will re-point it
afterwards. Do not touch `src/L/Rud/Switch.lagda.md` (a sibling is editing it).
SCOPE (read, in order): `src/ProbeSquareLaw.agda` **if it still exists**, else
`_build/l3.32-t21-report.md`, which records the route, the decisive step and
what it measured; `src/L/Ordinal/Pairing.lagda.md` (THE CONSUMER: its
`Pairing` module's exact hypothesis shape and its `col→τ` bijection);
`_build/l3.32-t16-report.md`; `src/L/Ordinal.lagda.md`,
`src/L/Ordinal/Linear.lagda.md`, `src/L/Ordinal/Stages.lagda.md`;
`src/L/WellOrder/Base.lagda.md` (the least-witness machinery T21 used, and
R-38's appended rule about it); `src/V/Presentation.lagda.md`;
`_build/literature/jech13.txt` (cite the classical statement you follow);
`dev/STYLE-agda.md`, `dev/STYLE-i18n.md`, `dev/LESSONS.md` (binding).

CONTENT: the square law by T21's route, in the shape `Pairing` consumes.
T21 measured the order core at 308 lines and named the remaining pieces (the
initial-ordinal layer, the finite base, the wrapper and transfer); build them.
T21 also flagged one risk inside the initial-ordinal layer, extracting the
equinumerosity with the least ordinal non-truncatedly: if it bites, say so
precisely rather than working around it silently.

CONSTRAINTS: `GHCRTS=-M8g agda <file>`, ONE Agda process at a time. STOP-LINE
650 non-blank in-fence lines. If the chapter cannot close inside it, STOP and
report what is proved and what remains. No postulate, no hole, no TERMINATING.
Trilingual prose (en and zh), no em dash, English only inside fences. Both
linters clean. Do NOT run `make check`. No git. Never touch `.claude/`.

RETURN (`_build/l3.32-t31-report.md`; final message = the summary): the exports
and whether they discharge `Pairing`'s hypothesis exactly; the measured size
against T21's 480-610; the classical route with its citation; whether the
flagged extraction risk bit; the walls by LESSONS class; and the fact that the
file needs `Everything` wiring and that `Pairing` needs re-pointing.
