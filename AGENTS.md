# AGENTS.md

Bedrock proves, in Cubical Agda, that the constructible universe `L` satisfies ZFC and
GCH. Both are proved and both are registered in `src/Landmarks.lagda.md`: `L⊨ZFC` and
`L⊨GCH`, each on `LEM (ℓ-suc ℓ)` and nothing else.

Requirements: Agda 2.8.0, cubical 0.9, Python 3.11 or later.
`src/Everything.lagda.md` imports every module. `make check` is the gate: it typechecks
the tree, runs the four linters and runs their unit tests.

## Current goal: smaller proofs and faster builds

Refactor the completed proofs and their code to reduce code size, proof length,
and typechecking/build time. Preserve `L⊨ZFC`, `L⊨GCH`, their statements, and their
single `LEM (ℓ-suc ℓ)` hypothesis.

The first milestone is a net reduction of at least 3,000 nonblank Agda code lines
from the 2026-09-06 baseline of 28,973, reaching at most 25,973 (and therefore
below 27,000). Count only lines inside Agda fences in `src/**/*.lagda.md`;
prose, fences, and blank lines do not count. Do not meet the target by packing
lines, deleting explanations, weakening statements, or moving code outside the
counted tree. Prefer shared proofs, simpler constructions, and removal of
verified redundant code. Record comparable timings, including cache conditions;
fewer lines alone do not establish a faster build.

Prioritize structural refactoring and mathematically simpler proofs. The line
milestone is a measurement, not a reason to sacrifice readability. Do not pursue
small textual reductions or add abstractions whose only benefit is fewer lines.

A refactoring brief may change intermediate APIs and migrate their actual
consumers together. Preserve mathematical statements and necessary opacity
boundaries; do not retain redundant compatibility wrappers solely to preserve
old helper names. Include every consumer migration in the net cost.

Use GPT 5.6 Sol for routine refactoring, audits, and verification. Reserve GPT 6
Astra for difficult proof design that needs it. Keep task briefs bounded, batch
related checks, and avoid repeated readiness messages or speculative searches.

The plan, measurements, and accepted changes live in `dev/REFACTOR.md`.

## Rules for a dispatched agent

1. **Write only the files your brief names.** Do not touch any other file. Never commit,
   never push, never run `git` commands that change state.
2. **Every Agda file must keep `--safe`.** No `postulate`, no `TERMINATING` or
   `NON_TERMINATING` pragma, no `trustMe`, no unsolved metas or holes in a file you call
   done. If you cannot close a goal, leave the hole and say so.
3. **Memory.** Run Agda only as `GHCRTS="-A64m -I0 -M8g" agda <file>`. Two Agda processes
   at most on this machine, so count them before you start one. Never typecheck
   `src/Everything.lagda.md` unless the brief says so.
4. **Deliverable.** Either the named file typechecks with exit 0, or a stop report. A stop
   report quotes the exact Agda error, the file and line, and the type of the goal that
   stands open. Nothing else counts as a result. **A measured negative is a result**: if
   the plan in your brief does not hold, say so with the evidence and stop.
5. **Report short.** State the outcome in the first line. Then the checked command and
   its exit code. Then anything the next person must know, with `file:line`. No history,
   no speculation, no restating the brief.
6. **Code style.** Follow the surrounding module. `dev/STYLE-agda.md` is the law for code
   and `dev/STYLE-i18n.md` for prose. **No comment inside an ```agda fence**: split the
   fence and write the comment as prose between the halves. Never an em dash. Do not
   rename or restructure existing definitions unless the brief asks.
7. **Trust grep, not prose.** A comment claiming a thing is proved once, or that a lemma
   has one consumer, has been wrong three times in this tree. Check before you rely on it.
