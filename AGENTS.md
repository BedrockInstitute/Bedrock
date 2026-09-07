# AGENTS.md

Bedrock proves, in Cubical Agda, that the constructible universe `L` satisfies ZFC and
GCH. Both are proved and both are registered in `src/Landmarks.lagda.md`: `L⊨ZFC` and
`L⊨GCH`, each on `LEM (ℓ-suc ℓ)` and nothing else.

Requirements: Agda 2.8.0, cubical 0.9, Python 3.11 or later.
`src/Everything.lagda.md` imports every module. `make check` is the gate: it typechecks
the tree, runs the four linters, checks the reading order and runs the gate tests.

## Current goal: coherent modules and a teachable reading order

Reorganize the completed development so that each module is a coherent learning
unit and the reading order introduces concepts before their substantive use.
Good mathematical interfaces, cohesive modules and clear teaching should support
one another. Preserve `L⊨ZFC`, `L⊨GCH`, their statements and their single
`LEM (ℓ-suc ℓ)` hypothesis.

The former line-reduction run is closed. Code size, build time and peak memory
are costs to measure, not optimization targets for this task. Modest increases
are acceptable when a concrete improvement in comprehension or modularity
justifies them. The coordinating agent is authorized to make these tradeoffs.
Do not compress proofs or merge unrelated material to reduce the module count.

A restructuring brief may rename, split or merge modules and definitions,
change intermediate APIs, and migrate all real consumers. Keep necessary
opacity boundaries. Avoid compatibility shells that leave the old conceptual
fragmentation in place. Update chapter introductions, the reading catalog,
namespace references and site navigation together.

Use GPT 5.6 Sol for scoped audits, migrations and verification. Reserve GPT 6
Astra for difficult mathematical design. Delegate disjoint concrete changes;
the coordinating agent owns the overall architecture and final checks.

The current architecture plan and acceptance criteria live in `dev/TEACHING.md`.
The previous closed run's record remains in `dev/REFACTOR.md`.

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
