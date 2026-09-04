# AGENTS.md

Bedrock proves, in Cubical Agda, that the constructible universe `L` satisfies ZFC and
GCH. `L ⊨ ZFC` is proved (`src/Landmarks.lagda.md`). The one open target is
`GCHStatement` in `src/L/GCH.lagda.md`. Every task you receive is a step toward it.

Requirements: Agda 2.8.0, cubical 0.9. `src/Everything.lagda.md` imports every module.

## Rules for a dispatched agent

1. **Write only the files your brief names.** Do not touch any other file. Never commit,
   never push, never run `git` commands that change state.
2. **Every Agda file must keep `--safe`.** No `postulate`, no `TERMINATING` or
   `NON_TERMINATING` pragma, no `trustMe`, no unsolved metas or holes in a file you call
   done. If you cannot close a goal, leave the hole and say so.
3. **Memory.** Run Agda only as `GHCRTS="-A64m -I0 -M8g" agda <file>`. One Agda process at
   a time. Never typecheck `src/Everything.lagda.md` unless the brief says so.
4. **Deliverable.** Either the named file typechecks with exit 0, or a stop report. A stop
   report quotes the exact Agda error, the file and line, and the type of the goal that
   stands open. Nothing else counts as a result.
5. **Report short.** State the outcome in the first line. Then the checked command and
   its exit code. Then anything the next person must know, with `file:line`. No history,
   no speculation, no restating the brief.
6. **Code style.** Follow the surrounding module. Comments in English, no prose blocks in
   a `.lagda.md` beyond a comment. Never an em dash. Do not rename or restructure
   existing definitions unless the brief asks.
