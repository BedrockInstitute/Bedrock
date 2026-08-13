# [L3.32-T29] The Realize cone's retirement, executed
tier: codex (default)

GOAL: `[T11]` measured this exact cut and found it GREEN, then restored the
file. Execute it permanently. `L.Rud.Realize` has already been moved to
`archive/src/L/Rud/Realize.lagda.md` by the orchestrator; your job is the
Switch-side half of the cut, which T11 measured at 500 lines.

CWD: /Users/alsg/Agentic/Bedrock
SCOPE (write): `src/L/Rud/Switch.lagda.md` ONLY, plus
`_build/l3.32-t29-report.md`. Never `src/Everything.lagda.md` (the orchestrator
wires it). Never `archive/` (the orchestrator owns the archive).
SCOPE (read, in order): `_build/l3.32-t11-report.md` IN FULL. **It is the
specification.** Its evidence index names every region by line, its RED finding
names the spec machinery that must go with the six modules, and its GREEN run
confirms the widened cut compiles. Also read `src/L/Rud/Switch.lagda.md`
itself, and `src/L/Rud/Bridge.lagda.md`'s import line (the only consumer, which
takes `module Descr` and `module Hops` and nothing else).

THE CUT, per T11: remove the `L.Rud.Realize` import; the six Realize-dependent
modules (`Bs`, `Ev`, `Rl`, `Closure` including the nested `Eval-J`, `WalkCon`,
`LimitSwitch`); and the notation-and-spec layer that consumes Realize's `∃ₚ`
(T11 names `unionSpec` first and the same-class residue in `prodSpec`,
`memSpec`, `condSpec`, `memWit`, `eqWit`, `chSepSpec`, `eqSepSpec`). KEEP
`Hops` and `Descr`, which T11 verified contain zero references to any Realize
machinery, and everything they need.

PROSE IS PART OF THE JOB: the chapter's own narrative and its recap describe
what is being removed. Rewrite the affected prose in BOTH en and zh so the
chapter reads as what it now is: the reverse hops and the description side,
the two things the bridge consumes. Do not leave orphaned prose describing
deleted code. Say in the report which sections you rewrote.

METHOD (C-10 binds: mechanical multi-site edits are scripted, asserted and
typechecked): after the cut, typecheck `Switch`, then `Bridge`, then
`SatTable`, in that order, one Agda process at a time. All three must be green
before you report. If one is red, the cut is wrong: fix or narrow it, and say
so.

CONSTRAINTS: `GHCRTS=-M8g agda <file>`, ONE Agda process at a time. No git
commands at all. `python3 scripts/lint-agda.py src/L/Rud/Switch.lagda.md` and
`python3 scripts/lint-prose.py src/L/Rud/Switch.lagda.md` clean. Do NOT run
`make check`. Never touch `.claude/`.

RETURN (`_build/l3.32-t29-report.md`; final message = the summary): the
measured before-and-after size of `Switch` in non-blank in-fence lines, against
T11's 500-line figure; the three typecheck results with wall times; which prose
sections were rewritten; any import that became unused and was dropped; and
anything you judged unsafe to remove, with the reason.
