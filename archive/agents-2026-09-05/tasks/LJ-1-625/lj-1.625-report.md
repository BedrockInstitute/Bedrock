# LJ-1.625 report: the landing survey, finished, with the LJ-1.620 cell filled

Status: COMPLETE. GO. No commit, no push. ASD-STE100. Written as a
skeleton before any Agda run (C-22) and filled as each run landed.
Every section below carries its measurement or says why it cannot.

## THE VERDICT

**GO.** The obligation
`agents/tasks/LJ-1-625/Probe625.agda::landing-survey` IS in the probe,
at `agents/tasks/LJ-1-625/Probe625.agda:286`, and the probe is GREEN:
`runs/final-1.out`, exit 0, 2.62 s, peak RSS 438,796,288 bytes, over
the files as they stand at this writing `runs/final-4.out`, exit 0,
2.03 s, peak RSS 462,569,472 bytes (this run re-elaborated both the
statement and the probe), and two repeat interface-load runs green
(`runs/final-2.out` 1.69 s, `runs/final-3.out` 1.61 s). The type is
`W3.Survey`, imported from `agents/tasks/LJ-1-625/runs/W3.agda`, which was alone-checked
before any content existed. No hole, no postulate, `--safe` is on,
nothing landed in `src/` (`git status`: only `agents/tasks/LJ-1-625/`
is new), and `make check` was not run. Caliber `-A64m -I0 -M2g` was
set by the program on this pane; I did not set `GHCRTS`. One Agda
process at a time. Every typecheck ran under a wall-clock cap I set
and report. `review-of-landing-survey.md` is NOT written because there
is no stop to state.

**THE MEASURED GENERAL ANSWER, AGAINST THE BRIEF'S GUESS.** The brief
guessed the four terms sit above every chapter that wants them, so
each needs a new master, and ordered the guess measured rather than
assumed. **The measurement refutes it: NO ingredient of the four
needs a new master. Each has an existing host whose direct imports
already cover every name the ingredient's spelling opens, so each
lands with ZERO new import edges.** Two landings widen one `using`
clause on an import line the host already has, which is not an edge.
The two-surveys shape holds ONLY of ingredient (i)'s natural home
`L.Definability`, one half of one row.

## D-10, BEFORE ANY AGDA, AND IT IS THE PARSE

`[LJ-1.620]`'s probe is red at parse, and this task reproduced the
cause before it could bite: a `data` block whose constructors share
one colon while written on separate lines raises
`Syntax.WrongContentBlock` (`runs/w3-1.out`, the first run of
`runs/W3.agda`, 1.40 s, exit 42 at parse). The error name says
"content block" and the damage is constructor syntax, not literate
markup. One-line constructor lists cured it, and the same cure is what
`[LJ-1.620]` needs: its `Survey` datatype carries the same multi-line
shared-colon shape. So the recorded residue "the probe cannot parse"
is TRUE with the cause now named. Premises 2 and 3 were verified
where the files live: `[LJ-1.620]`'s directory is NOT in this
worktree (`git ls-files agents/tasks/ | grep LJ-1-620` is empty at
HEAD `b49c3054`) and is untracked in the main tree
(`/Users/alsg/Agentic/Bedrock/agents/tasks/LJ-1-620/`, `git status`
`??`), which is where I read them: the report's (i) row with the
cycle and its unfilled host cells is
`/Users/alsg/Agentic/Bedrock/agents/tasks/LJ-1-620/lj-1.620-report.md:42`,
and the file carries 13 unfilled placeholder cells in 69 lines.

The target's truth, priced before the proof: every witness this survey
assembles is a substitution instance of a green `src/` chapter
(`DefOf.defSet`, `𝒟ₒ-inv`, `leastOf`, `keyS`) or a verbatim copy of a
green probe row (`[LJ-1.608]`'s `Rows.the-graph`), so no Tarskian or
cardinality obstruction can reach the obligation. The survey's own
content, the host readings, is checked the other way: by the
import-graph count below and by the fact that every open in the
probe's sections names a module the row's host already imports.

## THE IMPORT GRAPH, READ

I read the `import` and `open import` lines of all **102 masters**
under `src/` (`find src -name '*.lagda.md' | wc -l` gives 102; no
count in this report comes from a command containing `head`). The
reading extracted **1,900 import lines** in total, of which **1,292
are internal** (they name a `src/` module) and 608 name Cubical
modules. The per-file import lists are the evidence base for every
host claim below, each cited at `file:line`. Closures and dependent
counts were computed from that reading by a script over the extracted
graph; the counts it printed are the ones quoted here.

## W3, THE OBLIGATION TYPE ALONE

`runs/W3.agda` bound `landing-survey` with a hole over the full survey
type, all four ingredient types included, and typechecked ALONE under
a 60 s cap: `runs/w3-3.out`, exit 42 with exactly ONE unsolved
interaction meta (the hole at what was then `W3.agda:305`) and no
other error, 1.71 s, peak RSS 386,842,624 bytes. The two earlier runs
are the cure record: `runs/w3-1.out` (the constructor block, exit 42
at parse) and `runs/w3-2.out` (one arity row in (v)'s elimination
half, exit 42 at type, 2.08 s). After the alone run, the hole's
declaration moved out of `W3.agda` (a module with an open hole cannot
be imported: the probe's first chain run failed with
`SolvedButOpenHoles` at that import), and the obligation is now
declared in the probe AT `W3.Survey`, imported, so the stated survey
and the delivered one cannot drift. The current `W3.agda`, hole-free,
re-elaborates green alone: `runs/w3-6.out`, exit 0, 2.43 s, peak RSS
447,873,024 bytes (and loads green at `runs/w3-5.out`). (`runs/w3-4.out`
is a wrapper glitch with no Agda
output at all, exit 1 from `time`, superseded by `w3-5`.)

The brief estimated W3 at about ten lines. The file is longer because
the survey type carries each ingredient's delivered type, and
ingredient (iv)'s statement is a module of its own; the estimate was
for a witness-free term. The tree decided.

## THE FLOORS

Fresh modules over exactly each ingredient's measured dependency set,
one inhabited row each, all run AFTER the W3 runs under the same warm
`_build` (so the four are comparable with each other and warm; the
caps were 300 s and none was approached). These price the frame a NEW
master per ingredient would elaborate in.

| floor | dep set (src masters) | closure | seconds | peak RSS (bytes) | percent of cap | log |
|---|---|---|---|---|---|---|
| (i) | 5 | 13 | 1.81 | 233,652,224 | 10.9 | `runs/floorI-1.out` |
| (ii) | 5 | 30 | 1.35 | 315,785,216 | 14.7 | `runs/floorII-1.out` |
| (iv) | 10 | 30 | 1.28 | 328,368,128 | 15.3 | `runs/floorIV-1.out` |
| (v) | 6 | 45 | 1.45 | 345,325,568 | 16.1 | `runs/floorV-1.out` |

The caps and peaks of every run in this task: W3 runs capped at 60 s
(peaks 269,336,576 to 447,873,024 bytes), floors at 300 s, the probe
runs at 600 s (peaks 377,733,120 to 462,569,472 bytes). The highest
peak of the whole task is 462,569,472 bytes, 21.5 percent of the cap.
No wall was met and no heap restructuring was needed.

## FOUR INGREDIENTS, FOUR HOMES

The order is the table's: (i), (ii), (iv), (v)
(`agents/tasks/LJ-1-594/review-of-pairing-suffices.md:40-44`).

| ingredient | cheapest host measured | new import lines | blocker |
|---|---|---|---|
| (i) | `L.Constructible` (`Section-1`, `Probe625.agda:107-119`; every open is one of its own lines, `src/L/Constructible.lagda.md:29-37`) | none | the definability chapter `L.Definability` itself is blocked: the rows need `Lset` and `𝒟ₒ` from `L.Constructible`, and `L.Constructible` already imports `L.Definability` (`src/L/Constructible.lagda.md:37`); the reverse edge is a cycle |
| (ii) | `L.StageCardinal` (`Section-2`, `Probe625.agda:138-150`; `OrdSWO.ordSWO` is the site's own, `src/L/StageCardinal.lagda.md:228`, and the instance already elaborates in the site's `h` at `:351`) | none; ONE `using` widening: `IsLeast` joins the `L.WellOrder.Base` line (`src/L/StageCardinal.lagda.md:35-36`) | none |
| (iv) | `L.BoundedSubset` (`Section-4`, `Probe625.agda:166-236`; the host already imports every name the statement opens and already instantiates the site: `src/L/BoundedSubset.lagda.md:882` and `:1397`) | none | none at that host; the site chapter itself would need TWO new edges (`FOL.Absoluteness`, `L.Axioms.Basic` are absent from `src/L/StageCardinal.lagda.md`'s import lines) |
| (v) | `L.Choice.Faithful` (`Section-3`, `Probe625.agda:254-269`; the host imports `L.Coding.CodeSet` at `src/L/Choice/Faithful.lagda.md:63-65` with `keyS`, `AllCodes`, `AllCodes-out` in its `using`, `LsetS` at `:51`, `Lset` and `IsOrd` at `:46-47`) | none; ONE `using` widening: `key∈AllCodes` joins the CodeSet line | none |

The hosts above are not the only edge-free ones. The reading found,
for (i), ten further masters whose direct imports cover the
spelling (`L.Ordinal.Stages`, `L.Axioms.Basic`, `L.Axioms.Separation`,
`L.Choice.Name`, `L.Coding.Bridge`, `L.Coding.EnvSupply`,
`L.Coding.Key`, `L.Coding.Powerset`, `L.Coding.Uniform` and
`L.StageCardinal`, besides the row's choice and the aggregator); for
(ii) and (iv), only `L.BoundedSubset` and the aggregator besides; for
(v), only the aggregator besides. The aggregator
`src/Everything.lagda.md` imports all 101 others and defines nothing,
so it hosts nothing.

What a host COSTS, which the edges do not say: a landing in an
existing master invalidates that master's interface and every
dependent's. `L.Constructible` has 70 direct dependents (71
transitive) in the reading, `L.StageCardinal` 2 (3 transitive),
`L.BoundedSubset` 2 (2 transitive), `L.Choice.Faithful` 2 (8
transitive). A new leaf master has 0 dependents and one aggregator
line, at the frame prices of the floors table. This is the number the
next brief must weigh, not only the edge count.

## THE CHEAPEST ONE

**Ingredient (ii), landed in `L.StageCardinal`.** Three measured
reasons:

1. **The row is one line over a call the chapter already makes.** The
   body is `leastOf (OrdSWO.ordSWO δ oδ) lem`
   (`Probe625.agda:149-150`), and the site's own `h` already
   elaborates `leastOf (OrdSWO.ordSWO α oα) lem (...) (...)` today
   (`src/L/StageCardinal.lagda.md:351`). The landing names an existing
   inline call as a standalone row; no new normalisation shape enters
   the chapter.
2. **Zero new edges and one token of widening.** `IsLeast` joins the
   `L.WellOrder.Base` using list at `src/L/StageCardinal.lagda.md:35`;
   no import line is added anywhere.
3. **The blast radius is the smallest measured for an existing
   host.** Editing the site invalidates 3 interfaces in the reading
   (its two direct dependents plus one transitive), against 71 for
   `L.Constructible` and 8 for `L.Choice.Faithful`. The frame price of
   a fresh module over the same five direct imports is `FloorII`:
   1.35 s, 315,785,216 bytes.

The runner-up is ingredient (i) as a NEW leaf master: the smallest
frame of the four (`FloorI`, 13-master closure, 1.81 s, 233,652,224
bytes) and zero dependents, at the price of being a new chapter with
one aggregator line rather than an existing host. Ingredient (i) at
`L.Constructible` adds no edge either, but every edit there
invalidates 71 interfaces, the elaboration-frame pain
`[LJ-1.541]`/`[LJ-1.547]` measured as four 1800 s timeouts. What this
task did NOT measure is the site master's own re-elaboration time; the
floors price the frames, and the landing brief must carry the
`[LJ-1.559]`/`[LJ-1.622]` warm-floor check to close that gap.

## WHAT A LANDING BRIEF FOR IT MUST CARRY

1. A write scope naming `src/L/StageCardinal.lagda.md` AND
   `src/Everything.lagda.md`: `[LJ-1.555]`'s scope named neither and
   its 587-line master is absent from the branch
   (`agents/tasks/LJ-1-555/review-of-CardAboveL-landing.md:88-96`);
   `[LJ-1.622]`'s report says the same at its "WHAT A LANDING BRIEF
   SHOULD NOW SAY".
2. The row, verbatim at the site's own telescope (inside
   `L.StageCardinal`, `OrdSWO` unqualified):
   `least-at : (δ : V ℓ) (oδ : IsOrd δ) (P : ⟪ δ ⟫ → hProp (ℓ-suc ℓ)) → ∥ Σ[ a ∈ ⟪ δ ⟫ ] ⟨ P a ⟩ ∥₁ → Σ[ a ∈ ⟪ δ ⟫ ] IsLeast (OrdSWO.ordSWO δ oδ) P a`
   with body `least-at δ oδ = leastOf (OrdSWO.ordSWO δ oδ) lem`, plus
   `IsLeast` added to the using list of the `L.WellOrder.Base` line
   (`src/L/StageCardinal.lagda.md:35-36`).
3. The warm-floor check FIRST: if a fresh module over the site's own
   import lines reads far above `FloorII`'s 1.35 s / 315,785,216
   bytes in the landing worktree, the wall is in that worktree's
   `_build` and the brief bisects the build state, not the term
   (`agents/tasks/LJ-1-622/lj-1.622-report.md`, "WHAT A LANDING BRIEF
   SHOULD NOW SAY").
4. No `make check` inside the landing run, and no import of any probe
   (`agents/tasks/LJ-1-622/lj-1.622-report.md`, same section, measured
   both as wall sources).
5. A tie row after the landing: the probe's `Section-2.least-at`
   (`Probe625.agda:149`) must equal the landed row by `refl`, which is
   the proof the landing is the surveyed term and not a variant.

## THE GATES

`make check` was NOT run (the brief forbids it). Individual checks
were run from this worktree with the main tree's virtualenv python
(this worktree has no `.venv`): `check-probes.py` clean (7,927 tracked
files, no probe outside `agents/tasks/`), `check-closure.py` clean
(102 masters), `check-spec-surface.py` clean (8 surface files, 201
declarations, 499 in-fence lines), `lint-prose.py` clean,
`lint-agda.py` clean, `check-fences.py` clean (102 masters). The
ratio bar cannot fire on this task's writes: the write scope contains
no `.lagda.md` master, and a raw `.agda` probe carries no fence.

## W2, ANSWERED

The survey writes every ingredient ONCE, at the generic carrier the
host chapters themselves use: the probe's telescope is `{ℓ}`, `lem`,
`α₀`, `oα₀`, `sq`, nothing fixed, and each section's body is one
application of a chapter's own generic term (`DefOf.defSet`,
`𝒟ₒ-inv`, `leastOf`, `keyS`) or the one verbatim graph term, which
sits at the same generic telescope. No proof exists twice in this
file, and nothing was instantiated to make anything land.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`, read. Line 332 carries the row
  `| LJ-1.263 | Land the three L-rows into Key.lagda.md | ALL THREE LANDED. THE MASTER IS GREEN | Three re-runs import the master's versions and all exit 0, so this is a landing and not a copy |`.
  It is the campaign's
  measured precedent for the route this survey recommends: rows landed
  into an existing chapter, green, verified by re-import. It is a
  precedent of SHAPE and nothing here is funded against its numbers.
- `archive/dev/JOURNAL.md`, declined: not read. The campaign history
  it holds is not a premise of an import-graph reading.
- `archive/dev/JOURNAL-archived.md`, declined: not read. Same reason.
- `archive/dev/DECISIONS-archived.md`, declined: not read. No decision
  cited by this brief lives there.
- `dev/ARCHIVE.md`, declined: not surveyed. No module retires in this
  task, so W4's register is not consulted.

## LITERATURE USED

- `dev/literature/devlin-II5.md`, declined: not read. Every witness
  here is a substitution instance of a green tree chapter; no
  mathematical statement is settled by this survey.
- `dev/literature/truncation-and-selection.md`, declined: not read.
  The truncation behaviour of `leastOf` is settled in `L.WellOrder.Base`
  and only loaded, not priced.
- `dev/literature/digest.md`, declined: not read. Same reason as
  devlin-II5.md.
- `dev/literature/geology.md`, declined: not read. No layering or
  stratification question is open in this task.
- `dev/literature/glossary-review-2026-08.md`, declined: not read. No
  term is coined here; every name is a chapter's own.
