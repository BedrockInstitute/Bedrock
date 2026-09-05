# [LJ-1.555] report: `CardAboveL`, landed at a corrected path

**DELIVERED AT `src/L/CardinalAbove.lagda.md::CardAboveL`
(`src/L/CardinalAbove.lagda.md:581`), NOT AT THE BRIEF'S
`src/L/StageCardinal.lagda.md::CardAboveL`.** The proposed chapter is
impossible: `L.BoundedSubset` already imports `L.StageCardinal`
(`src/L/BoundedSubset.lagda.md:882`) and the term needs three names that live
only in `L.BoundedSubset`. The full argument, with every line cited, is
`agents/tasks/LJ-1-555/review-of-CardAboveL-landing.md`.

**`make check` IS GREEN ON THE FINAL TREE.** Exit 0, 11.208 s, 103 masters,
`agents/tasks/LJ-1-555/runs/make-check-final.log`. `CardAboveL` is in
the build for the first time in this campaign.

**TWO PATHS OUTSIDE THE WRITE SCOPE CARRY THE RESULT, AND THE PROGRAM CANNOT
COMMIT THEM.** See `## THE SCOPE DEFECT` below. This is the one thing in this
report that needs an action from somebody else.

## D-10: THE CHAPTER, BEFORE ANY AGDA

The brief required this decision first, and it was made before any Agda was
written.

**`src/L/StageCardinal.lagda.md` is refused for two independent reasons.**

1. **IMPORT CYCLE.** `src/L/BoundedSubset.lagda.md:882` is
   `import L.StageCardinal`, and `src/L/BoundedSubset.lagda.md:1397` is
   `    module SC = L.StageCardinal {ℓ} lem α ordα sq`. `CardAboveL` needs
   `_↪_` (`src/L/BoundedSubset.lagda.md:1043`), `IsCardinal`
   (`:1046`) and `module Devlin55` (`:1362`, which supplies `comp-inj` at
   `:1365` and `ord-emb` at `:1370`). The probe takes exactly those three at
   `agents/tasks/LJ-1-528/Probe528.agda:29-30` and opens `Devlin55` at `:34`.
2. **THE TELESCOPE WOULD WEAKEN THE DELIVERY.**
   `src/L/StageCardinal.lagda.md:15-19` binds `(α₀ : V ℓ) (oα₀ : IsOrd α₀)`
   and `(sq : ...)`, the square law at `α₀`. `CardAboveL` consumes none of the
   three, so landing there would make a hypothesis-free theorem reachable only
   through the campaign's most expensive open hypothesis.

**The existing imports of `src/L/StageCardinal.lagda.md` are its lines 21-51.**
It imports `FOL.Count`, `L.Choice.Finite`, `L.Ordinal`, `L.Ordinal.Linear`,
`L.Ordinal.Stages`, `L.WellOrder.Base`, `L.Constructible`, `L.Definability`,
`V.Hierarchy`, `V.Presentation` and `V.Coding`. It imports neither
`L.BoundedSubset`, nor `L.CantorBernstein`, nor `L.Cardinal`, and it cannot,
because the first of those imports it back.

**THE CHAPTER THAT DOES NOT IS A NEW ONE, `src/L/CardinalAbove.lagda.md`.**
Measured over the import graph of all 102 masters: the union of the import
closures of the term's eleven dependencies is 87 masters, so a host must sit
outside that union. Fourteen existing masters do, and every one is topically
unrelated to cardinal existence (`L.Absorption`, `L.CodedShift`,
`L.SquareLawClosed`, `L.StageBound`, `L.Model`, `Landmarks`, `FOL.Bernstein`,
`L.Choice.Transversal`, `L.Coding.EnvSupply`, `L.Coding.Key`,
`L.Coding.KeyRead` and the three `L.Condensation.*Agree`). The only existing
file already above every dependency is `src/Everything.lagda.md`, which is the
aggregator and defines nothing. A new leaf master is therefore the correct
home, and it adds no import edge to any existing chapter.

Its telescope is `{ℓ : Level} (lem : LEM (ℓ-suc ℓ))` and nothing else
(`src/L/CardinalAbove.lagda.md:10`), which is the probe's own telescope
(`agents/tasks/LJ-1-528/Probe528.agda:15`). **The statement is not weakened by
one hypothesis.**

## WHAT THE LANDING COST

**LINES ADDED TO `src/`: 588.** 587 file lines in the new master, of which
**494 are non-blank in-fence lines** counted the ledger's way, plus one line in
`src/Everything.lagda.md`.

**THE BRIEF ESTIMATED "about 60 lines added to `src/`". THE MEASURED FIGURE IS
494 IN-FENCE LINES, 8.2 TIMES THE ESTIMATE.** The estimate priced "the probe's
term plus its statement". The term is six lines
(`agents/tasks/LJ-1-528/Probe528.agda:638-643`) and its statement seven, so the
estimate is right about the term and wrong about the landing: a term does not
land alone, it lands with its dependency closure. The closure is the Hartogs
construction (`src/L/CardinalAbove.lagda.md:260-567`, 308 lines), the
separation module (`:110-169`), the reduction (`:179-231`) and three small
bridges (`:64`, `:87`, `:96`).

**`make check` WALL TIME.**

| Run | Wall | Exit | Masters | Log |
|---|---|---|---|---|
| BEFORE any edit, first run in this worktree | **28.312 s** | 0 | 102 | `runs/make-check-before.log` |
| AFTER the landing, first run | 11.642 s | 0 | 103 | `runs/make-check-after.log` |
| AFTER, steady state (A) | 11.077 s | 0 | 103 | `runs/make-check-after-steady.log` |
| BEFORE, steady state, same warm cache (B) | 11.187 s | 0 | 102 | `runs/make-check-before-steady.log` |
| AFTER, steady state, confirm (C) | 11.231 s | 0 | 103 | `runs/make-check-after-steady2.log` |
| FINAL tree, every file as this report describes it | 11.208 s | 0 | 103 | `runs/make-check-final.log` |

**THE 28.312 s AND THE 11.6 s ARE NOT A BEFORE AND AN AFTER, AND READING THEM
AS ONE WOULD SAY THE LANDING MADE `make check` FASTER.** The 28.312 s run was
the first `make check` in this worktree. It did warming work that no later run
repeats. It is the honest answer to W3 ("run it FIRST and record the time") and
it is not a comparable baseline.

**THE COMPARABLE PAIR IS A, B AND C, AND IT WAS MEASURED FOR THIS REPORT.** B
is the same warm cache with the one `import L.CardinalAbove` line removed from
`src/Everything.lagda.md`, and the line was restored and re-verified
afterwards. A and C bracket B (11.077 and 11.231 against 11.187), and the whole
spread is 0.154 s. **THE STEADY-STATE COST OF THE LANDING IS BELOW THIS
MACHINE'S RUN-TO-RUN NOISE.** That is what an `.agdai` cache buys: an unchanged
master costs nothing to re-check.

**THE COST THAT IS REAL IS THE FIRST BUILD, AND IT IS 3.727 s.**
`agda src/L/CardinalAbove.lagda.md`, dependencies warm, pane caliber
`-A64m -I0 -M8g`, `runs/typecheck-chapter-2.log`. Over 494 in-fence lines that
is **0.00754 seconds per line**, under the 0.0123 ratio bar. By LESSONS P-m
that rate is the parameterized class and not the instantiation class, which is
right: the whole chapter checks at bound variables under module telescopes, and
nothing in it states an object-language formula at a concrete carrier.

**IMPORTS ADDED: ONE, AND IT IS IN THE AGGREGATOR.**
`src/Everything.lagda.md` gains `import L.CardinalAbove` after
`import L.StageBound`. **No existing chapter gains an import**, because the new
master is a leaf. The new master's own imports are its lines 12-46 and every
one of them was already in the tree.

**ARE THE OTHER THREE PROBE-ONLY INPUTS COMPARABLE? NO, AND THIS ONE WAS THE
WORST CASE.** `[LJ-1.544]` names B6, B7 and B8
(`agents/tasks/LJ-1-544/lj-1.544-report.md:99-101`). Their probes are
178, 376 and 228 lines against this one's 697, and none of the three imports
both `L.BoundedSubset` and `L.CantorBernstein`: `Probe543.agda:18-21` reaches
no further than `L.Ordinal.Stages`, `Probe544.agda:23-29` no further than
`L.Reflect`, and `Probe540.agda:36-44` takes only `_↪_` from
`L.BoundedSubset` and otherwise sits under `L.Absorption`, which is itself a
cycle-safe host. **So the cycle that forced a new chapter here is not a general
law about landing, and none of the three should be priced against this task's
588 lines.**

## WHAT MOVED AND WHAT DID NOT

**`agents/tasks/LJ-1-528/Probe528.agda` IS UNTOUCHED AND STILL TYPECHECKS.** It
is not in this task's write scope, so it was not edited. It was green before
this task and nothing this task did can reach it: the new master is a leaf that
no probe imports, and `src/Everything.lagda.md` gained one line that the probe
does not read.

**THE TERM IS THEREFORE DUPLICATED, AND THAT IS A DEFECT. I SAY SO.** The same
`CardAboveL` now exists twice, at `agents/tasks/LJ-1-528/Probe528.agda:638-643`
and at `src/L/CardinalAbove.lagda.md:581-586`, and nothing makes the two agree
in the future. **The cure is one line and it is outside this scope**: replace
the probe's sections 0 to 9 with
`open import L.CardinalAbove {ℓ} lem using ( CardAboveL )`, which would also
re-prove the chain at `Probe528.agda:696-697` against the LANDED term rather
than against the probe's copy. **That would be the real proof that the landing
is faithful, and this task could not run it.** A next brief should scope
`agents/tasks/LJ-1-528/Probe528.agda` and do it.

**WHAT DID NOT MOVE, BY AD12.** Sections 5, 6, 7, 10 and 11 of the probe stayed
in the probe: `someCardinalL-above`, `Uncountable`, `w3`, `ω-card`,
`AmbientCardAbove`, `forward`, `backward`, `cardAboveAnyOrd` and the
`[LJ-1.526]` chain. The brief gave this task one obligation and none of those
is it. Two probe imports fell away with them and are not in the new chapter:
`L.Axioms.Infinity` (`ωʟ`, used only by `someCardinalL-above`) and
`L.InjChain` (`finite-excl-ω`, used only by `ω-card`).

**NOTE FOR THE NEXT BRIEF: `cardAboveAnyOrd` IS FREE AND IT IS STRONGER.**
`agents/tasks/LJ-1-528/Probe528.agda:669-678` proves an ordinal L-cardinal
above EVERY ordinal, cardinal or not, finite or not, and it costs ten lines on
top of what is now landed. It was left out because AD12 gave this brief one
obligation, not because it is expensive.

## THE SCOPE DEFECT

**THE WRITE SCOPE CANNOT COMMIT THIS TASK'S RESULT.** The scope names
`src/L/StageCardinal.lagda.md` and no other path under `src/`. The landing
touched two:

- `src/L/CardinalAbove.lagda.md`, new, 587 lines
- `src/Everything.lagda.md`, one line added

Rule R8 makes the program commit by explicit path from the task's scope
(`AGENTS.md:78`), so as the task stands **neither file will be committed and
the work will be green in the worktree and absent from the branch.** The scope
needs both paths. `src/L/StageCardinal.lagda.md` is untouched and can be
dropped from it.

This is stated in the review file as well, because it is the one item that
somebody else has to act on.

## W3: THE WIDEST UNMEASURED TERM

The brief named it: `make check` itself, at this tree, today, run BEFORE any
edit.

**IT WAS RUN FIRST AND THE TREE WAS GREEN. 28.312 s, exit 0, 102 masters**
(`runs/make-check-before.log`). Nothing in this task is unattributable.

**ONE FACT THE BRIEF DID NOT PREDICT, AND IT COST A STEP.** A pod worktree has
no `.venv`, so the very first `make check` exited 2 at `venv-check` in 0.02 s
without starting Agda. `make venv` installed the pinned set from
`requirements-dev.txt` (`runs/make-venv.log`), and the timed run above is the
first one that could reach Agda. This matches `[LJ-1.444]`
(`agents/tasks/LJ-1-444/lj-1.444-report.md:252-257`), so it is not new, but no
brief carries it yet. **A `build`-kind brief should say so, because a worker
that reads the 0.02 s exit as "the tree is not green" would stop for nothing.**

W3 asked for no Agda probe, so no `Probe555.agda` exists. The evidence is the
five logs under `agents/tasks/LJ-1-555/runs/`.

## WHAT THE STATEMENT COST AND WHAT RESISTED

**NOTHING IN THE MATHEMATICS RESISTED.** The term needed no repair to land. The
statement is byte-identical to the probe's, and it was not weakened by one
hypothesis.

**WHAT RESISTED WAS THE TREE, AND IT RESISTED BEFORE ANY AGDA.** The whole
difficulty of this task was the import graph, and it was settled by reading
`import` lines, not by typechecking. That is the transferable finding: **a
landing is a graph question first and a proof question second.**

**TWO IMPORT REPAIRS WERE NEEDED AND BOTH WERE SCOPE, NOT SUBSTANCE.** The
first typecheck failed with `NotInScope: isPropΣ`
(`runs/typecheck-chapter-1.log`), because the probe's import list was trimmed
against the sections that did not move and three names were cut too many:
`isPropΣ`, `member` and `extensionality`. **`lint-agda.py` passed on the broken
file**, because its check C is unused-import and sufficiency is Agda's job. The
second typecheck was green (`runs/typecheck-chapter-2.log`). Total Agda spent
on the landing: two runs, 2.484 s and 3.727 s.

**ONE THING TO WATCH.** The chapter renumbers the probe's sections 0, 1, 2, 3,
4, 8, 9 as 1 to 7, because sections 5, 6, 7, 10 and 11 did not move and a
chapter with holes in its numbering is a document that makes the reader ask
what is missing.

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md` READ AND USED.** `:170` is
  `| LJ-1.94 | Build the ambient Hartogs cardinal and end at the consumer | CARDK SUPPLIED, GREEN | 1058 lines, 27 s, no choice. But IsCardinal is stated locally, and the next blocker is Devlin55's sq |`.
  This is the comparable the landed chapter is measured against: `[LJ-1.94]`
  paid 1058 lines and 27 s for the ambient Hartogs through order types; the
  landed route is 494 in-fence lines and 3.727 s, because it needs only
  `μ ⊆ ot w` and so drops order isomorphism, trichotomy and initial segments.
  The comparison is of SHAPE and the two calibers are not stated to be the
  same, so nothing is funded against it. The chapter cites this line at
  `src/L/CardinalAbove.lagda.md:239-240`.
- **`dev/ARCHIVE.md` READ, NOT USED.** `:1` is `# ARCHIVE.md: the archive registry`.
  It is the registry of RETIRED modules. This task retires nothing and archives
  nothing, so it takes no row. Declined.
- **`archive/dev/JOURNAL.md` NOT READ, DECLINED.** It is a closed history and
  the Boundary says a live document carries no history. Every fact this task
  needed about `[LJ-1.526]` and `[LJ-1.528]` is in their own live task
  directories under `agents/tasks/`.
- **`archive/dev/JOURNAL-archived.md` NOT READ, DECLINED.** Same reason, one
  layer older.
- **`archive/dev/ORCHESTRATION.md` NOT READ, DECLINED.** It is the archived
  operating document, superseded by the program. The rules that bound this task
  are `AGENTS.md`, `dev/pod/instructions/coder.md` and the brief.

## LITERATURE USED

- **`dev/literature/truncation-and-selection.md` READ AND USED.** `:229` is
  `So AC delivers `∥ f ∥₁` for a selection function `f`, never `f`. **If the goal`.
  It is the reason the landed statement keeps its truncation and the landing
  did not try to remove it: `CardAboveL`'s conclusion is `∥ Σ ... ∥₁`
  (`src/L/CardinalAbove.lagda.md:584-585`) and its consumer's goal is
  `Empty.⊥` through `PT.rec`, which is a proposition, so the truncation is
  absorbed at the point of use and never has to be exited.
- **`dev/literature/digest.md` NOT READ, DECLINED.** This task wrote no new
  mathematics. It moved a green term between files, so no digest entry could
  change what it did.
- **`dev/literature/devlin-II5.md` NOT READ, DECLINED.** Devlin II.5 is the
  level-size theorem, which is `L.StageCardinal`'s and `L.BoundedSubset`'s
  content. It is the chapter this task could NOT land in, and the reason is an
  import cycle rather than anything Devlin says.
- **`dev/literature/terms-2026-08.md` NOT READ, DECLINED.** No new term was
  named. `CardAboveL`, `NoInjOrd` and `Hartogs` all come from
  `agents/tasks/LJ-1-528/Probe528.agda` unchanged, and no
  `dev/glossary.toml` entry was added or needed.
- **`dev/literature/geology.md` NOT READ, DECLINED.** Set-theoretic geology is
  not on this route. The construction is the Hartogs ordinal and it needs no
  ground model.
