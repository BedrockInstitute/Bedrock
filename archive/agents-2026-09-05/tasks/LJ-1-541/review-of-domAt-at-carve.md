# NO-GO: `domAt-at-carve` at this task's old frame

The obligation `agents/tasks/LJ-1-541/Probe541.agda::domAt-at-carve` is not
bound by this dispatch. The reason is one named difference between two types,
and it is measured, not guessed. This file states the difference, prices it,
and says what would reopen the task.

## D-10, THE TYPE COMPARISON

The brief orders the two types side by side before any Agda, and orders a STOP
if they are not identical. They are not identical.

**The old type, this task's frame**
(`agents/tasks/LJ-1-541/Probe541.agda`, the predecessor's parked artifact):

    domAt-at-carve : (a : S) (oa : IsOrd (fst a)) → DomAtOf (Dom.G a oa) a
    -- Probe541.agda:349

    G = fst (P529.rank-graph Q a bnd)   -- Probe541.agda:260
    Q = P521.ord-set-witness a oa .fst  -- Probe541.agda:254
    bnd = P529.Bound′.bnd a oa          -- Probe541.agda:257

**The new type, the type `[LJ-1.559]` gave its term**
(`agents/tasks/LJ-1-559/Probe559.agda`):

    domAt-at-carve : (a : S) (oa : IsOrd (fst a)) → DomAtOf (Carve.G a oa) a
    -- Probe559.agda:336-338

    G = fst (rank-graph Q a B.bnd)      -- Probe559.agda:261
    Q = ordQ a oa                       -- Probe559.agda:258
    module B = Bound′ a oa              -- Probe559.agda:255

**The family is the same in both files.**
`DomAtOf F a = ⟨ (F ∷ a ∷ []) ⊨ domAt zero (suc zero) ⟩` at
`Probe541.agda:154` and `Probe559.agda:188`, over the same `domAt` from
`src/L/Coding/Model`.

**The first argument is NOT the same.** It names two different local modules,
and three differences separate them:

1. **The carve's provenance.** The old frame names `P529.rank-graph`
   (`agents/tasks/LJ-1-529/Probe529.agda:150-154`), the module of a third
   task. The new frame names `rank-graph` defined in `Probe559.agda:146-150`,
   a local rebuild. Both bodies are
   `hasSeparationL bnd (P521.rankFo Q a) .fst`, but each is a separate
   definition in a separate file, and each needs its own unfolding.
2. **The bound.** The old frame takes `P529.Bound′.bnd`
   (`Probe529.agda:101-131`). The new frame takes the local `Bound′`
   (`Probe559.agda:108-137`), which its header declares
   "REBUILT and not imported" (`Probe559.agda:44-45`, `:97`).
3. **The `Q`.** The old frame writes `P521.ord-set-witness a oa .fst`
   directly. The new frame goes through the alias `ordQ`
   (`Probe559.agda:171-172`), one further unfolding.

After one unfolding of each side, the arguments are NOT syntactically
identical: the bound is still a projection into two different modules, and
`Q` is still an alias in one spelling. This is the case R-42 prices.

## THE MEASUREMENTS THAT PRICE THE DIFFERENCE

**R-42 is written from this task's own runs.** The rule
(`dev/LESSONS.md:4874`, main tree): a carve output compared across two
spellings may finish only if the spellings differ by unfolding ONE definition
whose arguments are then syntactically identical. Its measurement is this
task: `runs/BisC.agda` differs from `runs/BisE.agda` in one line and goes
from exit 0 at 1.74 s to killed at 155.02 s; `runs/BisD.agda`, with only a
module projection between the bodies, still fails at 337.30 s.

**`[LJ-1.566]` measured the exact crossing this file names, and it does not
finish.** Its W3 section (`agents/tasks/LJ-1-566/lj-1.566-report.md`):
`runs/U3.agda` asks one `refl` between `P559.Bound′.bnd a oa` and
`P529.Bound′.bnd a oa`, and the two module bodies are diffed
byte-identical (`Probe529.agda:101-131` against `Probe559.agda:108-137`).
The run is killed at 240.00 s, exit 142, its own cap, not a heap wall
(`runs/U1.agda` against the carves is killed the same way, and
`runs/U2.agda`, the full carve crossing, was written and deliberately not
run).

**So binding the imported term at this task's old frame is forbidden by two
measurements, not by preference.** Re-deriving the bridge in this file would
re-run the same code 566 already ran and stopped. That is the rerun the
ruling forbids.

## WHAT THE TREE HOLDS, AND WHAT THE CITATION MUST SAY

- The predecessor's artifact holds this obligation at its own frame, green:
  `Probe541.agda:349-350`, built at 7.67 s cold
  (`agents/tasks/LJ-1-541/lj-1.541-report.md`, VERDICT section). This file
  does not touch it.
- `[LJ-1.559]`'s term holds the same obligation name at its own frame
  (`Probe559.agda:336-339`), measured GO in its report.
- The assembly `[LJ-1.566]` consumes NEITHER: it rebuilds all four conjuncts
  in one module of its own, and its header states why
  (`agents/tasks/LJ-1-566/Probe566.agda:57-60`; its `domAt-at-carve` is at
  `:474-475`, over its own `Carve.G`).

So a citation of "the delivered `domAt-at-carve`" must name a frame. The two
named frames are inconvertible within a working cap, and the downstream
assembly already declined both and chose its own.

## WHAT WOULD REOPEN IT

One of two things:

1. A single shared module exports the carve at a `G` PARAMETER, so that all
   four conjuncts state over one name. This is the restatement the
   predecessor's W4 section proposes, and 566's one-frame rebuild is its
   measure.
2. An owner ruling that this row closes on the predecessor's artifact, which
   is in the tree and typechecks, with `[LJ-1.559]`'s term cited at its own
   frame and the difference above as the standing note.

## WHAT I BOUND AND FROM WHERE

Nothing. No import was written, no hole was filled, and no Agda process was
started. The dispatch spent zero seconds of Agda. The brief prices a GO at
about 40 lines and under 30 s, and the brief orders the STOP before any
Agda when the types are not identical; the comparison is section D-10 above,
and the cost of bridging is measured at 155.02 s, 337.30 s and 240.00 s in
the runs cited, each at a cap of one run, none near the heap.

## WHY THIS IS NOT A PROOF

The mathematics was done by `[LJ-1.559]`, which built the term, and by the
predecessor at this task, which built the same conjunct at this frame. This
dispatch closed a parked row: it compared the two types, named the difference,
and cited the measurement. No credit for the term is claimed here.

## A NOTE ON THE WORKTREE

This worktree was forked from `8d087288` (a stale `main` commit) and did not
contain `agents/tasks/LJ-1-559/`. The main tree stands at `pod-cutover`
(`3a0bfb5b`), and this dispatch re-checked the worktree to that commit before
doing anything else. The program's retry path reuses a parked worktree and
seeds only untracked inputs; it does not refresh the fork base. The
maintainer should know.

## GATES RUN

Markdown only; no `.agda` was written or typechecked, and nothing landed in
`src/`. `scripts/gate/check-probes.py --check` and
`scripts/gate/lint-prose.py --check` run from the main tree's venv:
see the dispatch report for the exits.
