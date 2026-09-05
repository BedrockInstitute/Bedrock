# LJ-1.634 report: land ingredient (iv), one binder

## HEAD
head_slot: coder
machine: exclusive
agda_tier: heavy

## VERDICT

**GO. `class-pred-iv` is landed and the whole tree typechecks.**

- The term, at the site the brief orders: `src/L/BoundedSubset.lagda.md:
  1512-1518` (`class-pred-iv`, inside `module Devlin55` → `BoundedSubsetAt`
  → `RGraph`), with the site in `At` at `src/L/BoundedSubset.lagda.md:
  1431-1510`.
- The obligation name, at the module top level where the meter reads it:
  `src/L/BoundedSubset.lagda.md:1746-1753` (the `BSA634` alias plus
  `class-pred-iv = BSA634.RGraph.class-pred-iv`). The witness resolves it:
  `runs/witness-2.out`, **`0 UNRESOLVED of 1`, 6.11 s, EXIT=0**; the
  obligation closes, delta -1.
- The whole tree: `runs/w3-3.out`, `Checking Everything`, **EXIT=0, 17.50 s,
  2.73 GB peak**, caliber `-A64m -I0 -M4g` set by the program on this pane; I
  did not set it; one Agda process at a time.
- The target file alone: `runs/target-16.out`, **EXIT=0, 20.76 s, 3.06 GB
  peak**.
- The gates: `lint-agda` and `lint-prose` exit 0 on the touched files;
  `check-survey-quotes.py LJ-1-634` reports clean (0 defect(s)).
- Standing figure, from `scripts/measure/ledger.py --brief`: 34,044 lines over
  101 masters, measured from HEAD.

**THE ONE BINDER WAS THE WHOLE DEFECT.** [LJ-1.630]'s diagnosis was tested,
not trusted: I copied that worktree's landing (122 inserted lines), changed
the `IH` binder from `(δ : Sx)` to `(δ : V ℓ)` at the two sites (the `At`
module parameter, `src/L/BoundedSubset.lagda.md:1433`, and the
`class-pred-iv` signature, `src/L/BoundedSubset.lagda.md:1514`), plus one
comment name (`S` to `Sx`). No second error appeared anywhere: the probe
passed, the file passed, the tree passed. **The carrier mismatch was one
site, not many: it was the binder, in two spellings of the same signature.**

## WHAT THE BRIEF COST

The brief said: if the one binder is the whole defect, this is a token edit
and a re-run. It was. Three lines changed relative to [LJ-1.630]'s landing
(`src/L/BoundedSubset.lagda.md:1433`, `:1514`, the comment at `:1406`), and
the price was the whole-tree check itself: **18.09 s at HEAVY, 2.47 GB**,
against the brief's estimate of a frame that fit in 11.46 s / 814 MB up to
[630]'s error (`runs/w3-1.out` here;
`.pod-state/worktrees/LJ-1-630/agents/tasks/LJ-1-630/runs/accept-1.out:25`).
The difference: 630 measured a failing run; mine is the closed one, and its
downstream masters recheck over an already-green
`L.BoundedSubset` interface (7 `Checking` lines in `runs/w3-1.out`; the
file's own 16.49 s is in `runs/target-1.out`, cold).

The probe cost 1.44 s / 320 MB at the same caliber (`runs/probe-3.out`).

## THE SHAPE THAT RESISTED

Nothing in the tree resisted. Two of my own probe shapes did, and both are
mine, not the tree's:

1. `runs/probe-2.out`, UnequalTerms at
   `agents/tasks/LJ-1-634/Probe634.agda:56`: I stated the 5-argument
   application's result as `SC.Upper.P δ`. In this tree
   `P α` (`src/L/StageCardinal.lagda.md:540-542`) is
   `IsOrd α → ⟨ α ∈ˢ sucV α₀ ⟩ → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → Σ[ f ∈ (⟪ Lset α ⟫ →
   ⟪ α ⟫) ] ...`, so the application `IH δ δ∈α oδ δ∈suc infδ` returns the
   `P`-body Σ, which is the shape the landed `IHδ` row declares
   (`src/L/BoundedSubset.lagda.md:1451-1452`). The probe now states that
   shape (`Probe634.agda` row 2) and passes.
2. Row 1 of the same file pins the V binder against this file's `P` at a
   bare V. Both rows together are the type-level statement that the one
   binder is the whole defect as far as the site's types are concerned.

**I weakened nothing.** The statement is [LJ-1.608]'s own spelling at its
own signature; the only edit inside the term is the binder, which the brief
orders and which the predecessor's own error names.

## W2

The rule is stated in the brief's obligation and answered here: the
mathematics is written once at the site's parameters and instantiated, not
fixed. The graph variables live at the constructible carrier `Sx`
(`src/L/BoundedSubset.lagda.md:1413-1414`), the stages are bare `V` elements,
and the whole site is parameterized over
`(β, oβ, β∈suc, infβ, IH, m, ω∈δ)`
(`src/L/BoundedSubset.lagda.md:1431-1436`); the shared parts (the composed
embedding, the fiber value equation, the two-direction graph shape) are the
generic `L.StageCardinal` kit, instantiated once at the module's own `α`
(`src/L/BoundedSubset.lagda.md:1397`). No fixed form was written, so no
deadline conflict is reported.

## RUNS

All at the pane caliber `-A64m -I0 -M4g` (HEAVY, set by the program on this
pane; I did not set it), one Agda process at a time, wall-capped through
`runs/run.sh`.

- `runs/probe-1.out`: NotInScope on `𝒮ᵥ`, 1.81 s. Missing import in my
  probe, not in the tree.
- `runs/probe-2.out`: UnequalTerms, 1.03 s. My probe's result type was the
  full `P δ` function type where the application returns the `P`-body Σ.
  Restructured the probe to state the P-body Σ, the shape the landed `IHδ`
  row declares; this is a probe-shape fix, not a heap wall.
- `runs/probe-3.out`: **GO, EXIT=0, 1.44 s, 320 MB peak.** Both rows of
  `Probe634.agda` typecheck.
- `runs/target-1.out`: **GO, EXIT=0, 16.49 s, 1.85 GB peak**, `src/L/
  BoundedSubset.lagda.md` with the landed row, cold. The frame price holds:
  [630]'s floor for this same file was 15.79 s
  (`.pod-state/worktrees/LJ-1-630/agents/tasks/LJ-1-630/runs/heavy-1-floor.
  out`), so the landed row adds about 0.7 s to the file.
- `runs/w3-1.out`: **GO, EXIT=0, 18.09 s, 2.47 GB peak**, `src/Everything.
  lagda.md`. No heap wall; no error anywhere in the log.
- Rounds 2–3, the top-level name. The direct spellings failed in term
  position: `runs/target-2.out` (NotInScope on `L.StageCardinal`),
  `runs/target-3.out` (NotInScope on `Devlin55.BoundedSubsetAt`),
  `runs/target-8.out` (NotInScope on `Devlin55.RGraph`), `runs/target-10.out`
  and `runs/target-11.out` (NotInScope on the module alias in term position).
  The alias-dotted form resolved: `runs/target-14.out` (the obligation path
  typechecks; the only error left is in my own probe line). The final file:
  `runs/target-16.out`, **GO, EXIT=0, 20.76 s, 3.06 GB peak**. The alias adds
  about 4 s to the file's own price over round 1's 16.49 s, because it
  re-instantiates the nine-parameter telescope.
- `runs/witness-2.out`: **GO, `0 UNRESOLVED of 1`, 6.11 s, EXIT=0**; the
  obligation `src/L/BoundedSubset.lagda.md::class-pred-iv` is resolved at the
  module top level.
- `runs/w3-3.out`: **GO, EXIT=0, 17.50 s, 2.73 GB peak**, `src/Everything.
  lagda.md`, final tree. No heap wall; no error anywhere in the log.

Ratio bar: in-fence lines of the write-scope master are 1514 (the project's
non-blank in-fence caliber; round 1 measured 1501 at the same count); 17.50 /
1514 = 0.0116, below the 0.0123 bar, so no escalation on that row.

## WHAT THE NEXT BRIEF NEEDS

1. **Ingredient (iv) is in the tree.** The `class-pred` table now has (i),
   (ii), (iv) and (v); **(iii) is the remaining ingredient**. The next
   brief names it and the site it lands in; nothing here presumes a shape
   for it.
2. **The site is at the right instantiability.** `class-pred-iv` takes its
   `IH` at the bare `V` binder exactly as [LJ-1.608] delivered it
   (`agents/tasks/LJ-1-608/Probe608.agda:177-184`); an assembler that
   consumes it must pass an `IH` whose result is the `P`-body Σ at the
   member stage, and the three extra arguments (`IsOrd δ`, `δ∈suc`, `infδ`)
   that `P` carries are all derivable at the site as the landed rows do
   (`src/L/BoundedSubset.lagda.md:1442-1449`).
3. **`L.BoundedSubset` rechecks in about 20.8 s at HEAVY with both rows in**
   (`runs/target-16.out`); round 1's nested row alone priced 16.49 s.
   If the next landing is in this file again, price against the 20.8 s floor.
4. **[LJ-1.630] left no report** (it parked with bare evidence, the backlog
   item at `dev/pod/maintainer-backlog.md:54`). Its worktree at
   `.pod-state/worktrees/LJ-1-630/` is the source of this landing; the
   predecessor clause is satisfied by its runs plus the maintainer record,
   and its verdict for the statement is no longer in question because the
   statement now closes here.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: read. It is the 464-row index archived
  at the POD cutover; `archive/dev/LJ-dispatch-index.md:3-4` states "These are
  the 464 dispatch rows that lived in `dev/PLAN.md` section 11 until the POD
  cutover." It indexes pre-cutover codes; this task's predecessors are POD
  tasks and its evidence lives in `agents/tasks/`, so nothing from it is
  cited in the verdict.
- `dev/ARCHIVE.md`: surveyed by grep for `boundedsubset`, `devlin55` and
  `class-pred`; no hit, no row concerns this landing. Not read.
- `archive/dev/JOURNAL-archived.md`: declined, not read; the task is
  self-contained in its runs and predecessor evidence.
- `archive/dev/JOURNAL.md`: declined, not read; same reason.
- `archive/dev/ORCHESTRATION.md`: declined, not read; it governs the
  pre-POD orchestration and this dispatch's channel is the brief and this
  report.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: read. The landing is Devlin II.5's 5.5;
  `dev/literature/devlin-II5.md:145` opens "### 1.5 5.5 to 5.8: the GCH
  chain" and `dev/literature/devlin-II5.md:148` carries the lemma's
  conclusion line "> κ (or more generally if x ⊆ L_α for some α < κ), then
  x ∈ L_κ." It confirms the module's address and that 5.5's proof leans on
  the same order machinery this file instantiates; it does not prescribe
  the Agda shape, which came from [LJ-1.608].
- `dev/literature/truncation-and-selection.md`: declined, not read; the
  landed row uses no selection over truncation.
- `dev/literature/geology.md`: declined, not read; no carrier-choice
  question arose beyond the one binder the brief and the error both name.
- `dev/literature/digest.md`: declined, not read; the specific chain is
  carried by `devlin-II5.md`, which I used.
- `dev/literature/primary-sources.md`: declined, not read; no primary text
  was consulted.

## RE-DISPATCH (round 2)

**Status at re-dispatch:** round 1 landed the nested term and passed whole-tree,
but parked on acceptance conjunct 6 (`lint`, a survey-quote line mis-citation)
with `obligations_open 1, obligations_delta 0` (`runs/accept-1.out`). The delta
was the second finding: the obligation `src/L/BoundedSubset.lagda.md::class-pred-iv`
is metered by a witness that derives `Target.class-pred-iv` at the module TOP
LEVEL (`scripts/pod/witness.py`), and the nested row, inside
`Devlin55.BoundedSubsetAt.RGraph.At`, was NotInScope there. Measured: witness
run round 2, `NotInScope` at the witness's `witness` line, 2.45 s.

**The shape that landed.** At the module top level, a value whose body is a
path into the parameterized submodule `Devlin55.BoundedSubsetAt` is not a
term in this Agda: the fully applied path `Devlin55.BoundedSubsetAt κ ... sq
.RGraph .class-pred-iv` is NotInScope (`runs/target-3.out`), and so is the
path through a module alias written in term position
(`runs/target-10.out`, `runs/target-11.out`). What is a term is the dotted
reference through the alias: the alias carries the site's nine-parameter
telescope in module position, and the obligation name is one dotted
reference (`src/L/BoundedSubset.lagda.md:1746-1753`):

    module BSA634 (κ : S) ... (sq : ...) = Devlin55.BoundedSubsetAt ...
    class-pred-iv = BSA634.RGraph.class-pred-iv

That is the form that typechecked (`runs/target-14.out` first, then
`runs/target-16.out` on the final file) and the form the witness resolves
(`runs/witness-2.out`). The nested row stays at the site the brief orders
(`src/L/BoundedSubset.lagda.md:1512-1518`); the top row is the name the
obligation meter reads. This keeps the house form in spirit: `class-pred-i`
sits at the module top level of `L.Constructible` (where the witness resolves
it), so a `class-pred` ingredient lands where its obligation name resolves.

**Round 3 acceptance state.** Every round 1 evidence line holds at its round
3 measurement: whole tree `runs/w3-3.out` (EXIT=0, 17.50 s, 2.73 GB), target
`runs/target-16.out` (EXIT=0, 20.76 s), witness `runs/witness-2.out` (0
UNRESOLVED of 1), gates clean (`lint-agda`, `lint-prose`,
`check-survey-quotes.py LJ-1-634`, all exit 0 / 0 defects). The two things
that parked round 2 are both closed. The conjunct 6 lint failure was a
survey-quote mis-citation in this report; it is corrected
(`archive/dev/LJ-dispatch-index.md:3-4`, `dev/literature/devlin-II5.md:148`).
The open obligation with delta 0 is resolved: the witness reads the name at
the module top level and the delta is -1.
