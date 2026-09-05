# LJ-1.444 report: land the ambient route's endpoint, with its one residue named

slot: `coder`. Written early as a skeleton and filled as the stop
landed (C-22). No commit, no push. I wrote only in
`agents/tasks/LJ-1-444/`. I did not set `GHCRTS`. The pane caliber is
`GHCRTS="-A64m -I0 -M8g"`. No Agda process ran on a master or a
probe. No heap event.

TARGET: land ONE term `chain-upper` in
`src/L/StageBound.lagda.md`, under the named hypothesis `AmbToCoded`
at `[LJ-1.414]`'s delivered type.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection. It does not start phase 3.
No Boundary clause is in conflict.

## THE STOP

The brief says: read `agents/tasks/LJ-1-442/lj-1.442-report.md`
before anything else; if that file does not exist, or its verdict is
not `GO`, or `src/L/StageBound.lagda.md` is not in the tree, write
nothing and stop.

**Two of those three held.**

| # | gate | this tree |
|---|---|---|
| 1 | `agents/tasks/LJ-1-442/lj-1.442-report.md` exists | NO. `ls agents/tasks/LJ-1-442` fails. `git ls-files` has no `LJ-1-442` path. |
| 2 | that report's verdict is `GO` | UNREADABLE here. The file is absent. |
| 3 | `src/L/StageBound.lagda.md` is in the tree | NO. `ls src/L/StageBound.lagda.md` fails. `src/Everything.lagda.md:393` imports `L.BoundedSubset`. The next import is `L.Choice.Transversal`. There is no `import L.StageBound`. |

Which of the three happened: **(1) and (3)**. (2) cannot be answered
from this tree.

I wrote no Agda. I did not create `src/L/StageBound.lagda.md`. A
brief that names a master a predecessor creates, when that
predecessor is not in the tree, is a stop and not a guess
(`dev/pod/instructions/coder.md:20-23`). The brief's own gate is
`agents/tasks/LJ-1-444/LJ-1.444.md:27-29`.

## VERDICT

**NO-GO.** The obstruction is `review-of-chain-upper.md`. The
ambient route's endpoint is not in `src/` in this tree. The residue
`AmbToCoded` is not named in a master in this tree.

This is not a refutation of `chain-upper`. See D-10.

## 0. D-10, BEFORE ANY AGDA

### 0.1 `[LJ-1.420]`

VERDICT line, `agents/tasks/LJ-1-420/lj-1.420-report.md:53`:

    **GO.** `chain-upper` typechecks

The hypothesis type it says it took,
`agents/tasks/LJ-1-420/lj-1.420-report.md:29-35`:

    amb-to-coded :
        (x : S) (ox : IsOrd (fst x)) → ⟨ ω ∈ˢ fst x ⟩
      → (d : S) → ⟨ fst d ∈ˢ fst x ⟩ → (⟨ fst d ∈ˢ ω ⟩ → Empty.⊥)
      → ∥ ⟪ fst x ⟫ ↪ ⟪ fst d ⟫ ∥₁
      → ∥ Σ[ F ∈ S ] InjCode F x d ∥₁

cited at the probe, never at a brief
(`agents/tasks/LJ-1-414/Probe414.agda:134-139`). Site in the 420
probe: `agents/tasks/LJ-1-420/Probe420.agda:76-80`.

The verdict is `GO`. I did not stop on 420.

MEASURED line count of `[LJ-1.420]`'s file, which replaces the
brief's estimate of about 110 in-fence lines: **58** non-blank
non-comment lines in `agents/tasks/LJ-1-420/Probe420.agda` (99 total
lines, 85 non-blank). I opened the file and counted. The brief's
own basis already named 58. Comparables of SHAPE, not of size.
Nothing is funded against them.

MEASURED median of 420, quoted from its report at
`agents/tasks/LJ-1-420/lj-1.420-report.md:54`: median **1.66 s** on
three forced rechecks. That is the W3 estimate. W3 did not run
here, so there is no measured master time to compare.

### 0.2 `[LJ-1.414]`

VERDICT line, `agents/tasks/LJ-1-414/lj-1.414-report.md:51`:

    **NO-GO on `amb-to-coded`. GO on HALF B.**

**It is a NO-GO.** That is why `AmbToCoded` enters this chapter as a
PARAMETER and never as a term.

The statement is not named FALSE. It is not decidable in this tree
(`agents/tasks/LJ-1-414/lj-1.414-report.md:20`). HALF B is green
(`agents/tasks/LJ-1-414/Probe414.agda:115-128`). HALF A has no
producer. The obligation is a hole at
`agents/tasks/LJ-1-414/Probe414.agda:139`.

A predecessor taken as a hypothesis is the REPORT and never the
brief (`dev/pod/audit-2026-08-20.md:41-42`, "the brief, not the
result"). The 414 report does not name the statement FALSE. Taking
the type as a parameter is legal. Inhabiting it is not.

### 0.3 Projection for projection, as `[LJ-1.437]` does

Form copied from `agents/tasks/LJ-1-437/lj-1.437-report.md:62-70`.

420 hypothesis (`Probe420.agda:76-80`) against 414 delivered type
(`Probe414.agda:134-139`):

| # | 420 hypothesis | 414 obligation | same? |
|---|---|---|---|
| 1 | `(x : S)` | `(x : S)` | yes |
| 2 | `(ox : IsOrd (fst x))` | `(ox : IsOrd (fst x))` | yes |
| 3 | `⟨ ω ∈ˢ fst x ⟩` | `⟨ ω ∈ˢ fst x ⟩` | yes |
| 4 | `(d : S)` | `(d : S)` | yes |
| 5 | `⟨ fst d ∈ˢ fst x ⟩` | `⟨ fst d ∈ˢ fst x ⟩` | yes |
| 6 | `(⟨ fst d ∈ˢ ω ⟩ → Empty.⊥)` | `(⟨ fst d ∈ˢ ω ⟩ → Empty.⊥)` | yes |
| 7 | `∥ ⟪ fst x ⟫ ↪ ⟪ fst d ⟫ ∥₁` | `∥ ⟪ fst x ⟫ ↪ ⟪ fst d ⟫ ∥₁` | yes |
| 8 | `∥ Σ[ F ∈ S ] InjCode F x d ∥₁` | `∥ Σ[ F ∈ S ] InjCode F x d ∥₁` | yes |

The binder name `amb-to-coded` is not a type. 420 wraps it as a
module parameter (`Probe420.agda:75-81`). 414 wraps it as a
definition with a hole (`Probe414.agda:134-139`). The brief names
the same Pi as a `Type` alias `AmbToCoded`. That is packaging. The
types are the same. I did not stop on a mismatch. I did not weaken
either side.

The conclusion of 420 is the consumer's own
`stage-card-upper` (`src/L/StageCardinal.lagda.md:564-565`), reached
as `SC.Upper.stage-card-upper` (`Probe420.agda:95-99`).

### 0.4 The unfolding repair

The audit names an explicit `unfolding` where three probes each
sealed their own `κL` (`dev/pod/audit-2026-08-20.md:128-145`).
`[LJ-1.420]` postdates that audit's scope.

**The repair is already inside `[LJ-1.420]`'s file** at
`agents/tasks/LJ-1-420/Probe420.agda:58-66`:

    opaque
      unfolding P406.κL P413.κL
      unfolding-cost :
          ...
      unfolding-cost = P406.init-at-kappa

420's report, `agents/tasks/LJ-1-420/lj-1.420-report.md:60-61`:
"The unfolding join of the two `κL` seals was heap-safe." Median of
that W3 alone: 1.53 s, peak RSS 419790848 bytes
(`agents/tasks/LJ-1-420/lj-1.420-report.md:97-98`). No heap event.
I did not re-run it. I did not copy it into a master.

## 1. W2 (DD4)

The rule: write the mathematics once at a generic carrier and
instantiate it.

`[LJ-1.420]` already does that. `Probe420.agda:25-26` is generic in
`ℓ`. `α₀` and `oα₀` are the consumer's own parameters
(`src/L/StageCardinal.lagda.md:15-16`). `chain-upper` quantifies
over a generic `δ : V ℓ`. `amb-to-coded` is generic in `x` and `d`.
No band, no numeral except `ω`, no site.

I wrote no Agda, so there is no fixed form to report and no W2
conflict. A later dispatch that lands the chapter must keep that
genericity. A deadline does not permit the fixed form.

W4 does not fire: no module was retired.

## 2. W3: `SC.Upper.stage-card-upper` inside a master

**NOT RUN.** The brief names the instantiation of `L.StageCardinal`
inside a MASTER, as 420 reaches it at `Probe420.agda:99` under the
module application at `Probe420.agda:75-96`. The chapter to write
that in is `src/L/StageBound.lagda.md`. That file is not in this
tree. Writing the chapter up to the module application would be
writing the master the gate forbade.

The W3 estimate, quoted from 420 at
`agents/tasks/LJ-1-420/lj-1.420-report.md:54`, is median **1.66 s**.
There is no measured master time in this tree to compare with it.

No heap event, because no Agda ran on this obligation.

## 3. A descendant commit that this worktree does not have

This worktree is detached at `e41c233` (`pod: admit LJ-1.444`).
Commit `a983bb7` (`pod: LJ-1.442 done, row task-lj-1-442-go`) is a
descendant of that HEAD. `git merge-base --is-ancestor HEAD a983bb7`
holds. `git merge-base --is-ancestor a983bb7 HEAD` fails.

`git show --stat a983bb7` lists both files the gate asked for:

- `agents/tasks/LJ-1-442/lj-1.442-report.md` (248 lines added)
- `src/L/StageBound.lagda.md` (103 lines added)
- `src/Everything.lagda.md` (`import L.StageBound`)
- `dev/ledger.toml` (one `gch_wing` row)

I read those files with `git show`. I did not check them out. I did
not merge `a983bb7`. The brief's stop is on THIS tree.

From `git show a983bb7:agents/tasks/LJ-1-442/lj-1.442-report.md`,
the VERDICT line opens `**GO.**`. The master in that commit lands
`bounded-from-trunc` (truncated consumer), not `chain-upper`. The
442 report says `[LJ-1.443]` lands `Distance`. So even on that
commit, 444's job would be to ADD `AmbToCoded` and `chain-upper` to
a chapter that already holds the truncated consumer. That is the
shape the 444 brief names ("both routes' endpoints ... in one
chapter"). It is not the shape of THIS tree.

I did not bring those files here. Copying a successor commit into
this worktree would invent the premise the gate said to refuse.

This task does not depend on `[LJ-1.441]` and did not wait for it.
`agents/tasks/LJ-1-441/` is also absent from this tree.

## THE RATIO

No master was written. In-fence line count of this task's write
scope under `src/` is **0**. Measured Agda seconds on the obligation
are **0**. The bar is 0.0123 seconds per in-fence line. A ratio
with divisor 0 is not a rate. The bar cannot fire on a report-only
return.

## WHAT THIS DOES NOT MEASURE

This task measures nothing about the TRUNCATED route, whose residue
is `SqCollect` in this same chapter after `[LJ-1.443]`, and the two
residues are not known to be the same statement. Nobody has measured
that, and this task does not.

This task also measures nothing about `L.StageCardinal` inside a
master. 420 measured it inside a probe (median 1.66 s). 442, on
the descendant commit, measured `Devlin55.BoundedSubsetAt`
instantiation inside `StageBound` (median 15.29 s, from `git show`
of that report). Combining both instantiations in one master is
unmeasured. This return does not guess that price.

`chain-upper` under a hypothesis is not a proof of the
stage-cardinal bound. It is a proof that ONE statement stands
between this tree and that bound on this route. I did not land
that term. I do not claim the trophy. I did not touch
`src/Landmarks.lagda.md`.

The architecture is a CANDIDATE (`dev/pod/screen.toml:10`). Only a
measurement settles it. This task did not take that measurement.

## make check

- Before any write: **0.01 s**, exit 2, peak RSS 2113536 bytes.
  Stopped at `venv-check`: `No virtualenv at .venv/. Run: make venv`.
  No Agda process started. `runs/make-check-before.out`.
- `make venv` then installed the pinned set from
  `requirements-dev.txt`. That is not an Agda run and it does not
  set `GHCRTS`.
- After the reports land: **14.63 s**, exit 0, peak RSS 909934592
  bytes. One Agda process, pane caliber `-A64m -I0 -M8g`. Agda
  printed no `Checking` line. The catalog was warm. Closure 99
  masters. No file under `src/` changed. `runs/make-check-after.out`.

`.venv/bin/python scripts/measure/ledger.py --brief` printed:

    standing 33,078 lines over 97 masters, measured from HEAD

That figure does not include `src/L/StageBound.lagda.md`. The
master is not in this tree.

## ARCHIVE USED

- `archive/dev/JOURNAL.md`: read at `:1`. Quote: `# ARCHIVED 2026-08-20`.
  Declined, not used. The per-episode journal is retired. The stop
  is that a live predecessor is missing from this worktree.
- `archive/dev/LJ-dispatch-index.md`: read at `:1`. Quote:
  `# THE `LJ` DISPATCH INDEX, archived 2026-08-18`. Declined, not
  used. It is the retired dispatch index. The live gate is the 442
  report path the brief named.
- `archive/dev/JOURNAL-archived.md`: read at `:1`. Quote:
  `# Archived journal: the retired route`. Declined, not used.
  Retired-route journal. This stop is about a live master.
- `archive/dev/ORCHESTRATION.md`: read at `:1`. Quote:
  `# ORCHESTRATION: the orchestrator's operating rules`. Declined,
  not used. The live operating rules are `AGENTS.md` and the slot
  file.
- `archive/dev/DECISIONS-archived.md`: read at `:1`. Quote:
  `# Archived decisions: the D series`. Declined, not used. The
  live clauses that bind this slot are W2 and W4.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: read at `:1`. Quote:
  `# Devlin II.5: the Condensation Lemma and the GCH in L`.
  Declined, not used. The stop is a missing master, not II.5.
- `dev/literature/truncation-and-selection.md`: read at `:1`. Quote:
  `# Truncation and selection: how the two literatures pick a witness`.
  Declined, not used. D-10 here is a type comparison of two probes,
  not a truncation argument.
- `dev/literature/digest.md`: read at `:1`. Quote:
  `# Digest: the orthodox form of the rud route, pinned from the collected literature`.
  Declined, not used. No rud-route step is consulted.
- `dev/literature/terms-2026-08.md`: read at `:1`. Quote:
  `# The terminology dossier: fourteen renderings for the owner's ruling`.
  Declined, not used. No glossary term is at issue.
- `dev/literature/geology.md`: read at `:1`. Quote:
  `# Geology dossier: set-theoretic geology sources and the five questions`.
  Declined, not used. Geology is not this consumer.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start an Agda process on a master or a probe.
- I did not write `src/L/StageBound.lagda.md`.
- I did not edit `src/Everything.lagda.md`.
- I did not edit `dev/ledger.toml`.
- I did not inhabit `AmbToCoded`. I did not postulate it. I did not
  substitute a different type for it.
- I did not claim the trophy.
- I did not wait for `[LJ-1.441]`.
- I did not merge or check out `a983bb7`.
- I did not pad a chapter. There is no chapter.

## WHAT THE NEXT BRIEF NEEDS

Re-dispatch this obligation on a tree that already contains
`a983bb7` (`pod: LJ-1.442 done`). On that commit the master exists,
its 442 verdict is `GO`, and `chain-upper` is still absent. 444's
job there is to ADD `AmbToCoded` and `chain-upper` to the chapter
442 created for `bounded-from-trunc`.

Do not inhabit `AmbToCoded`. `[LJ-1.414]` is NO-GO on that name
(`agents/tasks/LJ-1-414/lj-1.414-report.md:51`). It is a parameter.

The 420 and 414 types match projection for projection. No repair
of the hypothesis is needed.

The unfolding repair is already in
`agents/tasks/LJ-1-420/Probe420.agda:58-66`. Copy that one clause.
420 measured it heap-safe at 1.53 s.

W3 on the re-dispatch is the StageCardinal instantiation inside the
master that already instantiates `Devlin55.BoundedSubsetAt`. 420
measured StageCardinal alone in a probe (1.66 s). 442 measured
BoundedSubsetAt alone in the master (15.29 s, from `git show` of
that report). The sum is not a measurement. Re-measure at the combined site. A
measured cure does not transfer by analogy.

Keep `α₀` and `oα₀` as module parameters or as arguments; 420 kept
them as module parameters (`Probe420.agda:25-26`) because they are
the consumer's own (`src/L/StageCardinal.lagda.md:15-16`).

Do not wait for `[LJ-1.441]`.

`chain-upper` under a hypothesis is not a proof of the
stage-cardinal bound. It is a proof that ONE statement stands
between this tree and that bound on this route. Write that sentence
and no stronger one.
