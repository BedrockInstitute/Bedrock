# LJ-1.727-SPLIT report: the supply name, split into its own file

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.727-SPLIT
obligation: agents/tasks/LJ-1-727-SPLIT/Probe727Split.agda::level-at-pair
verdict: **GO.** The obligation's term is delivered:
`agents/tasks/LJ-1-727-SPLIT/Probe727Split.agda::level-at-pair`,
transcribed from `[LJ-1.727]`'s green delivery, typechecks at
EXIT=0 cold-in-worktree 2538.40 s (`runs/p-1.out:13,31`), warm
recheck 3.70 s (`runs/p-2.out:3,21`), and the name is exported at the
file's top level (`Probe727Split.agda:139`), the alias form the meter
reads. No heap kill, no hole, nothing postulated. W3 is answered GO:
the alias still converts in a fresh file. No `review-of-*.md` is
written, because that channel states a NO-GO and this verdict is GO.

Written as a skeleton before the first Agda run and filled after each
run landed (C-22; `dev/LESSONS.md:2307`). No commit, no push.
Written only inside `agents/tasks/LJ-1-727-SPLIT/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M2g"`
(recorded as the first line of every `.out`), the WIDE tier, ONE
Agda process at a time; I did not set `GHCRTS`. Nothing lands in
`src/`. The probe is a raw `.agda` file, so it carries no fence,
counts 0 in-fence lines, and the ratio bar cannot fire on it.

**NO HEAP WALL WAS MET.** `grep -c "Heap overflow"` is 0 in both
`.out` files, and peak RSS was instrumented this time (`/usr/bin/time
-l`, which 727 did not carry): 2536194048 B on the cold run
(`runs/p-1.out:14`), 700940288 B warm (`runs/p-2.out:4`), the
difference being the elaboration cone the warm run does not reload.

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

The predecessor is `[LJ-1.727]`, read in its worktree. Its verdict is
GO on the supply term and NO-GO only on the obligation name it
deliberately did not inhabit
(`/Users/alsg/Agentic/Bedrock/.pod-state/worktrees/LJ-1-727/agents/tasks/LJ-1-727/lj-1.727-report.md:9-13`).
Per the slot clause, the type I take is the one that typechecked
there: `Probe727.agda:138-143`, exported by alias at
`Probe727.agda:166`. The brief's four premises were checked and stand:

1. The obligation name of 727 is absent on purpose (report:9-12).
2. `level-at-pair` is delivered green at the top level (report:13-14).
3. The type is the unbounded level reading at the packed pair
   (`Probe727.agda:138-143`).
4. W3 on `completeness-from-pack` is answered NO (report:18-19). This
   file does not restate, inhabit or name that target as a term; the
   NO-GO already has its review file.

## 2. WHAT THE FILE CARRIES

`agents/tasks/LJ-1-727-SPLIT/Probe727Split.agda`, 139 lines, is a
line-by-line transcription of 727's `At727` frame narrowed to the
supply term's own support:

- `pack`, `toL`, `same-at-codes`, `graph-at-pair`, `level-at-pair`,
  in that order, bodies verbatim from `Probe727.agda:104-145`.
- The export `level-at-pair = At727Split.level-at-pair` at
  `Probe727Split.agda:139`, the `[LJ-1.709]/[LJ-1.721]/[LJ-1.727]`
  alias form: the frame telescope becomes the leading arguments.
- Trimmed, because their only consumers did not move: 727's
  `hier-at-code`, `cfp-shape` and `bounded-demand` (they serve 727's
  obligation shape, not the supply term), and the imports only they
  used, `hierL` and `Lset→isL`.
- Kept despite being type-only: `LsetGraphAt` (the declared type of
  `graph-at-pair`, the reading the supply consumes) and the full
  `LEM` parameter (every imported module takes it).

The obligation name of 727 does not appear in the delivered file at
all, not even in comments: this file has no view of that target.

## 3. THE RUNS

The 2026-08-23 floor ruling was answered BEFORE the run, with a
measurement rather than a new one: the floor of this exact frame is
727's own, which confirmed every type-level composition at
`Probe727.agda:103,112,126,142` (the `PackStage` projections, the
`Lset-defines` unification, the `levelFo-Σ₁` projection) before its
bodies were filled. This task transcribes a measured-green term and
adds no new proof, so a second floor run would re-price a measured
frame, and the single complete-file run is itself the W3 answer.

| run | state checked | time | peak RSS | exit | record |
|---|---|---|---|---|---|
| p-1 | the delivered file, complete; cone COLD (fresh worktree, no cached interfaces) | 2538.40 s | 2536194048 B | 0 | `runs/p-1.out:13,14,31` |
| p-2 | the delivered file, warm recheck | 3.70 s | 700940288 B | 0 | `runs/p-2.out:3,4,21` |

Two Agda processes, sequential, 2542.10 s of measured run time in
total. The cold run built this worktree's whole cone (652, 641, 520,
679, 673, 667 with both `W3` files, 721, then this file:
`runs/p-1.out:3-12`).

## 4. W2

Answered in code, not in prose. The mathematics is written once, at
the generic frame `At727Split`, and consumed at predecessor exports:
721's `pack-stage`, Hierarchy's `Lset-defines`, 520's
`levelFo-Σ₁`, 679's `SameHyp`/`SameAsGraph`/`At` — all called, none
restated. The one new top-level name is the alias
(`Probe727Split.agda:139`). No deadline conflict.

## 5. W4, P-l, AND THE LAWS IN THE BUNDLE

- **W4**: no module is retired here. Nothing moves to `archive/`.
- **P-l** (`dev/LESSONS.md:2367`): the supply term's conclusion names
  the level formula's presentation, `fst (P520.levelFo-Σ₁ zero
  (suc zero))`. As at 727 (its report, section 5): that IS the
  supply's honest output, the projection `SameAsGraph`'s own type
  produces, and at the binder it reduces to the component types 720
  and 721 delivered. No opaque stage is dragged.
- **D-10** (`dev/LESSONS.md:1375`): the residue's truth was priced
  before this dispatch: the target I was handed is the term 727
  measured green, not the false one its W3 refuted, and the
  re-measurement at the new site confirms it. The open target 727's
  D-10 analysis recorded (the bounded `BoundInStage` decision at the
  codes of `∅` and `Lset ∅`) is NOT priced here and stays open.
- **C-22** (`dev/LESSONS.md:2307`): the report was a skeleton before
  the first Agda run; the probe, both run records and every section
  landed as each step finished.
- **D-26** (`dev/LESSONS.md:1735`): does not bind; no well-founded
  key is built here.
- **C-42** (`dev/LESSONS.md:3762`): no refutation lands here, so no
  sweep is owed by me. The one refutation this task stands on is
  `[LJ-1.716]`'s via 727's W3, and its sweep is already measured
  (`agents/tasks/LJ-1-727/lj-1.727-report.md`, section 5).

## 6. PRICE

- The delivered probe: 139 lines, of which 0 are in-fence (raw
  `.agda`, no fence), so the ratio bar divisor is 0 and cannot fire.
- Cold-in-worktree price, wide caliber, fresh worktree (cone
  included, paid once): 2538.40 s (`runs/p-1.out:13`). Warm price:
  3.70 s (`runs/p-2.out:3`).
- Peak RSS: 2536194048 B cold (`runs/p-1.out:14`), 700940288 B warm
  (`runs/p-2.out:4`); no heap kill in either run at `-M2g`.
- The brief's estimate for the W3 probe was 20 to 50 lines. The
  delivered file is 139: the meter's obligation names the term at a
  file's top level, and the term consumes the frame, so the probe is
  the frame plus the term. The W3 question itself (does the alias
  still convert) cost nothing beyond the transcription: one run, GO.

## 7. WHAT THE NEXT BRIEF NEEDS

- The supply name now exists in the tree:
  `agents/tasks/LJ-1-727-SPLIT/Probe727Split.agda::level-at-pair`,
  top level, export at `:139`. A consumer takes the alias form: the
  seven frame arguments, then SameHyp, two codes, `IsOrd` on the
  parameter, and the level equation.
- The supply closes only the UNBOUNDED level reading. The bounded
  demand is still open where 727 left it: BRIDGE 2's production side,
  with the site-fact bill named in
  `agents/tasks/LJ-1-727/review-of-completeness-from-pack.md`.
- The D-10 probe 727 named (decide `BoundInStage` at the codes of
  `∅` and `Lset ∅`) is still the cheapest decisive next measurement;
  this task did not touch it.
- Prices to budget: warm 3.70 s (`runs/p-2.out:3`); a fresh worktree
  pays the cone once, 2538.40 s (`runs/p-1.out:13`); the cone is
  built in this worktree's `_build`.

## 8. GATES

`make check` is not run here: the task lands no `src/` file and no
commit; the program gates the return. The brief's mandatory check was
run and its output is pasted verbatim below.

```
$ /Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-727-SPLIT
check-survey-quotes: LJ-1-727-SPLIT clean (0 note(s), 0 defect(s))
rc=0
```

Note on the interpreter path: this worktree carries no `.venv`
(git-ignored, not copied into worktrees), so the project's pinned
venv interpreter at the main checkout ran the checker, as in
`lj-1.721-report.md` and `lj-1.727-report.md` before it. The checker
resolves the repository root from the script's own location.

## ARCHIVE USED

- **`archive/dev/ORCHESTRATION.md` DECLINED.** Line 1 reads,
  verbatim: '# ORCHESTRATION: the orchestrator's operating rules'.
  Not used: the dispatch process is not consulted by a transcription.
- **`archive/dev/DD-archived.md` DECLINED.** Line 1 reads, verbatim:
  '# THE `DD` RULING SERIES, archived in full 2026-08-18'. Not used:
  the ruling series is closed, and this task adds no ruling.
- **`archive/dev/PLAN-archived.md` DECLINED.** Line 1 reads,
  verbatim: '# ARCHIVED 2026-08-20'. Not used: the live status is
  `dev/pod/screen.toml`, which this return does not restate.
- **`archive/dev/TASKS-archived.md` DECLINED.** Line 1 reads,
  verbatim: '# Archived task index: the `L3.32-T` series'. Not used:
  that series is not a predecessor of this supply term.
- **`archive/dev/STATUS-archived.md` DECLINED.** Line 1 reads,
  verbatim: '# STATUS-archived: the goal table of the internalization
  route'. Not used: the goal table of a closed route names no level
  formula and no caliber.

## LITERATURE USED

- **`dev/literature/level-formula-slot-roles.md` DECLINED.** Line 1
  reads, verbatim: '# The level-hood formula: arity, what it binds,
  what stays free'. Not used: the formula this file names is the
  tree's own projection, read off `Probe520`'s export; the slot-role
  vocabulary was not consulted.
- **`dev/literature/glossary-review-2026-08.md` DECLINED.** Line 1
  reads, verbatim: '# Glossary review: the 119 pre-protocol entries'.
  Not used: no glossary term is proposed here.
- **`dev/literature/devlin-errata.md` DECLINED.** Line 1 reads,
  verbatim: '# Devlin errata: documented error classes
  (do-not-repeat checklist)'. Not used: no scanned quote is under
  test; the transcribed term is the tree's own.
- **`dev/literature/primary-sources.md` DECLINED.** Line 1 reads,
  verbatim: '# Primary sources, second round: Jensen manuscript,
  Devlin, Jech'. Not used: the mathematics cited is the tree's own,
  at the file:line addresses of the probes and chapters.
- **`dev/literature/BIBLIOGRAPHY.md` DECLINED.** Line 1 reads,
  verbatim: '# Bibliography for the rud route'. Not used: no
  literature route is consulted by this transcription.
