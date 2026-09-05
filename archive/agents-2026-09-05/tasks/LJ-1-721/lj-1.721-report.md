# LJ-1.721 report: the packing, exported at the name the meter reads

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.721
obligation: agents/tasks/LJ-1-721/Probe721.agda::pack-stage
verdict: **GO.** `pack-stage` is delivered at the FILE'S top level
and green: cold EXIT=0 at 1444.25 s and 2,581,348,352 bytes
maximum resident (`runs/p-1.out:4-5,22`), no heap kill. Warm, the
delivered file re-checks in 3.00 s at 712,392,704 bytes
(`runs/p-final.out:3-4,21`). W3 is answered YES: a top-level alias
of the nested `pack-stage` checks, and it costs nothing measurable.

Written only inside `agents/tasks/LJ-1-721/`. No commit, no push.
Agda under the caliber the program set on this pane,
`GHCRTS="-A64m -I0 -M2g"` (recorded in every `.out`'s first line),
the WIDE tier, ONE Agda process at a time. I did not set `GHCRTS`.
Nothing lands in `src/`. Nothing is postulated; the delivered probe
carries `--safe` and no hole (`Probe721.agda:1`). The probe is a raw
`.agda` file, so it carries no fence, counts 0 in-fence lines, and
the ratio bar cannot fire on it.

Scope note. `review-of-pack-stage.md` is in the write scope and is
NOT written, on purpose: it is the NO-GO vehicle (the slot clause),
the outcome is GO, and this report is the record of a GO.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection and it does not start phase
3. No Boundary clause is in conflict.

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

The verdict came from the predecessor's report: **GO** at
`lj-1.720-report.md:9`. The type came from the probe that
typechecked: `PackStage` and `pack-stage` at
`Probe720.agda:98-111`. Per the slot clause, a GO verdict means I
inhabit the brief's type, and I did.

Everything is transcribed verbatim from the 720 delivered probe:
the imports (`Probe721.agda:24-40` from `Probe720.agda:25-41`), the
`Pack` telescope (`Probe721.agda:51-55` from `Probe720.agda:52-56`),
the three lemmas with their explicit codomains
(`Probe721.agda:61-79` from `Probe720.agda:62-84`), and the packing
(`Probe721.agda:89-102` from `Probe720.agda:98-111`). The ONE new
content is the export: two alias lines at the top level
(`Probe721.agda:112,114`), the `[LJ-1.709]` form
(`Probe709.agda:77`).

Premise 4 held. `[LJ-1.700]` is NO-GO on the closed term
`completeness-from-hier`, which is defined nowhere in the tree
(`review-of-LJ-1-700-1.md:167-169`, `Probe700.agda:76-79`), not on
the three lemmas. Nothing here touches `Completeness`; the comment
block of the delivered probe says so in code
(`Probe721.agda:116-118`). The 720 report's reading stands:
`SameHyp` and `HierInStage` remain hypotheses of the components
(`lj-1.720-report.md:229-231`), and `BoundInStage` is not reached.

## 2. THE FLOOR

`runs/floor-1.out`, on the floor shape now snapshotted inert as
`runs/FLOOR721.agda.txt`: the delivered file with all four bodies
holed, the packing type and both top-level aliases in place. The
run paid the cold probe cone (`runs/floor-1.out:4-11`: Probe652,
Probe641, Probe679, Probe673, Probe667 with its W3 file, Probe520,
the 679 W3 file) and reported 128.58 s and 1,780,465,664 bytes
maximum resident (`runs/floor-1.out:30-31`), EXIT=42
(`runs/floor-1.out:48`).

EXIT=42 is the floor doing its job: the only errors are the four
installed holes (`runs/floor-1.out:20-27`). No error points at the
export lines, so the alias form already checked at the floor. The
frame price matches 720's floor, 118.64 s and 1,780,547,584 bytes
(`.pod-state/worktrees/LJ-1-720/agents/tasks/LJ-1-720/runs/floor-1.out:17-18`),
on a shape that differs by the two alias lines: the frame, not the
export, is the cost, and it fits the wide cap with the same ~1.78 GB
margin.

## 3. W3, WHETHER THE TOP-LEVEL ALIAS STILL CHECKS

**YES.** The brief estimated 20 to 60 lines on
`lj-1.720-report.md:13`; the delivered probe is 118 lines, of which
116 are the 720 file it transcribes and 2 are the export
(`Probe721.agda:112,114`). The measured answer:

- The delivered shape is green first try: EXIT=0 at 1444.25 s and
  2,581,348,352 bytes maximum resident (`runs/p-1.out:4-5,22`).
- The alias lines are free at the margin that matters. Against 720's
  p-3, 1350.11 s and 2,591,981,568 bytes
  (`.pod-state/worktrees/LJ-1-720/agents/tasks/LJ-1-720/runs/p-3.out:4-5`),
  the cold wall moved +94.14 s and the resident set moved 10,633,216
  bytes DOWN. I attribute neither movement to the alias: the cones
  are cold in both worktrees and the machine is shared. The
  defensible claim is the exit code and the band: no kill in any of
  the three runs (`grep -c "Heap overflow"` is 0 in
  `runs/floor-1.out` and `runs/p-1.out`), resident at 2.58 GB, the
  same band 720 reported.
- Warm, the interface written by p-1
  (`_build/2.8.0/agda/agents/tasks/LJ-1-721/Probe721.agdai`) rechecks
  in 3.00 s (`runs/p-final.out:3`).

## 4. W2

Answered in code, not in prose. The packing is written ONCE, inside
`module Pack`, at the generic telescope. The two top-level lines are
ALIASES of that one term (`Probe721.agda:112,114`): Agda's module
telescope becomes the leading arguments, so the exported
`pack-stage` IS the nested term, not a second writing of it. The
bodies are the predecessor's, byte for byte. No deadline conflict.

## 5. W4, AND P-l

W4: no module is retired here. Nothing moves to `archive/`.

P-l (`dev/LESSONS.md:2367`): the export names no new type
statement, so it drags no presentation. The component types stay at
the binder's own projections (`Probe721.agda:89-100`), the cure 720
measured; at the delivered term they reduce to `[LJ-1.700]`'s own
types (`lj-1.720-report.md:223-228`).

## 6. THE LAWS IN THE BUNDLE

- **D-10** (`dev/LESSONS.md:1375`). The target of this discharge is
  720's green term at a second NAME. Truth check before the proof:
  no new quantifier, no new mathematical content, so no cardinality
  or Tarskian obstruction is possible; the floor confirmed the frame
  before any body was filled. No corrected target was needed.
- **C-22** (`dev/LESSONS.md:2307`). This file was written as a
  skeleton before any Agda and filled after each run; the three run
  records landed in section 7 as they finished.
- **P-l** (`dev/LESSONS.md:2367`). Section 5.
- **D-26** (`dev/LESSONS.md:1735`). Does not bind: no well-founded
  key is built here.
- **C-42** (`dev/LESSONS.md:3762`). No refutation landed. The
  floor's unsolved metas are the holes the floor installs on
  purpose (`runs/floor-1.out:20-27`), not a refutation of a
  statement, and there is no shape sweep to run.

## 7. RUNS

One Agda process at a time, sequential, caliber from the pane
(`GHCRTS=[-A64m -I0 -M2g]` is every `.out`'s first line).

| run | state checked | time | max resident | exit | record |
|---|---|---|---|---|---|
| floor-1 | all four bodies holed, export in place | 128.58 s | 1,780,465,664 | 42 | `runs/floor-1.out:30-31,48`, holes at `:20-27`, cold cone at `:4-11` |
| p-1 | the delivered file, complete | 1444.25 s | 2,581,348,352 | 0 | `runs/p-1.out:4-5,22` |
| p-final | the delivered file, warm cache | 3.00 s | 712,392,704 | 0 | `runs/p-final.out:3-4,21` |

The ladder honors the 2026-08-23 ruling: the floor priced the frame
before the real attempt, and the real attempt followed it. The
interface exists after p-1, so the acceptance re-check should run at
the warm price.

## 8. PRICE

- The delivered probe: 118 lines, of which 0 are in-fence (raw
  `.agda`, no fence), so the ratio bar divisor is 0 and cannot fire.
- Cold price of the obligation, wide caliber: 1444.25 s and
  2,581,348,352 bytes maximum resident (`runs/p-1.out:4-5`).
- Warm price: 3.00 s and 712,392,704 bytes (`runs/p-final.out:3-4`).
- Three Agda processes, 1575.83 s of measured run time in total
  (section 7).
- The brief's estimate for the term was 20 to 60 lines; 118 landed,
  the extra being the transcription the obligation names and the
  comment block.

## 9. WHAT THE SHAPE RESISTED

Nothing new. The delivered shape checked first try, and the floor
caught no defect: its only errors are the installed holes
(`runs/floor-1.out:20-27`). The two honest findings:

1. The frame is the whole price of this file, and it was already
   paid at 720. Floor to floor, 128.58 s against 118.64 s, the
   shapes differ by two alias lines and the price did not move
   (section 2). A future export of a nested name is not a cost
   question; it is a name question.
2. The margin note carries over. 2.58 GB resident sits above the
   2.3 GB band where `[LJ-1.700]`'s runs were killed
   (`review-of-LJ-1-700-1.md:138-144` names the site). None of my
   three runs was killed, and 720's five were not either; but this
   file sits in the same band, and a consumer that adds to it
   should floor its own frame first.

## 10. WHAT THE NEXT BRIEF NEEDS

- `pack-stage` is delivered at
  `agents/tasks/LJ-1-721/Probe721.agda::pack-stage` AND at the file's
  top level. The top-level name is the import surface: a consumer
  imports `LJ-1-721.Probe721` and reads `Probe721.pack-stage`,
  carrying the `Pack` telescope as seven explicit leading arguments
  `(lam : S) (ordλ : IsOrd lam) (succλ : ...) (X : S) (X⊆Lλ : ...)
  (∅∈λ : ...) (elem : P652.Frame652.A.Elementary ...)`
  (`Probe721.agda:51-55`). `Probe721.PackStage` is exported the same
  way, so the pair `pack-stage : PackStage` is stated at the top
  level exactly as the obligation writes it.
- Consumption is 720's consumption, one argument list earlier:
  `fst (pack-stage lam ordλ succλ X X⊆Lλ ∅∈λ elem)` is the packing
  function (it is `toL`, by computation); `fst (snd (...))` is
  `same-at-codes`; `snd (snd (...))` is `hier-at-code`
  (`lj-1.720-report.md:223-228`).
- `SameHyp` and `HierInStage` remain HYPOTHESES. Nothing here
  discharges them, and `Completeness` is still not inhabited:
  the obstruction argument of `Probe700.agda:76-79` stands
  unrefuted.
- Prices to budget: cold re-check 1444.25 s / 2.58 GB resident on
  the wide caliber (`runs/p-1.out:4-5`); warm 3.00 s / 0.71 GB
  (`runs/p-final.out:3-4`).
- The tracked supply this GO creates: `[LJ-1.717]`'s successor may
  consume the packing at its export name instead of restating the
  three bodies (`lj-1.720-report.md:239-240` named this consumption;
  the export is what makes it cheap).

## 11. GATES

`make check` is not run here: the task lands no `src/` file and no
commit; the program gates the return. The brief's mandatory check
was run and its output is pasted verbatim below.

```
$ /Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-721
check-survey-quotes: LJ-1-721 clean (0 note(s), 0 defect(s))
rc=0
```

Note on the interpreter path: this worktree carries no `.venv`
(git-ignored, not copied into worktrees), so the project's pinned
venv interpreter at the main checkout ran the checker. The checker
resolves the repository root from the script's own location, so the
clean verdict above is this worktree's report.

## ARCHIVE USED

- **`archive/dev/DD-archived.md` DECLINED.** Line 1 reads, verbatim:
  `# THE \`DD\` RULING SERIES, archived in full 2026-08-18`. Not
  used: the ruling series is closed, and this task adds no ruling.
- **`archive/dev/ORCHESTRATION.md` DECLINED.** Line 1 reads,
  verbatim: `# ORCHESTRATION: the orchestrator's operating rules`.
  Not used: the dispatch process is not consulted by a probe.
- **`archive/dev/PLAN-archived.md` DECLINED.** Line 1 reads,
  verbatim: `# ARCHIVED 2026-08-20`. Not used: the live status is
  `dev/pod/screen.toml`, which this return does not restate.
- **`archive/dev/TASKS-archived.md` DECLINED.** Line 1 reads,
  verbatim: `# Archived task index: the \`L3.32-T\` series`. Not
  used: that series is not a predecessor of this export task.
- **`archive/dev/STATUS-archived.md` DECLINED.** Line 1 reads,
  verbatim: `# STATUS-archived: the goal table of the internalization
  route`. Not used: the goal table of a closed route names no stage
  lemma and no caliber.

## LITERATURE USED

- **`dev/literature/devlin-errata.md` DECLINED.** Line 1 reads,
  verbatim: `# Devlin errata: documented error classes
  (do-not-repeat checklist)`. Not used: no scanned quote and no
  Devlin reading is under test; the obligation is an export of
  delivered terms.
- **`dev/literature/formalizations-landscape.md` DECLINED.** Line 1
  reads, verbatim: `# Formalization landscape sweep: L, V=L,
  condensation, AC-in-L, GCH-in-L, rud (OPEN item 7)`. Not used: the
  task compares no formalization; it moves one term to one name.
- **`dev/literature/glossary-review-2026-08.md` DECLINED.** Line 1
  reads, verbatim: `# Glossary review: the 119 pre-protocol
  entries`. Not used: no term is proposed and no glossary question
  arose.
- **`dev/literature/level-formula-slot-roles.md` DECLINED.** Line 1
  reads, verbatim: `# The level-hood formula: arity, what it binds,
  what stays free`. Not used: no level formula is stated here; the
  packing's types are the predecessor's.
- **`dev/literature/primary-sources.md` DECLINED.** Line 1 reads,
  verbatim: `# Primary sources, second round: Jensen manuscript,
  Devlin, Jech`. Not used: the export cites no source; the
  mathematics is the tree's own, taken from Probe720.
