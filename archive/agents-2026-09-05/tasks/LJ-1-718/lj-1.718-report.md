# LJ-1.718 report: the repaired `LsetGrounded`, composed from two named hypotheses

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.718
obligation: agents/tasks/LJ-1-718/Probe718.agda::grounded-from-complete
verdict: **NO-GO, stated in
`review-of-grounded-from-complete.md`.** The repaired statement is
delivered as green types (`Probe718.agda:74-102`, `runs/p-2.out`,
`EXIT=0` at `:22`, 9.27 s, peak 1,759,444,992 bytes against the
2,147,483,648-byte wide cap). The codes DO match the hull's δ: the
`Completeness` -> `hull-closed` half composes green across the module
boundary (`runs/d-2.out`, `EXIT=0` at `:22`, 108.47 s). The wall is
the APPLICATION of `At.Convert`: `conv ca cp a sat` does not
elaborate at six shapes, two of them heap walls at the cap
(`runs/d-3.out:4-6`, 282.36 s, peak 2,604,580,864; `runs/d-4.out:4-6`,
283.63 s, peak 2,551,070,720), and the application alone still hangs
in a lean module (`runs/d-7.out`). `[LJ-1.673]`'s report records the
same route dying at `runs/p-4.out`. The term is not declared and no
`grounded-from-complete` name exists in the file, so the witness
meter reads MISSING truthfully and no red probe lies about it.

**W3, ANSWERED.** The brief asked: do `hull-closed` plus `Convert`
plus `IsOrd δ` produce the ambient triple, or do `Completeness`'s
codes fail to match the hull's δ? The second alternative is measured
FALSE (`runs/d-2.out` is the codes flowing into `hull-closed`, green).
The first is blocked by the elaborator at the one step that consumes
`Convert`. The mathematics of the composition is otherwise complete;
the obstruction is the placement of `Convert`'s type
(`Probe673.agda:115-119`, stated inside `At`, applied outside).

Written as a skeleton before any Agda beyond the predecessor read and
filled as each measurement landed (C-22). No commit, no push. I wrote
only inside `agents/tasks/LJ-1-718/`. Agda ran under the caliber the
program set on this pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier,
ONE Agda process at a time. I did not set `GHCRTS`. Nothing is
postulated, the delivered probe carries `--safe` and no hole, and
nothing lands in `src/`. The probe is a raw `.agda` file, so it
carries no ` ```agda ` fence, counts 0 in-fence lines, and the ratio
bar cannot fire on it.

**A HEAP WALL WAS MET, AND THE RESTRUCTURING DUTY WAS SPENT.** Two
runs exhausted the 2 GB cap (`runs/d-3.out:4-6`, `runs/d-4.out:4-6`).
I restructured six ways and tested each new shape at the same cap:
the whole composition (`p-1`, killed at the 900 s tool cap), the
composition with `comp` holed (`d-1`, 300 s cap), a plain-argument
lemma (`d-3`, wall), `conv` + `subst` alone (`d-4`, wall), the bare
`conv` application (`d-5`, 300 s cap), and the bare application in a
lean module without the frame (`d-7`, 300 s cap). The application
alone still hangs, so the wall is reported as a finding, per the
coder clause. Rerunning the SAME code hoping for a different result
was never done; every run after `p-1` is a different shape.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection and it does not start phase 3.
No Boundary clause is in conflict.

**I wrote `review-of-grounded-from-complete.md`.** The obligation is
not inhabited. A `review-of-*.md` is how a coder states a NO-GO; the
critic reads that file.

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

The brief's premises name five bases. All five were read before the
first run:

- `hull-closed` at `inBound` is the consumer of `BoundInStage`
  (`agents/tasks/LJ-1-673/Probe673.agda:100-104`), and
  `bound-from-stage` drops the satisfaction, so the ambient triple
  needs `hull-closed`'s full triple, not the green consumer alone.
- `Convert` is paid at `matrix₃` by `[LJ-1.692]`
  (`agents/tasks/LJ-1-692/Probe692.agda:61-66`), as a CONSTRUCTED
  term, which is the fact the next brief needs (section 5).
- The unrepaired `LsetGrounded` drops `IsOrd δ`
  (`agents/tasks/LJ-1-673/review-of-LJ-1-673-1.md:157-165`), so the
  repair carries `IsOrd` on the supplier AND `IsOrd δ` in the
  obligation's telescope. Both are in the delivered types.
- `[LJ-1.673]` started this name and did not finish it
  (`agents/tasks/LJ-1-673/Probe673.agda:136-144`); `runs/p-4.out`
  still reads Checking.
- `Completeness` is a hypothesis, not inhabited
  (`agents/tasks/LJ-1-673/Probe673.agda:126-130`), with `IsOrd` added
  on the parameter.

The floor was priced before the proof, per the heavy-object ruling of
2026-08-23: statement with a hole standing in for the body, delivered
as `runs/FLOOR.agda.txt` and run under the `.agda` dance. The floor is
120.49 s cold, peak 1,792,933,888 bytes, and the frame itself is not
the problem (`runs/floor-1.out`).

## 2. THE STATEMENT I BUILT

`Probe718.agda` states the brief's target at the frame telescope,
inside `module Build` (`Probe718.agda:60`), with the frame aliased off
`A` so the module instances are one name (`Probe718.agda:66-68`):

- `Convert` is `A.Convert` verbatim (`Probe718.agda:74-75`).
- `Completeness` is `Probe673.agda:126-130` with the critic's repair:
  `IsOrd (fst (val cp))` added on the parameter code
  (`Probe718.agda:81-86`).
- `GroundedFromComplete` is the obligation's whole telescope
  (`Probe718.agda:93-101`): the two suppliers, the matrix's soundness,
  `δ`, `IsOrd δ`, both hull memberships, and the truncated Σ.

The planned proof, which the statement was built for: (1) `hull-member`
reads both memberships as codes; (2) `Completeness` fires there,
`IsOrd (fst (val cp))` by `subst` along `δ`'s readback, the graph
equation by composition with `cong Lset`; (3) `hull-closed` reads the
stage existential as a hull member `a` carrying the `inBound`
satisfaction; (4) `Convert` turns that into the ambient triple at the
code values, and two transports rename them to `Lset δ` and `δ`. Steps
(1)-(3) measured green (`runs/d-2.out`). Step (4) is the wall.

## 3. THE MEASURED GRID

All runs one Agda process at a time, wide caliber from the pane. The
`d`-files are diagnostic shapes kept as `.agda.txt` in `runs/`; none
is a verification target.

| run | shape | seconds | peak (bytes) | outcome |
|---|---|---:|---:|---|
| `floor-1` | statement, hole body, cold | 120.49 | 1,792,933,888 | `EXIT=42`, the designed hole |
| `p-1` | full body, first shape | > 900 | n/a | killed at the tool cap |
| `d-1` | full body, `comp` holed | > 300 | n/a | killed at the tool cap |
| `d-2` | `Completeness` -> `hull-closed` half | 108.47 | 1,771,179,392 | `EXIT=0` |
| `d-3` | full composition, plain-argument lemma | 282.36 | 2,604,580,864 | `EXIT=251`, heap exhausted |
| `d-4` | `conv` + `subst` only | 283.63 | 2,551,070,720 | `EXIT=251`, heap exhausted |
| `d-5` | bare `conv` application | > 300 | n/a | killed at the tool cap |
| `d-6` | `conv`'s domain stated in a signature | 7.59 | 1,229,750,272 | `EXIT=42`, designed hole only |
| `d-7` | bare application, lean module | > 300 | n/a | killed at the tool cap |
| `p-2` | delivered probe, statements only | 9.27 | 1,759,444,992 | `EXIT=0` |

Two facts isolate the poison. First, the SIGNATURE is cheap: `d-6`
states `conv`'s whole domain, `⟨ (a ∷ []) ⊨ᵐ (mapFo val (inBound ca
cp)) ⟩` and the `fst (val c)` environments, and checks in 7.59 s.
Second, the `hull-closed` half is cheap: `d-2` is green at 108.47 s.
The cost fires only when `At.Convert`'s body is computed FOR an
application and its domain compared against the argument's type.

## 4. THE FLOOR, THE PEAK, NO OTHER SHAPE MISSED

The delivered probe's frame floor is the cold `floor-1` run at
120.49 s, and its warm green recheck is `p-2` at 9.27 s. The highest
peak of a finished green run is 1,792,933,888 bytes (`runs/floor-1.out`),
83 percent of the wide cap; the two heap walls are reported as the
finding, not as the price of a shape nobody tried to route around.
`p-1`, `d-1`, `d-5` and `d-7` carry no `ended` line because the
dispatch's tool timeout killed them; that is disclosed here and their
`.out` files are kept as evidence.

## 5. WHAT THE NEXT BRIEF NEEDS

1. **Do not re-dispatch the hypothesis-based composition as stated.**
   Six shapes measured; the application of `At.Convert` is the wall
   (`review-of-grounded-from-complete.md`, section 2).
2. **Fund `Convert` as a CONSTRUCTED term at this frame and compose
   against the construction.** `[LJ-1.692]`'s `hull-convert-at-matrix`
   inhabits `At.Convert` at the `(Lset lam)` instance by construction
   (`agents/tasks/LJ-1-692/Probe692.agda:61-66`). Composing against a
   delivered `Convert` spends the hypothesis instead of assuming it,
   which changes the obligation's content: the mathematician's call.
3. **Or fund the generic unpack at a 3-slot Δ₀ formula**, the
   predecessor's own recommendation
   (`agents/tasks/LJ-1-673/lj-1.673-report.md`, section 12, item 2).
4. **The repaired telescope is settled.** `GroundedFromComplete`
   (`Probe718.agda:93-101`) is the statement the next attempt carries,
   with `IsOrd δ` in the conclusion's own telescope and
   `IsOrd (fst (val cp))` on the supplier. The codes match the hull's
   δ; nothing mathematical reopens.

## 6. W2 ANSWERED

The mathematics is `Probe673`'s `inBound`, the hull's `hull-closed`
and `Probe673`'s `Convert`, all imported and instantiated; the new
code is the composition and the repaired statement only
(`Probe718.agda:60-102`). No generic lemma is restated, and no second
formula or second carrier exists in the write scope.

## 7. PRICE

Non-blank non-comment lines, counted the ledger's way
(`awk 'NF' file | grep -cv '^[[:space:]]*--'`).

| what | lines | at |
|---|---:|---|
| `Probe718.agda`, whole | 44 | `Probe718.agda` (101 lines total) |
| `Build` telescope and aliases | 8 | `Probe718.agda:60-68` |
| `Convert` | 2 | `Probe718.agda:74-75` |
| `Completeness` | 5 | `Probe718.agda:81-86` |
| `GroundedFromComplete` | 9 | `Probe718.agda:93-101` |

The delivered probe is a raw `.agda` file: no ` ```agda ` fence, 0
in-fence lines, the ratio bar cannot fire on it.

## 8. BOUNDARY COMPLIANCE

No commit, no push. The working tree holds exactly the write scope:
`Probe718.agda`, this report,
`review-of-grounded-from-complete.md`, and `runs/` (ten `.out` files,
the `run.sh` wrapper, and the `.agda.txt` diagnostic shapes, none a
verification target). Nothing landed in `src/`. No generated file was
committed, no em dash was written in any language, no secret was
printed, no dependency was added, and no in-file `SPDX-*` header was
written.

## ARCHIVE USED

- `archive/dev/ORCHESTRATION.md`: not read, declined. The dispatch
  mechanics it records played no part in the statement repair or the
  elaboration measurements of this task.
- `archive/dev/DD-archived.md`: not read, declined. The live rulings
  that bind this task reached it through the brief and
  `dev/pod/instructions/coder.md`; the archived decision corpus was
  not opened.
- `archive/dev/PLAN-archived.md`: not read, declined. The plan
  history has no bearing on a probe whose verdict is measured by
  `agda`'s exit and heap, not by the plan's phases.
- `archive/dev/TASKS-archived.md`: not read, declined. The task
  history before LJ-1.673 informed nothing here; the predecessor
  basis came from `agents/tasks/LJ-1-673/` itself.
- `archive/dev/STATUS-archived.md`: not read, declined. The standing
  status is `dev/pod/screen.toml`; the archived status file was not
  opened and no claim in this return rests on it.

## LITERATURE USED

- `dev/literature/level-formula-slot-roles.md`: read and used.
  `dev/literature/level-formula-slot-roles.md:26` reads "`v` at 1,
  `γ` at 2 | **VALUE, ORDINAL**" for Devlin 5.2 (a): the level
  formula's parameter slot carries role ORDINAL, which is the
  literature ground for the critic's repair this task delivers, and
  it is why `IsOrd (fst (val cp))` sits on the supplier and
  `IsOrd δ` in the conclusion's own telescope
  (`Probe718.agda:81-86`, `:93-101`).
- `dev/literature/glossary-review-2026-08.md`: not read, declined.
  No term of this task's write scope was coined here; the glossary
  review bears on translation terms, and this task lands code and
  project records only.
- `dev/literature/BIBLIOGRAPHY.md`: not read, declined. No source
  was consulted beyond the tree's own extracts already cited by the
  predecessor basis.
- `dev/literature/devlin-errata.md`: not read, declined. The Devlin
  5.2 statement reached this task through
  `dev/literature/level-formula-slot-roles.md:26` and the critic
  review; the errata sheet was not opened and no erratum is claimed.
- `dev/literature/primary-sources.md`: not read, declined. No
  primary-source locator was needed; the one locator cited above is
  read from the slot-roles table itself.
