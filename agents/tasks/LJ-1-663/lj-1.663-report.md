# LJ-1.663 report: the two laws that buy everything downstream

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.663
obligation: agents/tasks/LJ-1-663/Probe663.agda::level-laws
verdict: **STOP ON THE OBLIGATION, AND THE STOP IS
`review-of-level-laws.md`. COMPLETE RESISTS AT `SatAtPacked`, NOT AT THE
WITNESS SEARCH. THE MEMBERSHIP HALF IS BUILT AND GREEN.**

The obligation reads `missing` (`runs/meter-obligation.out`,
`1 UNRESOLVED of 1`, `probe_red=False`: the probe is green and the name is
absent, not broken). Eleven other names are green
(`runs/meter-names.out`, `0 UNRESOLVED of 11`).

**READ THESE FOUR SENTENCES BEFORE YOU QUEUE ANYTHING.**

1. **THE ANSWER IS NO, AND THE RESISTING LAW IS COMPLETE, IN THE FORM
   THE BRIEF ASKED TO NAME.** `level-laws` is not written. `Sound` and
   `Complete` are copied verbatim from
   `agents/tasks/LJ-1-659/Probe659.agda:155-161`. Neither is inhabited at
   any formula.
2. **COMPLETE IS NOT ONE WALL.** It splits. The membership conjunct
   `Lset(γ) ∈ Lset lam` is a theorem, `value-in-stage`
   (`Probe663.agda:118-123`). The packing is `packed` (`:126-127`). The
   arrow `SatAtPacked lf → Complete lf` is `complete-from-sat`
   (`:144-146`). So W3's "truncated existence at ordinal γ" is not a
   search for `v`. The truncation is over satisfaction of the formula at
   the packed pair.
3. **`SatAtPacked delivered` IS THE WALL, AND AGDA PRINTS IT AS AN
   EXISTENTIAL OVER A THIRD SLOT.** `runs/NO-SAT.agda.txt` /
   `runs/nosat-2.out`, exit 42: the packed equality is not `_⊨c_`, and
   `_⊨c_` of `[LJ-1.651]`'s formula unfolds to a bound `K` in the stage
   plus the Δ₀ matrix. That is Devlin's Φ with the bound existentially
   closed, searched inside `Lset lam`. It is `[LJ-1.52]`'s 2.6(ii)
   (`archive/dev/LJ-dispatch-index.md:101`) under this task's names.
4. **THE GRADE WALL DID NOT RECUR.** The formula is the one `[LJ-1.651]`
   already certified as Σ₁. This task did not rebuild it. Premise 3 is
   confirmed rather than repaired: Agda's unfolding of the two-slot
   reading is a three-slot matrix under one `∃̇`.

Written as a skeleton before any Agda beyond the floor and filled as each
answer landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-663/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier, ONE Agda process at a time. I
did not set `GHCRTS`. Nothing is postulated, every delivered file carries
`--safe`, the delivered probe carries no hole, and nothing lands in `src/`.
The probe is a raw `.agda` file, so it carries no ` ```agda ` fence, counts 0
in-fence lines, and the ratio bar cannot fire on it.

**EVERY NUMBER BELOW IS MEASURED WITH A WARM `src/` INTERFACE CACHE.** No
number here is a cold-cache number, and this report does not bound one.

The standing direction (`dev/pod/direction.md`) says one SRC collection
after LJ-1, not after `[LJ-2.5]`. This task is LJ-1 work. It does not start
that collection and it does not start phase 3. No Boundary clause is in
conflict.

## 1. THE FLOOR, AND THE IMPORT IS STILL CHEAP

Coder clause, owner 2026-08-23: price the frame before the term. The honest
way to take `[LJ-1.651]`'s formula is to IMPORT it. `[LJ-1.659]` measured
that import at 5.82 s and 857,849,856 bytes
(`agents/tasks/LJ-1-659/lj-1.659-report.md:62-64`). This task re-measured
the same frame with the two law types added and no proof:

| run | file | exit | wall | peak bytes |
|---|---|---|---|---|
| `floor-1` | `runs/Floor663.agda` | 0 | 5.45 s | 851,230,720 |
| `floor-final` | same, interface removed | 0 | 3.62 s | 715,128,832 |

40 percent of the 2,147,483,648-byte wide cap at the first run, 33 percent
at the recheck. No restructuring. The 2026-08-23 wall is still about probe
chains, not about one import of `Probe651`.

## 2. D-10, BEFORE THE PROOF

The target is Devlin's biconditional at the stage
(`dev/literature/devlin-II5.md:219-222`). I did not find a cardinality or
Tarskian obstruction to it at `lam` a limit. `[LJ-1.642]` already recorded
that the frame admits `lam = ω`
(`agents/tasks/LJ-1-642/lj-1.642-report.md:234-241`), and Devlin's (b) is
stated at `α > ω`. That does not refute the target. It says a supplier
routed through (b) inherits an extra hypothesis the frame does not carry.

The class-carrier pair is delivered: `Lset-only`
(`src/L/Hierarchy.lagda.md:334-335`) and `Lset-defines` (`:646-648`). The
stage pair is the residue `[LJ-1.52]` pinned
(`archive/dev/LJ-dispatch-index.md:101`). I did not prove the target false.

## 3. WHAT WAS BUILT, AND WHAT EACH THING COSTS

Every name below is metered green in `runs/meter-names.out`.

| name | line | what it is | hypothesis |
|---|---|---|---|
| `delivered` | 71 | `[LJ-1.651]`'s term, by import | none |
| `Sound` / `Complete` | 76 / 79 | the two laws, as types, verbatim | none |
| `LevelLaws` | 86 | the brief's obligation, as a type | none |
| `index-of` | 103 | ordinal of the stage is in `lam` | none |
| `Lset∈suc` | 110 | `Lset γ ∈ Lset (suc γ)` | none |
| `value-in-stage` | 118 | **membership half of Complete** | none |
| `packed` / `packed-fst` | 126 / 129 | that member as `SL` | none |
| `SatAtPacked` | 135 | **satisfaction half of Complete, as a type** | none |
| `complete-from-sat` | 144 | `SatAtPacked → Complete` | the satisfaction |

The probe is 163 lines, 75 non-blank non-comment.
`runs/p-final.out`: exit 0 in 3.75 s at 730,890,240 bytes, re-elaborated with
its interface removed.

**W2.** Nothing is proved twice. `value-in-stage` instantiates delivered
lemmas (`rank-fix`, `rank-Lset`, `𝒟ₒ-intro`, `Lset-suc`, `Lset-mono`) at
this frame's `lam`. The class-carrier pair `Lset-only` / `Lset-defines` is
cited and not rebuilt. I did not meet a conflict between W2 and a deadline.

**W4.** Nothing was retired and nothing was deleted. No `dev/ARCHIVE.md` row
is owed.

## 4. W3, COMPLETE: THE ESTIMATE WAS ABOUT THE WRONG HALF

The brief named Complete, "the truncated existence at ordinal γ", at 150 to
320 lines, from `[LJ-1.651]`'s 60-line analogue. **Section 2 of the probe is
the membership half and the split, 28 non-blank non-comment lines
(`Probe663.agda:89-146`), and it answers in three parts.**

### 4.1 THE WITNESS `v` IS FREE

`value-in-stage` (`:118-123`) is the EnvSupply spelling
(`src/L/Coding/EnvSupply.lagda.md:127-129`) plus `rank-fix`, `rank-Lset`,
`succλ` and `Lset-mono`. It does not mention any formula. `packed-fst` is
`refl`.

### 4.2 THE TRUNCATION IS OVER SATISFACTION

`complete-from-sat` (`:144-146`) is a one-line packing. Given
`SatAtPacked lf`, Complete of `lf` costs nothing more.

### 4.3 SATISFACTION IS THE 2.6(ii) WALL, AND THE GRADE WALL DID NOT RECUR

`runs/nosat-2.out:6-18` is the refusal. The packed equality is not `_⊨c_`.
The right-hand side is a truncated existential over a third slot, the bound
`K`, then `[LJ-1.651]`'s `step2` under `mapFo slide` and `renameFo (liftρ
swap)`. **That is the three-slot Δ₀ matrix with the bound existentially
closed, read at the stage.** Premise 3 (`[LJ-1.652]`: ask for three slots,
not two) is the shape Agda printed. The two-slot obligation hides the third
slot under `∃̇`. Closing that `∃̇` inside `Lset lam` is Devlin 2.6(ii), the
sequence `(L_δ | δ ≤ γ)` as a member of the stage
(`dev/literature/devlin-II5.md:220-222`).

The grade wall of `[LJ-1.646]` does not recur here: this task did not build a
formula, and `[LJ-1.651]` already certified `lset-formula` as Σ₁ with two
unbounded `∃̇` (`agents/tasks/LJ-1-651/lj-1.651-report.md:96-98`). The count
for the shape that Agda unfolded is that same count: two unbounded `∃̇` (the
closures of `u` and `K`) over the Δ₀ core. No new count is owed.

**Sound is uninhabited, and I did not spend the rest of the dispatch on
it.** The class-carrier decode is `Lset-only`
(`src/L/Hierarchy.lagda.md:334-335`). The bounded-to-machine decode at a
real `K` is `HierInK` (`agents/tasks/LJ-1-532/lj-1.532-report.md:171`). That
is the same 2.6(ii) wall from the uniqueness side. A second copy of the wall
is not a second measurement.

## 5. WHAT THE NEXT BRIEF NEEDS

**5.1 THE OBLIGATION TO RESTATE.** Not `level-laws`. It is

```
SatAtPacked delivered
```

`Probe663.agda:135-138` gives the type, at `[LJ-1.651]`'s formula and
`[LJ-1.651]`'s slot order. `complete-from-sat` (`:144-146`) turns that into
`Complete`. `[LJ-1.659]`'s `level-from-laws`
(`agents/tasks/LJ-1-659/Probe659.agda:199-214`) then turns the pair into
`LevelFormula`. Do not fund Complete's membership half again.

**5.2 IT HAS A HISTORY, AND THE HISTORY IS THE SAME OBJECT.** 
`archive/dev/LJ-dispatch-index.md:101` records `[LJ-1.52]`, "The level-hood
adequacy at the hull", as `PINNED, not discharged`. `[LJ-1.494]` named
`hier-in-stage`
(`agents/tasks/LJ-1-494/review-of-GraphSatAtStage.md:47-53`). `[LJ-1.610]`
wall 1 named 2.6(ii)
(`agents/tasks/LJ-1-610/review-of-graph-stage.md:18-30`). `[LJ-1.642]` wall 4
named it again
(`agents/tasks/LJ-1-642/lj-1.642-report.md:210-227`). **Price the next brief
against that record, not against this task's 75 lines.**

**5.3 PREMISE 3 IS CONFIRMED.** The literature's free pair is VALUE,
ORDINAL (`dev/literature/level-formula-slot-roles.md:36-38`). The Σ₀ matrix
has a third slot, the bound (`:26`, row 4, arity 3 in Φ). Agda unfolded the
two-slot reading to that third slot. A brief that wants the Δ₀ matrix to
cross a collapse should ask for the three-slot form, as `[LJ-1.652]` said.
A brief that wants Complete at two slots is asking for the existential
closure of that matrix inside the stage, which is 2.6(ii).

**5.4 SOUND IS NOT CLOSED AND IS NOT THIS TASK'S WALL TO RE-PRICE.** If the
next brief wants Sound at `_⊨c_`, the decode is `HierInK` plus `Lset-only`.
Do not price it as a new object.

**5.5 C-42, AND THIS TASK DID NOT RUN THE SWEEP.** The stop measures ONE
site: `SatAtPacked delivered`. It says nothing about how many other
delivered two-slot readings hide the same bound. The sweep is a recon
dispatch.

## 6. HEAP AND TIME, IN FULL

| run | file | exit | wall | peak bytes |
|---|---|---|---|---|
| `floor-1` | `runs/Floor663.agda` | 0 | 5.45 s | 851,230,720 |
| `floor-final` | `runs/Floor663.agda`, interface removed | 0 | 3.62 s | 715,128,832 |
| `p-1` | `Probe663.agda`, first full check | 0 | 4.04 s | 730,890,240 |
| `p-final` | `Probe663.agda`, interface removed | 0 | 3.75 s | 730,890,240 |
| `nosat-1` | `runs/NO-SAT.agda`, first attempt, `[NotInScope]` on `⊨` | 42 | 3.02 s | 718,520,320 |
| `nosat-2` | `runs/NO-SAT.agda.txt`, the designed refusal | 42 | 3.03 s | 605,372,416 |
| `meter-obligation` | the brief's obligation | 42 | 2.95 s | not measured |
| `meter-names` | 11 names, grouped | 0 | 3.41 s | not measured |

**The highest peak of any run is 851,230,720 bytes, 40 percent of the
2,147,483,648-byte wide cap, and it is a GREEN run.** No run walled. No run
came near the 900 s wall cap enforced by the perl alarm (`runs/run.sh`).
**No heap wall was met, so the restructuring clause was not exercised.**

The only failure that was not a designed refusal was `nosat-1`:
`[NotInScope]` on a class-carrier `⊨` this file did not open. The designed
refusal is `nosat-2`. Both were run as `.agda` and the file that cannot
typecheck is named `runs/NO-SAT.agda.txt`.

**Every `.agda` file under this task home typechecks.** There are two,
`Probe663.agda` and `runs/Floor663.agda`. The one file that cannot
typecheck is named `.agda.txt`.

The brief estimated 150 to 320 lines. The probe is 163 lines: inside the
estimate, and it does not inhabit the obligation. The 75 non-blank
non-comment lines are the split, not Complete.

## 7. WORKING TREE

`git status --porcelain` reads `?? agents/tasks/LJ-1-663/` and nothing else.

- `agents/tasks/LJ-1-663/Probe663.agda`: the probe, green (p-final).
- `agents/tasks/LJ-1-663/lj-1.663-report.md`: this report.
- `agents/tasks/LJ-1-663/review-of-level-laws.md`: the stop.
- `agents/tasks/LJ-1-663/runs/`: every run, the floor, the red file and the
  two meters.

No `src/` change. No file under `_build/` authored (the interface cache
entries are Agda's own). Not committed, not pushed.

## ARCHIVE USED

- **`archive/dev/ORCHESTRATION.md`**: **DECLINED.** It is the archived
  operating document, superseded by
  `dev/memos/LJ-4-pod-program-design.md`. Nothing in this task turns on how
  the loop is operated.
- **`archive/dev/DD-archived.md`**: **DECLINED.** It is the archived DD
  series. The live rulings are `dev/pod/rulings.toml`. This task applies
  W2 and W4 from the slot file and does not reopen a DD row.
- **`archive/dev/PLAN-archived.md`**: **DECLINED.** It is the construction
  registry as it stood on archival day. The live status is
  `dev/pod/screen.toml`.
- **`archive/dev/STATUS-archived.md`**: **DECLINED.** It is the archived
  goal table of the internalization route. The live obligation is this
  brief's `level-laws`.
- **`archive/dev/TASKS-archived.md`**: **DECLINED.** It is the archived
  `L3.32-T` index. The operative history for this task is the LJ-1
  predecessors named in the premises, plus
  `archive/dev/LJ-dispatch-index.md:101` (STANDING, cited in section 5.2).

## LITERATURE USED

- **`dev/literature/level-formula-slot-roles.md`**: **READ, AND IT IS
  PREMISE 4 AND SECTION 5.3.** At
  `dev/literature/level-formula-slot-roles.md:28` the line reads

  > | 7 | Jech 13.13 | A Π₂ SENTENCE `σ`: `(M,∈) ⊨ σ` iff `M = L_δ` for a limit `δ` | **0** | everything | nothing | level-hood is a property of the CARRIER | `_build/literature/jech13.txt:605-614` |

  That is the zero-slot row. The two-slot law is at `:36`:

  > Rows 3, 4, 5, 6, 8 and 9 agree. **A level-hood formula leaves exactly the two

  and at `:37`:

  > slots its conclusion uses.** No source leaves anything else free.

  The obligation is that two-slot form. Row 4 at `:26` is the three-slot Φ,
  which is the matrix Agda unfolded under Complete's `∃̇`. Jech's zero-slot
  row is not the object this brief asked for, and I did not inhabit a
  carrier sentence in place of the two-slot pair.
- **`dev/literature/BIBLIOGRAPHY.md`**: **DECLINED.** It is the citation
  register. The slot-role table already names the sources this task used.
- **`dev/literature/glossary-review-2026-08.md`**: **DECLINED.** It is a
  terminology review. This task adds no `dev/glossary.toml` entry and
  proposes none.
- **`dev/literature/devlin-errata.md`**: **DECLINED.** It is a do-not-repeat
  checklist of OCR error classes. The load-bearing Devlin lines are in
  `devlin-II5.md` (STANDING), cited in section 2 and section 4.3.
- **`dev/literature/primary-sources.md`**: **DECLINED.** It is the second
  fetch round. The slot-role digest and `devlin-II5.md` already carry the
  statements this task used.
