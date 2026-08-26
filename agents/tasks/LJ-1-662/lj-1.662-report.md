# LJ-1.662 report: the existential half of the hood

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.662
obligation: agents/tasks/LJ-1-662/Probe662.agda::hoodexists-at-levelhood0
verdict: **STOP ON THE OBLIGATION, AND THE STOP IS
`review-of-hoodexists.md`. The pinning is done and green. The transport the
brief expected to be the risk is NOT the risk: it is built. What blocks the
obligation sits one layer earlier, at the stage, and it is the chapter's own
priced residue.**

The obligation reads `missing` (`runs/meter-obligation.out`,
`1 UNRESOLVED of 1`, `probe_red=False`: the probe is green and the name is
absent, not broken). Twenty-one other names are green
(`runs/meter-names.out`, `0 UNRESOLVED of 21`).

**READ THESE SIX SENTENCES BEFORE YOU QUEUE ANYTHING.**

1. **THE ALPHABET GAP THAT STOPPED `[LJ-1.657]` DOES NOT ARISE AT THE
   CHAPTER'S OWN SHAPE.** `[LJ-1.657]` stopped because `[LJ-1.650]`'s
   `LevelFormula` is typed at `Code` and nothing relabels out of `Code`
   (`agents/tasks/LJ-1-657/Probe657.agda:83-84`). The chapter's `LevelHood0`
   matrix is typed at `CS.S` and it is **CONSTANT-FREE**: `count-hood2 = refl`
   (`Probe662.agda:119`) and `φ₀-inv` (`Probe662.agda:127`) are green. **The
   pinned formula `Probe662.agda:122` exists.**
2. **PREMISE 4's STALENESS IS CURED BY IMPORT AND NOT BY COPY.** `pro`
   (`Probe662.agda:179`) is `[LJ-1.654]`'s delivered `PiReflectsOrd`, and
   `pro-restates-657` (`Probe662.agda:172`) inhabits `[LJ-1.657]`'s named type
   with `λ p → p`, so Agda checks the match rather than my reading of it.
3. **THE EXISTENTIAL HALF NEVER READS THE SOUNDNESS HALF**, so this task takes
   the covering half ALONE (`CoverP`, `Probe662.agda:191`), certified against
   `[LJ-1.657]`'s bundled type by `cover-restates-657` (`Probe662.agda:197`).
   The brief's "do not build `HoodSoundP`" is answered by construction.
4. **PREMISE 3 IS NOW MEASURED AT THE VALUE AND NOT ONLY AT THE ORDINAL.**
   `level-in-stage` (`Probe662.agda:268`) proves `Lset γ` is a stage member
   outright. So `CoverP` splits, and what remains of it is `SatAtLevel`
   (`Probe662.agda:284`): the SATISFACTION and nothing else.
5. **THE WHOLE OBLIGATION NOW COSTS EXACTLY TWO FACTS**, `SatAtLevel φ₀` and
   `ElemDown`, and `ElemDown` is discharged at the chapter's own consumer
   (`src/L/BoundedSubset.lagda.md:1667-1668`).
6. **AND `SatAtLevel φ₀` CANNOT BE EARNED AT `LevelHood0`'s OWN ARITY.** The
   leaf agreement needs one `KFacts` and the tree's only value of it sits at
   fourteen environment slots (`src/L/Condensation.lagda.md:7389`, `:7411`);
   `LevelHood0` offers five, and all five are committed
   (`src/L/BoundedSubset.lagda.md:68-72`, `:841-842`). Section 3 of
   `review-of-hoodexists.md` is that counting fact.

Written as a skeleton before any Agda beyond the floor and filled as each
answer landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-662/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier, ONE Agda process at a time. I
did not set `GHCRTS`. Nothing is postulated, the delivered probe carries
`--safe` and no hole, and nothing lands in `src/`. The probe is a raw `.agda`
file, so it carries no ` ```agda ` fence, counts 0 in-fence lines, and the
ratio bar cannot fire on it.

**EVERY NUMBER BELOW IS MEASURED WITH A WARM `src/` INTERFACE CACHE**
(708 `.agdai` files under `_build/` at the start of the task). No number here
is a cold-cache number, and this report does not bound one.

## 1. THE FLOOR, MEASURED BEFORE ANY PROOF

The standing coder clause orders a floor before a heavy object.
`runs/FLOOR.agda.txt` states the three predecessors by import and nothing
else.

| run | frame | wall s | peak RSS bytes | exit |
|---|---|---|---:|---:|
| `runs/floor-1.out` | 653, 654 and 657, all COLD in this worktree | 15.34 | 1,112,309,760 | 0 |
| `runs/floor-2.out` | the same, warm | 3.23 | 699,842,560 | 0 |

`runs/floor-1.out:5-9` shows all five predecessor probes checked inside that
run, so `[LJ-1.649]`, `[LJ-1.650]`, `[LJ-1.653]`, `[LJ-1.654]` and
`[LJ-1.657]` are green in THIS worktree and not only in their own.

**THE FRAME IS 0.70 GB AND THE TASK'S CEILING IS 2 GB.** That ratio is why
sections 5 and 6 exist.

## 2. THE PINNED FORMULA, AND WHY THE ALPHABET GAP DOES NOT ARISE

`HoodExistsP` demands `Formula (⊥* {ℓ-suc ℓ}) 2`
(`agents/tasks/LJ-1-653/Probe653.agda:283`). The chapter states its matrix at
`Formula CS.S 4`, at the environment `u ∷ v ∷ γ ∷ K ∷ []`
(`src/L/BoundedSubset.lagda.md:68-72`, `:848-849`). Two moves cross the gap
and both are green.

**THE RE-SLOTTING.** `hood2` (`Probe662.agda:110`) closes the bound `K` by
`∃̇` and the unused slot by the chapter's own bounded existential over `K`,
and permutes what is left to `v ∷ γ ∷ []`. The permutation is `ρ`
(`Probe662.agda:88`), four clauses.

**THE ERASURE, AND IT IS THE FINDING.** `count-hood2 : countFo hood2 ≡ 0` is
`refl` (`Probe662.agda:119`). The chapter's whole bounded code-set
description carries NO constant, so `FOL.Count`'s `erase` applies and
`φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2` exists (`Probe662.agda:122`). `φ₀-inv`
(`Probe662.agda:127`) is `erase-inv` and says the erasure is faithful.

I measured the `refl` alone before believing it: `runs/COUNT.agda.txt`,
5.48 s and 619,692,032 bytes (`runs/count-1.out`, exit 0). The whole pinned
block alone is `runs/PIN.agda.txt`, 23.44 s and 882,819,072 bytes
(`runs/pin-1.out`, exit 0).

**THIS CONTRADICTS NOTHING `[LJ-1.657]` MEASURED.** That task's stop is about
`Formula Code 2`, and `Code` is inhabited by a constructor
(`agents/tasks/LJ-1-657/Probe657.agda:81`), so no relabelling leaves it. The
chapter's shape is not typed at `Code`, so the refutation does not reach it.

## 3. THE COMPOSITION, AND WHAT EACH HYPOTHESIS COSTS

`[LJ-1.657]` routed the pinned existential half from THREE hypotheses
(`agents/tasks/LJ-1-657/Probe657.agda:435-437`). This task deletes one and
halves another.

| hypothesis | status here | at |
|---|---|---|
| `PiReflectsOrd` | **DISCHARGED**, by import from `[LJ-1.654]` | `Probe662.agda:179` |
| `LevelFormulaP`, soundness half | **DROPPED**, never read | `Probe662.agda:191` |
| `LevelFormulaP`, covering half | kept, then split by premise 3 | `Probe662.agda:284` |
| `ElemDown` | kept, and the chapter discharges it | `src/L/BoundedSubset.lagda.md:1667-1668` |

`hoodExistsP-from-cover` (`Probe662.agda:215`) is the transport. It is
`[LJ-1.657]`'s shape (`Probe657.agda:146-183`) with the soundness slot gone
and `pro` supplied inside, so the caller sees two hypotheses and not three.

**W2 (DD4), ANSWERED, AND WITH ONE CONFLICT REPORTED.** Every term of this
file is generic in the formula `φ` and is instantiated at the pinned one
ONCE, in `AtLevelHood0` (`Probe662.agda:310-343`). No fact is proved twice.

**THE CONFLICT IS `[LJ-1.657]`'s BUNDLING AND IT IS WORTH A LINE IN THE NEXT
BRIEF.** `LevelFormulaP` (`agents/tasks/LJ-1-657/Probe657.agda:412-419`) is a
`Σ` of a soundness half and a covering half. The existential route reads only
the second. A consumer that HAS the second and not the first cannot call that
file's term at all, so this task re-derived it. **The cure is to split the
`Σ`, not to re-derive it again.** `cover-restates-657` (`Probe662.agda:197`)
certifies that my half is exactly the predecessor's, with `snd ∘ snd` as the
whole proof.

## 4. PREMISE 3, MEASURED AT THE VALUE

The brief's premise 3 says the covering witness is free at the stage and only
its name costs, on the basis of `[LJ-1.650]`'s `cover-in-stage`
(`agents/tasks/LJ-1-650/Probe650.agda:333-347`). **That term is about the
covering ORDINAL. The level formula's witness is the covering VALUE, and they
are not the same object.** So I measured the value.

`level-in-stage` (`Probe662.agda:268`) is nine lines and spends three
delivered facts: `ord∈Lset→∈` (`src/L/Ordinal/Stages.lagda.md:265`) puts the
ordinal in `lam`; `defSet⊤≡A` (`src/L/Definability.lagda.md:178`) makes the
stage a definable subset of itself, so `𝒟ₒ-intro`
(`src/L/Constructible.lagda.md:301`) puts `Lset γ` at the next stage; and
`Lset-mono` (`src/L/Constructible.lagda.md:365`) brings it back under `lam`.

**PREMISE 3 IS CONFIRMED AT THE VALUE, AND THE CONFIRMATION IS WORTH ITS OWN
SENTENCE**, because it is what makes the residue a single fact.
`cover-from-sat` (`Probe662.agda:289`) turns `SatAtLevel φ` into `CoverP φ`
with `refl` in the equality slot.

## 5. THE HEAP, AND THE TWO RESTRUCTURINGS IT FORCED

**A WALL WAS MET TWICE AND ROUTED AROUND BOTH TIMES.** The clause of
2026-08-23 says a wall is restructured in the same dispatch and the new shape
tested under the same cap. It was.

**WALL 1, THE TRANSPARENT FORMULA.** With `φ₀` transparent, naming it in a
downstream TYPE unfolds the chapter's whole bounded code-set description
inside the elaborator. `runs/p-3.out`: exit 251, `Heap exhausted`, at 10.57 s.
The cure is P-l (`dev/LESSONS.md:2367`): seal the formula. `opaque`
(`Probe662.agda:109`) is that seal, and the four facts inside it are the
official readings, so no consumer needs `unfolding`.

**THE SEAL WAS NECESSARY AND NOT SUFFICIENT.** Sealed, the same file reached
48.02 s before walling at 2,317,811,712 bytes (`runs/p-4.out`, exit 251).

**WALL 2, THE WHOLESALE MODULE APPLICATION, AND THIS IS THE MEASUREMENT TO
KEEP.** I split the file three ways and it still walled (`runs/p-5.out`,
`runs/b2-1.out`, both exit 251). The bisection found the cause and it is not
the mathematics.

| run | what it measures | wall s | peak RSS bytes | exit |
|---|---|---:|---:|---:|
| `runs/floor-2.out` | the frame | 3.23 | 699,842,560 | 0 |
| `runs/b7-1.out` | the frame **plus `module Bd = P657.Bridge lam ...` and NOTHING ELSE** | 5.50 | 1,293,303,808 | 0 |

**`module M = N args` ON A TELESCOPED MODULE COSTS 0.59 GB HERE, FOR NO
TERM.** It specialises every definition of the applied module at the new
telescope. Every name this file takes from `[LJ-1.657]`'s `Bridge` is
PROJECTED instead, as `P657.Bridge.<name> lam ordλ succλ X X⊆L ∅∈λ`
(`Probe662.agda:172`, `:197`, `:209-211`), which specialises nothing.

The effect is the whole difference between a file that walls and a file with
room to spare:

| shape | wall s | peak RSS bytes | exit | at |
|---|---:|---:|---:|---|
| three files, wholesale application | 29.17 | 2,074,263,552 | 0 | `runs/p-7.out` |
| three files, projections | 7.79 | 1,181,745,152 | 0 | `runs/p-12.out` |
| **ONE file, projections (delivered)** | 28.14 | 1,472,004,096 | 0 | `runs/join-2.out` |

**SO THE THREE-WAY SPLIT WAS UNDONE.** Once the module applications were
gone, the joined file fitted with 0.6 GB to spare, and one file is the better
deliverable. `runs/Pinned662.agda.txt` and `runs/Bridge662.agda.txt` are the
split copies, kept as evidence and not run.

## 6. RUNS, EVERY NUMBER

Caliber `-A64m -I0 -M2g`, set on the pane by the program and untouched here.
ONE Agda process at a time, from the repository root, warm `src/` cache. The
`LJ-1-662` interface was deleted before every forced recheck. The wall cap is
a perl alarm, because this macOS has no `timeout` (`[LJ-1.602]`,
`[LJ-1.610]`); `runs/run.sh` carries the mechanism, copied from
`agents/tasks/LJ-1-657/runs/run.sh`.

**The delivered file**, seventeen runs through `runs/run.sh`, sixteen of
them forced (the interface deleted first). The ten green forced checks:

| run | wall s | peak RSS bytes | exit |
|---|---:|---:|---:|
| `runs/p-final-4.out` | 28.90 | 1,404,993,536 | 0 |
| `runs/p-final-5.out` | 30.80 | 1,050,542,080 | 0 |
| `runs/p-final-6.out` | 27.61 | 1,734,344,704 | 0 |
| `runs/p-final-7.out` | 27.50 | 1,694,285,824 | 0 |
| `runs/p-final-8.out` | 28.01 | 1,560,379,392 | 0 |
| `runs/p-final-9.out` | 28.21 | 1,560,313,856 | 0 |
| `runs/p-final-11.out` | 31.73 | 1,535,229,952 | 0 |
| `runs/p-final-13.out` | 27.39 | 1,735,344,128 | 0 |
| `runs/p-final-15.out` | 30.73 | 1,542,111,232 | 0 |
| `runs/p-final-17.out` | 37.29 | 1,535,344,640 | 0 |

Median wall **28.56 s**, median peak RSS **1,551,212,544 bytes**, which is
**72 %** of the 2,147,483,648-byte wide cap. The highest single green peak is
1,735,344,128 bytes (`runs/p-final-13.out`), which is **81 %**.
`runs/p-final-2.out` (3.26 s) is a tenth green run and I keep it out of the
table because its interface was not deleted, so it checks nothing.

**EIGHT RUNS OF THIS FILE WERE KILLED, AND `agda-watchdog.sh` KILLED EVERY
ONE OF THEM ON THE SYSTEM FREE-MEMORY FLOOR.** The killed runs record
`EXIT=1` with no Agda diagnostic at all, and a plain `agda` run of the same
bytes returns **137**, which is `128 + SIGKILL`. The watchdog's only kill is
`kill -9` (`scripts/ops/agda-watchdog.sh:26`, `:32`). Its log names them by the
second:

    2026-08-26 19:38:22 KILLED agda pid=95925 (free 6% < 8%)
    2026-08-26 19:39:42 KILLED agda pid=97151 (free 6% < 8%)
    2026-08-26 19:43:23 KILLED agda pid=250   (free 5% < 8%)
    2026-08-26 19:54:25 KILLED agda pid=10133 (free 3% < 8%)
    2026-08-26 19:57:06 KILLED agda pid=12450 (free 3% < 8%)
    2026-08-26 19:57:46 KILLED agda pid=12945 (free 3% < 8%)
    2026-08-26 20:00:07 KILLED agda pid=14338 (free 3% < 8%)
    2026-08-26 20:08:50 KILLED agda pid=21464 (free 3% < 8%)

Each stamp is within 25 s of the start stamp of one killed run
(`runs/p-final-1.out`, `-3`, `-10`, `-12`, `-14`, `-16`, and two plain runs
outside the wrapper).

**IT IS THE FREE-PERCENTAGE LIMB AND NOT THE PER-PROCESS BACKSTOP.** The
backstop is 6 GB (`scripts/ops/agda-watchdog.sh:17`) and no run of this task
came near it. The limb that fired is `FREE_MIN=8`
(`scripts/ops/agda-watchdog.sh:21`, spent at `:32`), which kills **the largest Agda on the
box** when system free memory drops under 8 percent. That is why the sampled
peaks of the killed runs are meaningless: one died at **0.28 s and
23,691,264 bytes**, long before it had allocated anything. The kill is not
about this file's size.

**AND HERE IS THE PART THE NEXT WORKER IN A WORKTREE NEEDS.** The watchdog
resolves its own repository root from its own path
(`scripts/ops/agda-watchdog.sh:10-14`), and the live process runs from the
MAIN checkout (`ps ax`: `/bin/zsh /Users/alsg/Agentic/Bedrock/scripts/ops/agda-watchdog.sh`).
So it writes `/Users/alsg/Agentic/Bedrock/_build/tools/agda-watchdog.log`.
**The copy inside this worktree is a stale snapshot**: 3,493 bytes, last
written `18:15`, against 4,004 bytes and `20:00` in the main checkout. I read
the worktree copy first, found no kill in my window, and nearly recorded the
wrong cause. **In a worktree, read the MAIN checkout's watchdog log.**

Nothing here is a fact about the mathematics or about the file. The delivered
bytes typecheck, ten forced green checks say so, and a resource fact is
parked and not escalated (`[LJ-1.534]`).

**Everything else measured**, in order:

| run | what | wall s | peak RSS bytes | exit |
|---|---|---:|---:|---:|
| `runs/count-1.out` | `countFo` `refl` on the chapter's matrix, alone | 5.48 | 619,692,032 | 0 |
| `runs/pin-1.out` | the whole pinned block, alone | 23.44 | 882,819,072 | 0 |
| `runs/p-1.out` | Part 1 inside the probe frame | 23.82 | 1,277,788,160 | 0 |
| `runs/p-2.out` | Parts 1 and 2 | 29.38 | 1,580,236,800 | 0 |
| `runs/p-3.out` | Parts 1 to 4, formula TRANSPARENT | 10.57 | 972,424,464 (footprint) | 251 |
| `runs/p-4.out` | the same, formula SEALED | 48.02 | 2,317,811,712 | 251 |
| `runs/b1-1.out` | Parts 1 to 3 | 28.32 | 1,853,734,912 | 0 |
| `runs/pinned-1.out` | Part 1 split into its own module | 19.99 | 896,221,184 | 0 |
| `runs/p-5.out` | split three ways, Part 4 named directly | 31.50 | 2,289,893,376 | 251 |
| `runs/b2-1.out` | Part 4 cut to ONE term | 33.47 | 2,124,120,064 | 251 |
| `runs/p-6.out` | formula as a variable with its equation | 34.86 | 2,065,317,888 | 0 |
| `runs/bridge-1.out` | the bridge, wholesale module application | 11.11 | 1,701,314,560 | 0 |
| `runs/p-7.out` | three files, wholesale application | 29.17 | 2,074,263,552 | 0 |
| `runs/p-8.out` | the pin named once at the top level | 31.55 | 1,912,733,696 | 0 |
| `runs/p-9.out` | forced recheck of `p-8`'s shape | 30.28 | 2,043,232,256 | 0 |
| `runs/p-10.out` | the same | 29.74 | 2,197,766,144 | 0 |
| `runs/p-11.out` | the same | 29.63 | 2,061,467,648 | 0 |
| `runs/b3-1.out` | Part 4 with the pin REMOVED | 15.63 | 1,958,576,128 | 0 |
| `runs/b4-1.out` | both split modules imported, no term | 9.09 | 1,715,568,640 | 0 |
| `runs/b5-1.out` | the bridge imported alone | 9.62 | 1,622,228,992 | 0 |
| `runs/b6-1.out` | the pinned formula imported alone | 2.77 | 713,031,680 | 0 |
| `runs/b7-1.out` | ONE wholesale module application, no term | 5.50 | 1,293,303,808 | 0 |
| `runs/bridge-2.out` | the bridge, projections instead | 8.21 | 1,233,534,976 | 0 |
| `runs/p-12.out` | three files, projections | 7.79 | 1,181,745,152 | 0 |
| `runs/join-2.out` | the re-joined single file | 28.14 | 1,472,004,096 | 0 |
| `runs/control-654-1..3.out` | `[LJ-1.654]`'s probe, three forced rechecks, as a control | 5.68, 4.93, 4.63 | 969,359,360 to 1,003,847,680 | 0, 0, 0 |

**THE METERS:**

- `runs/meter-obligation.out`: `missing exit=42 4.32 s`, `1 UNRESOLVED of 1`,
  `probe_red=False`. The obligation is ABSENT and the probe is GREEN: that is
  what `probe_red=False` beside a `missing` row means.
- `runs/meter-names.out`: twenty-one names, `0 UNRESOLVED of 21`, 11.05 s,
  `probe_red=False`.
- `runs/meter-names-killed.out` is the SAME twenty-one names run four minutes
  earlier: `5 UNRESOLVED of 21`, `probe_red=True`, and every unresolved row
  reads `exit=-9`. The watchdog killed four Agda processes between
  `20:05:29` and `20:07:09`, all on `free 3% < 8%`. I keep the file so the
  shape of a watchdog-polluted meter is on the record: **`exit=-9` is not a
  red probe**, and a meter that spawns one Agda per obligation is the run
  most likely to trip the free-memory floor.

This worktree has no `.venv`. The meter ran as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py`.

**THE SIZE.** `Probe662.agda` is 342 lines, of which **175** are non-blank and
non-comment. The brief's W3 estimate was 80 to 170 lines for the covering
witness alone; the covering witness is not built at all, and the 175 lines are
the pinning, the transport and the split of the residue.

**THE GATES**, run individually while I worked, as the Boundary orders:
`lint-prose.py --check` and `lint-agda.py --check` are silent;
`check-probes.py --check` reports `clean (10144 tracked files, no probe
outside agents/tasks/ and no generated file)`; `check-fences.py --check`
reports `clean (103 masters, run threshold 3)`. I did NOT run `make check`:
its `typecheck` target runs the whole tree under its own caliber, and the
standing coder clause forbids me a second caliber. The Boundary makes
`make check` the gate before a commit, and I do not commit.

**W4 (DD13).** This task retires no module and adds no `dev/ARCHIVE.md` row.
Every red or superseded file under `runs/` is kept as `.agda.txt`, so nothing
is deleted and conjunct 1 does not run them.

**THE DIRECTION.** `dev/pod/direction.md` orders one `src/` collection after
LJ-1 and nothing in phase 3 before `[LJ-2.5]`. This task is LJ-1 work, starts
no collection, and lands nothing in `src/`. No Boundary clause is in conflict.

## 7. WHAT THE NEXT BRIEF NEEDS

**THE OBLIGATION IS ONE FACT AWAY AND THE FACT HAS A NAME.**
`SatAtLevel φ₀` (`Probe662.agda:284`). Everything else on the road is green:
`hoodexists-at-levelhood0-from-sat` (`Probe662.agda:331`) takes it and
`ElemDown` and returns the brief's own conclusion.

**DO NOT PIN AT `LevelHood0`.** Section 3 of `review-of-hoodexists.md` counts
it: twelve numeral columns cannot come from five committed slots, so no choice
of that module's twenty-eight parameters can carry the `KFacts` the leaf
agreement needs. The next brief must choose which side of the tension to pay:

- **arity 2 and parameter-free**, which `HoodExistsP` demands
  (`agents/tasks/LJ-1-653/Probe653.agda:283`); or
- **fourteen pinned environment columns**, which the only `KFacts` value in
  the tree supplies (`src/L/Condensation.lagda.md:7389`, `:7411`).

`LevelHood {n}` for `n ≥ 14` has room for the columns and then has arity
`4 + n`. Closing the surplus by `∃̇` returns to arity 2 and loses the tag
equations. **A formula that SAYS its own columns are the numerals is the third
option and nobody has priced it.** The numerals are parameter-free definable,
so it is not obviously out of reach.

**THE BOUNDED GRAPH HAS NO TIE TO THE UNBOUNDED ONE ANYWHERE IN `src/`.**
`graphBndAt` occurs at six lines total (`src/L/Condensation.lagda.md:2492`,
`:2493`, `:2495`, `:2496`; `src/L/BoundedSubset.lagda.md:111`, `:115`). The
delivered adequacy is `Lset-only` and `Lset-defines`
(`src/L/Hierarchy.lagda.md:334`, `:646`), for the UNBOUNDED graph at the CLASS
carrier. Any route to `SatAtLevel` crosses that gap, and the gap is the
chapter's own named residue (`src/L/BoundedSubset.lagda.md:901-902`).

**TAKE `level-in-stage`, DO NOT REPROVE IT** (`Probe662.agda:268`). Nine
lines, and it is what makes the residue a single fact rather than two.

**TAKE THE PROJECTION LESSON TO EVERY PROBE IN THIS CHAIN.** `runs/b7-1.out`
prices `module M = N args` on a telescoped module at 0.59 GB with no term
written. `[LJ-1.657]` opens five such modules
(`agents/tasks/LJ-1-657/Probe657.agda:51-63`) and `[LJ-1.654]` one
(`agents/tasks/LJ-1-654/Probe654.agda:364`). I did not re-measure them at
their own sites and I do not claim the number transfers: a measured cure does
not transfer by analogy. **I claim only that it is cheap to check and that
this task could not have closed without it.**

## ARCHIVE USED

- **`archive/dev/TASKS-archived.md`: READ.** At
  `archive/dev/TASKS-archived.md:119`:
  `| L3.32-T84 | Lever B: condensation story onto the kit | STOP (D-10) | `_build/l3.32-t84-report.md` |`
  This is the earliest recorded STOP under D-10 on the condensation story,
  and it is the same law this task's section 5 of the review answers: price
  the target's truth before pricing its proof. The row records that the
  condensation story has stopped a task before at the point where it is
  fitted onto a concrete kit, which is exactly where `LevelHood0` sits.
- **`archive/dev/ORCHESTRATION.md`: NOT USED, declined.** Surveyed by grep,
  not read: zero hits for `LevelHood`, `levelHood`, `KFacts` and `graphBnd`,
  and one hit for `level` that is not the level hierarchy. It is the archived
  operating document and it binds no rule today.
- **`archive/dev/DD-archived.md`: NOT USED, declined.** Surveyed by grep:
  zero hits for `LevelHood`, `KFacts` and `graphBnd`. The `DD` series is set
  aside in this form by amendment A7, and this task cites no `DD` row.
- **`archive/dev/PLAN-archived.md`: NOT USED, declined.** Surveyed by grep:
  zero hits for `LevelHood`, `KFacts`, `graphBnd` and `condens`. It carries
  no mathematics about the level hierarchy.
- **`archive/dev/STATUS-archived.md`: NOT USED, declined.** Surveyed by grep:
  zero hits for `LevelHood`, `KFacts` and `graphBnd`. It is a status record
  and this task's standing status is `dev/pod/screen.toml`.

## LITERATURE USED

- **`dev/literature/level-formula-slot-roles.md`: READ, AND IT IS THE FILE
  THAT SETTLES THE SHAPE.** At `dev/literature/level-formula-slot-roles.md:31`:
  `| 9 | Schindler-Zeman 1.10(2) | "`x = S_γ^A` is Σ₁ over `J_α^A` as witnessed by a formula which does not depend on `α`" | 2 | not exhibited | `x`, `γ` | **VALUE, ORDINAL** | `_build/literature/sz-full.txt:322-323` |`
  Nine rows agree that the free pair is the VALUE and the ORDINAL and that
  nothing else stays free. That is why `hood2` (`Probe662.agda:110`) closes
  the bound and the unused slot rather than leaving them free, and it is the
  source `[LJ-1.657]` cited for the same reading. I also read
  `dev/literature/level-formula-slot-roles.md:40`:
  `### 2.2 ONE bound binds ALL the unbounded quantifiers`
  That section is the literature's own statement of the K bound, which is the
  slot the counting fact of section 3 of the review is about.
- **`dev/literature/devlin-errata.md`: READ.** At
  `dev/literature/devlin-errata.md:98`:
  `- Bounding quantifiers (10.6, p. 60): the proposed bounding class for the`
  The errata records that Devlin's own proposed bounding class for the
  quantifier is defective twice over, "not provably a set" and "the wrong
  type". This is a documented warning against taking the bound's adequacy for
  granted, and it is the reason I did not assume `SatAtLevel` was cheap
  before measuring what supports it.
- **`dev/literature/BIBLIOGRAPHY.md`: NOT USED, declined.** Its title line
  says it is the bibliography for the rud route. This task touches no rud
  function and cites no new source.
- **`dev/literature/primary-sources.md`: NOT USED, declined.** It is the
  second fetch round of developer notes for the rud-route formalization.
  Nothing in this task rests on a source that needed fetching.
- **`dev/literature/glossary-review-2026-08.md`: NOT USED, declined.** It
  reviews the 119 pre-protocol glossary entries. This task adds no term and
  writes no `dev/glossary.toml` entry.
