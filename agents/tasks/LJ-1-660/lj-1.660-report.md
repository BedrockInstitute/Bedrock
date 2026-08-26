# LJ-1.660 report: can the built reflection delete step 2's ordinal slot

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.660
obligation: agents/tasks/LJ-1-660/Probe660.agda::step2-unconditioned
verdict: **NO-GO ON THE OBLIGATION, STATED, AND A GO ON THE QUESTION W3
ASKS.** The obligation is not inhabited and the statement of that stop
is `agents/tasks/LJ-1-660/review-of-step2-unconditioned.md`. The meter
records it: `runs/meter-obligation.out:2`,
`1 UNRESOLVED of 1, 7.12 s, probe_red=False`. Both delivered files are
GREEN and carry no hole (`runs/p-15.out` and `runs/c-5.out`, `EXIT=0`),
and eighteen other names are metered green
(`runs/meter-names.out`, `0 UNRESOLVED of 15`; `runs/meter-chain.out`,
`0 UNRESOLVED of 3`).

**READ THESE FIVE SENTENCES BEFORE YOU QUEUE ANYTHING.**

1. **`PiReflectsOrd` CANNOT DELETE THE `IsOrd` SLOT. IT MOVES IT.** The
   collapse reflects AND preserves ordinality at a hull member, both
   built by `[LJ-1.654]`, so `IsOrd y` and `IsOrd (C.π y)` are
   interderivable there. `AtSite.the-two-holes-are-one`
   (`Probe660.agda:135-136`) is that equivalence, green.
2. **THE OBLIGATION'S CONCLUSION IS `[LJ-1.646]`'s UN-ORDINAL KEYSTONE,
   NOT A COROLLARY OF IT.** `AtSite.the-obligation-is-the-unordinal-keystone`
   (`Probe660.agda:164-167`) gives both directions. So the brief asked
   for `[LJ-1.646]`'s un-ordinal variant under another name.
3. **THE MISSING FACT IS FALSE AT THE THEOREM'S OWN TELESCOPE.** It
   forces `IsOrd x` on the ARBITRARY bounded subset the chapter is about
   (`Probe660.agda:268-269`), and it makes `Lset α` an ordinal
   (`:288-291`). Both are green derivations, not arguments.
4. **W3 IS ANSWERED YES, AT ALL FOUR SITES, AND THE BRIEF'S NO-GO CLAUSE
   DOES NOT FIRE.** `IsOrd (C.π y)` is available where step 2 is
   CONSUMED. No site fails. **The un-ordinal keystone stays PREFERABLE
   and does NOT become MANDATORY.**
5. **`levelIn` NOW STANDS ON TWO OBJECTS, AND ONE OF THEM IS A FORMULA.**
   `Chain660.agda`'s `levelin-from-keystone-and-hood` takes
   `[LJ-1.646]`'s keystone and ONE level-hood formula's soundness and
   completeness. Nothing else. That is `[LJ-1.647]`, `[LJ-1.649]`,
   `[LJ-1.653]` and `[LJ-1.654]` composed, which no file had done.

Written as a skeleton before any Agda beyond the floor and filled as
each answer landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-660/`. Agda ran under the caliber the program set on
this pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier, ONE Agda process at
a time. I did not set `GHCRTS`. Nothing is postulated, both probes carry
`--safe`, neither delivered file carries a hole, and nothing lands in
`src/`. Both probes are raw `.agda` files, so they carry no ` ```agda `
fence, count 0 in-fence lines, and the ratio bar cannot fire on them.

**NO HEAP WALL WAS MET.** The highest peak of any run is 1,826,635,776
bytes against the 2,147,483,648-byte wide cap, which is 85 %, and that
run is `runs/p-11.out`, a shape I REJECTED for that reason and split
into two files (section 7). The delivered shapes peak at 56 % and 48 %.
The longest Agda run is 10.15 s against the 900 s cap I set on every
run. The cap is a wall-clock cap enforced by a perl alarm
(`runs/run.sh` carries the mechanism), because this macOS has no
`timeout` (`[LJ-1.602]`, `[LJ-1.610]`).

**EVERY NUMBER BELOW IS MEASURED WITH A WARM `src/` INTERFACE CACHE**
(708 `.agdai` files under `_build/` at the start of the task). No number
here is a cold-cache number, and this report does not bound one.

**AND ONE WARNING ABOUT THE PEAK NUMBERS.** On this shared machine the
peak RSS is NOT stable across runs of identical bytes. `Probe660.agda`
read between 950,616,064 and 1,572,880,384 bytes over nine green runs of
two shapes that differ by a comment block. The wall clock IS stable
(within 0.3 s). So section 8 reports wall deltas as measurements and
peak deltas as bounds, and never the other way round.

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

The brief names four predecessors and I opened the report and the probe
of each.

| task | verdict | what I took |
|---|---|---|
| `[LJ-1.647]` | GO (`lj-1.647-report.md:9`) | `hull-closed-lset`, `hull-closed-op∥`, `hull-mem-is-code`, `LsetCodeOrd`, `LsetCodeOrd∥` |
| `[LJ-1.649]` | GO (`lj-1.649-report.md:9`) | `HullClosedLset`, `HullClosedLsetOrd`, `PiCommuteLsetOrd`, `levelin-from-647-ord-commute` |
| `[LJ-1.653]` | GO (`lj-1.653-report.md:3`) | `step4-at-ord-pf`, `HoodCompleteP`, `HoodSoundP` |
| `[LJ-1.654]` | GO (`lj-1.654-report.md:9`) | `PiReflectsOrd`, `PiPreservesOrd`, `pi-ord-iso`, `fifth` |

**NO REPORT NAMES ANY STATEMENT FALSE, so the standing coder clause does
not order a stop on a predecessor's account.** The stop in this task is
about the BRIEF's obligation and is measured here.

**I COPIED NO TYPE. I IMPORTED EVERY ONE.** `Probe660.agda:67-89` and
`Chain660.agda:60-74` apply the four probe modules to one telescope, so
the typechecker answers the clause instead of my reading of it.

**AND THE BRIEF'S PREMISE 4 IS HONOURED.** It says `[LJ-1.653]`'s note 3
is stale about `PiReflectsOrd`. I took `[LJ-1.653]`'s step 4 REDUCTION
only, which is independent of that note, and I say so in the file
(`Chain660.agda:23-26`). I did not take its note 3 as current.

The standing direction (`dev/pod/direction.md:37`) orders one `src/`
collection after LJ-1, not after `[LJ-2.5]`. This task is LJ-1 work. It
does not start that collection and it does not start phase 3. No
Boundary clause is in conflict.

## 2. THE FLOOR, MEASURED BEFORE ANY PROOF

The standing coder clause orders a floor before a heavy object and the
imports trimmed to the facts my own rows use. I ran it.
`runs/FLOOR.agda.txt` is the frame, the obligation stated, and a HOLE
where the term goes.

**THE FRAME COSTS 0.76 GiB AND 3.93 s.** Three runs, the `LJ-1-660`
interfaces deleted before each: 7.09 s, 3.70 s, 3.93 s. Median wall
**3.93 s**, median peak **814,252,032 bytes**. Exit 42 every time with
ONE error and it is the hole (`runs/floor-1.out:8-10`,
`[UnsolvedInteractionMetas]` at `52.25-30`). `runs/floor-1.out` is the
first run and it compiled the three predecessor probes in the same
process, which is why it is 3.2 s slower than the other two.

**THE IMPORT TRIM, AND ONE ADDITION THAT PAID FOR ITSELF.** I started
from `[LJ-1.654]`'s import set and dropped `FOL.Syntax`,
`FOL.Manipulation.Relabelling`, `Cubical.Data.Sum` and
`isPropIsTransV`, because no row of mine names a formula. I ADDED
`module HullStage` and `module UnionKit` from `L.BoundedSubset`, and
section 3 says what they bought.

**THE FRAME IS NOT THE PROBLEM HERE.** The floor is 38 % of the wide
cap and the delivered probe is 56 %. This object is not heavy and the
floor proved it before any proof was attempted.

## 3. THE FRAME IS THE CONSUMER'S OWN MODULE, NOT A COPY OF IT

**FOUR PROBES HAD COPIED `src/L/BoundedSubset.lagda.md:903-914` AND THIS
ONE STOPS THE COPYING.** `[LJ-1.462]` (`Probe462.agda:78-88`),
`[LJ-1.647]` (`Probe647.agda:69-72`), `[LJ-1.649]`
(`Probe649.agda:61-64`) and `[LJ-1.654]` (`Probe654.agda:81-84`) each
restate the telescope. This task applies the ORIGINAL
(`Probe660.agda:86`, `module Site = HullStage lam ordλ succλ X X⊆L ∅∈λ`)
and then applies the three probe modules to the SAME arguments.

`AtSite.carriers-agree` (`Probe660.agda:93-94`) is `refl`, so the four
carriers are definitionally one and the four copies are proved faithful
rather than assumed so. **THE COST OF STOPPING THE COPYING IS ZERO**:
the floor with the real module applied is 3.93 s, and `module Condense`
inside it does not elaborate at application.

## 4. W3, ANSWERED YES, AND THE FOUR SITES NAMED

W3 asks "whether `PiReflectsOrd`'s hypothesis `IsOrd (C.π y)` is
available where step 2 is CONSUMED".

**IT IS, AND THE ANSWER IS ONE SLOT OF A TERM `[LJ-1.649]` ALREADY
WROTE.** `pix-closed-op` (`Probe649.agda:124-139`) carries a `reflect`
parameter, `(y : S) → ⟨ y ∈ˢ M ⟩ → Q (C.π y) → P y`, and it supplies
`Q (C.π y)` at `Probe649.agda:139` by `subst Q (sym e) qδ`, where `e` is
step 1's `C.π y ≡ δ` and `qδ` is the consumer's own hypothesis. At
`P = Q = IsOrd` that slot is exactly `PiReflectsOrd` and the consumer's
`IsOrd δ` is exactly `qδ`. Nothing else is spent.

**THE FOUR SITES, RE-COUNTED FROM `src/`, AND `[LJ-1.649]`'s COUNT AND
`[LJ-1.654]`'s CONFIRMATION BOTH HOLD.** All four declare `levelIn` with
the same type:

| # | site | binder line |
|---|---|---|
| a | `HullStage.Condense` | `src/L/BoundedSubset.lagda.md:917` |
| b | `Devlin55.BoundedSubsetAt....Co` | `src/L/BoundedSubset.lagda.md:1671` |
| c | `StageBound.Instantiation.Co` | `src/L/StageBound.lagda.md:80` |
| d | `StageBound`'s anonymous `module _` | `src/L/StageBound.lagda.md:106` |

**AND THE SWEEP FOUND ONE THING WORTH RECORDING: SITES (b), (c) AND (d)
ARE THE SAME `HullStage` INSTANCE.** `src/L/BoundedSubset.lagda.md:1521`
and `src/L/StageBound.lagda.md:103` both set
`HS = HullStage lam ordλ succλ UK.X UK.X⊆Lλ UK.∅∈λ`, at `UnionKit`'s
`X`. Site (a) is the general telescope. So two terms cover all four:

- `AtSite.levelin-from-keystone` (`Probe660.agda:190-194`) at the
  general telescope, which is site (a);
- `AtTheorem.levelin-at-the-three-sites` (`Probe660.agda:281-285`) at
  `UnionKit`'s `X`, which is sites (b), (c) and (d).

**AND SITE (a) IS CHECKED BY AGDA AND NOT BY THIS REPORT.**
`AtSite.FeedTheSite` (`Probe660.agda:233-239`) applies the REAL
`Site.Condense` to `levelin-from-keystone`, so the chapter's own module
accepts the term in its `levelIn` slot. `cover` stays a hypothesis
because it is unbuilt: `[LJ-1.654]` section 5 built only its `IsOrd γ`
conjunct.

## 5. WHY THE OBLIGATION AS STATED IS A STOP

The full statement is `review-of-step2-unconditioned.md`. The four
measurements in one table:

| measurement | where | what it shows |
|---|---|---|
| three readings, three holes | `runs/holes-1.out:5-9` | every reading of the brief leaves EXACTLY ONE hole and no other error |
| the two holes are one | `Probe660.agda:135-136`, green | `PiReflectsOrd` moves the debt across the collapse and cannot close it |
| the conclusion is the keystone | `Probe660.agda:164-167`, green | the obligation IS `[LJ-1.646]` in the un-ordinal form |
| the gap fact is false | `Probe660.agda:268-269` and `:288-291`, green | it forces `IsOrd x` on the chapter's arbitrary subset, and makes `Lset α` an ordinal |

**I DID NOT BUILD A CLOSED `⊥`.** That needs a concrete non-transitive
member of a concrete stage and this task did not price it. The evidence
is a derivation to two statements the chapter does not have and cannot
want. That is enough to stop and I say plainly that it is not a
refutation in the strict sense.

**WHY NO TERM OF THAT NAME WAS WRITTEN AT ANOTHER TYPE.** A
`step2-unconditioned` at any type the tree supports would meter as
RESOLVED and the branch table's `go` row keys on
`obligations_delta_max = -1`. That is a GO the measurement does not
support. The name is left unwritten so the return routes to
`stop-stated`.

## 6. W2 (DD4)

**THIS TASK WROTE NO NEW MATHEMATICS AND THAT IS THE W2 ANSWER.** Every
mathematical step in both files is imported:

- `A647.hull-closed-op∥` (`Probe647.agda:135-149`), generic in the
  operation `F` and the side condition `P`;
- `A649.pix-closed-op` (`Probe649.agda:124-139`), generic in `F`, `P`
  and `Q`;
- `A654.PiReflectsOrd` and `A654.PiPreservesOrd`
  (`Probe654.agda:295-297` and `:337-349`);
- `A653.step4-at-ord-pf`, generic in the level-hood formula `φ₀`.

**NOT ONE OF THEM IS RESTATED HERE.** The longest body in either
delivered file is three lines. The clause's conflict did not arise: no
deadline pushed me toward a fixed form, because there was no form to
choose.

**AND THE W2 FINDING WORTH A RULING IS ABOUT THE TELESCOPE, NOT THE
MATHEMATICS.** Four probes copied `src/L/BoundedSubset.lagda.md:903-914`
by hand. Copying it is unnecessary, it costs nothing to stop, and
`carriers-agree` (`Probe660.agda:93-94`) shows the check is a `refl`.
**A probe at a `src/` consumer should apply that consumer's module
rather than restate its telescope.** I do not propose this as a rule; I
report the measurement and the owner rules.

## 7. THE HEAP SIGNAL, AND THE RESTRUCTURING IT ORDERED

I met no wall. **I met 85 % of the cap and I restructured before I
reported anything**, which the standing coder clause orders.

`runs/p-11.out` is `Probe660.agda` with `[LJ-1.653]` imported and the
chain folded in: green, 9.10 s, **1,826,635,776 bytes, 85 % of the wide
cap**, on a machine the pod shares. Acceptance runs ONE Agda process per
target (`scripts/pod/accept.py:165-167`), so the cure is a second file
and not a smaller proof.

`Chain660.agda` is that file. It carries the 653 chain and the leanest
frame that reaches it. **The split changes no mathematics and it holds
the peak down**: `Probe660.agda` runs at 1,201,635,328 bytes (56 %) and
`Chain660.agda` at 1,025,359,872 (48 %), against 1,826,635,776 (85 %)
for the one-file shape.

**AND ONE HARNESS FAILURE HAPPENED AND I RECORD IT RATHER THAN HIDING
IT.** `runs/p-10.out` exited 1 at 10.15 s with `time: command
terminated abnormally` and `time: signal: Invalid argument`, part way
through checking `LJ-1-653.Probe653`. **IT IS NOT AN AGDA RESULT.**
`[LJ-1.647]` recorded the same artifact in its own `runs/p-3.out` and
warned that it should be re-run before it is believed. I did that:
`runs/p653-alone.out` checks `Probe653.agda` by itself, green at
2.88 s, and `runs/p-11.out` is the same bytes as `p-10` and green. This
machine is `shared` and other Agda processes were live during the task,
which is the likeliest cause and which I did not prove.

## 8. RUNS, EVERY NUMBER

Caliber `-A64m -I0 -M2g`, set on the pane by the program and untouched
here. ONE Agda process at a time, from the repository root, warm `src/`
cache. The `LJ-1-660` interfaces were deleted before every forced
recheck. Cap 900 s on every run.

**The floor**, `runs/FLOOR.agda.txt`, red by design (one hole):

| run | wall s | peak RSS bytes | exit |
|---|---|---|---|
| `runs/floor-1.out` | 7.09 | 858,767,360 | 42 |
| `runs/floor-2.out` | 3.70 | 814,219,264 | 42 |
| `runs/floor-3.out` | 3.93 | 814,252,032 | 42 |

Median wall **3.93 s**, median peak **814,252,032 bytes**.

**The delivered `Probe660.agda`**, the run of the delivered bytes plus
three forced rechecks:

| run | wall s | peak RSS bytes | exit |
|---|---|---|---|
| `runs/p-12.out` | 7.04 | 1,201,618,944 | 0 |
| `runs/p-13.out` | 9.32 | 950,616,064 | 0 |
| `runs/p-14.out` | 6.96 | 1,201,635,328 | 0 |
| `runs/p-15.out` | 6.73 | 1,201,651,712 | 0 |

Median wall **7.00 s**, median peak **1,201,627,136 bytes**.
`runs/p-13.out` is the low peak and the slow wall together, which is the
contention pattern the warning in the head describes. I report it and I
do not use it.

**The delivered `Chain660.agda`**, three forced rechecks:

| run | wall s | peak RSS bytes | exit |
|---|---|---|---|
| `runs/c-3.out` | 5.58 | 1,025,327,104 | 0 |
| `runs/c-4.out` | 5.59 | 1,025,359,872 | 0 |
| `runs/c-5.out` | 5.66 | 1,025,359,872 | 0 |

Median wall **5.59 s**, median peak **1,025,359,872 bytes**. This file
is the STABLE one: three runs within 0.08 s and 32,768 bytes.

**The earlier probe runs.** `runs/p-1.out` (3.30 s, 681,869,312, exit 42)
is the ONE failed attempt of this task and its error is `[NotInScope]`
on `A647.Code`: `[LJ-1.647]` opens `Code` and `val` from `H.T` without
`public`, so the names are not re-exported and the qualified path is
`A647.H.T.Code`. `runs/p-2.out` (7.67 s, 1,161,969,664, exit 0) is the
first green run. `p-3` to `p-9` are the intermediate shapes, `p-10` is
the harness failure of section 7 and `p-11` is the rejected one-file
shape. `runs/c-1.out` (3.24 s, exit 42) is `Chain660.agda`'s one failed
attempt, three missing Cubical imports, and `runs/c-2.out` (8.19 s,
854,360,064, exit 0) is its first green run.

**The closing check on the delivered bytes**, both green with warm
interfaces: `runs/final-Probe660.out` (3.05 s, 760,692,736, exit 0) and
`runs/final-Chain660.out` (3.21 s, 758,611,968, exit 0). These two are
NOT comparable with the forced rechecks above: they reuse the
`LJ-1-660` interfaces instead of rebuilding them, so they measure the
acceptance run's shape and not the term's price.

**The three slices**, all `.agda.txt`, each with its own reproduction
recipe at its head:

| slice | exit | run | what it prices |
|---|---|---|---|
| `runs/HOLES.agda.txt` | 42 | `runs/holes-1.out`, 4.12 s, 882,622,464 | THREE holes, one per reading of the obligation, and no other error |
| `runs/NO-FEED.agda.txt` | 0 | `runs/no-feed-1.out`, 6.93 s, 1,485,783,040 | what the check against the real consumer costs |
| `runs/NO-THEOREM.agda.txt` | 0 | `runs/no-theorem-1.out`, 4.89 s, 909,082,624 | what the `UnionKit` application costs |

**THE TWO SLICE DELTAS, AS WALL MEASUREMENTS AND PEAK BOUNDS.**

- `module FeedTheSite`, the check at the real `src/` consumer, costs
  **0.46 s**: `no-feed-1` at 6.93 s against its contemporaneous baseline
  `runs/p-3.out` at 7.39 s. **The peak delta, 10,518,528 bytes, is
  inside the run-to-run spread and I do not claim it.**
- `module AtTheorem` and the `UnionKit` application cost **2.11 s**:
  `no-theorem-1` at 4.89 s against the delivered median of 7.00 s. The
  peak delta is 292,552,704 bytes and it too is inside the spread, so it
  is a bound and not a measurement. **`UnionKit` is the expensive part
  of this frame, not the four probe imports**, which is why
  `Chain660.agda` imports one probe MORE than `Probe660.agda` and costs
  LESS.

**The meters**, all against the delivered bytes:

- `runs/meter-obligation.out`: `1 UNRESOLVED of 1`, 7.12 s,
  `probe_red=False`. The obligation `step2-unconditioned` is `missing`
  with `[NotInScope]`.
- `runs/meter-names.out`: fifteen names of `Probe660.agda`,
  `0 UNRESOLVED of 15`, 5.71 s, `probe_red=False`.
- `runs/meter-chain.out`: three names of `Chain660.agda`,
  `0 UNRESOLVED of 3`, 5.38 s, `probe_red=False`.
- This worktree has no `.venv`. The meter ran as
  `/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py`.
  I did not add a dependency and I did not create a local `.venv`.

**The individual gates**, run while I worked, as the Boundary orders:
`lint-prose.py --check` (exit 0), `lint-agda.py --check` (exit 0),
`check-probes.py --check` (`clean, 10054 tracked files`) and
`check-fences.py --check` (`clean, 103 masters`). I did NOT run
`make check`: its `typecheck` target runs the whole tree under its own
caliber, and the standing coder clause forbids me a second caliber. The
Boundary makes `make check` the gate before a commit, and I do not
commit.

**AGAINST THE BRIEF'S ESTIMATE.** The brief priced W3 at "50 to 110
lines", basis `[LJ-1.654]`'s 3.28 s probe in the same frame. The
delivered files are 129 and 78 non-blank non-comment lines, 207
together, over 465 total lines. **The composition W3 actually asked for
is about 35 of those**; the rest is the measurement of the stop
(sections 1 and 5) and the second file's own frame. The brief's basis
sentence is right that the frame is `[LJ-1.654]`'s: this file adds only
`module HullStage` and `module UnionKit` to it.

## 9. WHAT THE NEXT BRIEF NEEDS

**`[LJ-1.646]` IS STILL A PREFERENCE AND NOT A GATE, AND THIS TASK DOES
NOT CHANGE THAT.** `[LJ-1.654]` ruled it preferable rather than
mandatory and the brief's NO-GO clause would have reversed that. It does
not fire: every one of the four sites supplies `IsOrd (C.π y)`. **Do not
re-price `[LJ-1.646]` upward on this return.**

**BUT `[LJ-1.646]` MUST STILL BE BUILT IN ONE FORM OR THE OTHER, AND THE
ORDINAL FORM IS THE ORTHODOX ONE.** Every source in
`dev/literature/level-formula-slot-roles.md`'s table states level-hood
with the ORDINAL as a free slot in the role ORDINAL. No source writes
`v = L_x` for an arbitrary set `x`. So the ordinal-conditioned keystone
`lset-code-ord` is the shape the literature supports and the un-ordinal
`lset-code` has no textbook counterpart. **A brief that prices the two
should know that before it chooses.**

**`levelIn` NOW REDUCES TO TWO OBJECTS AND ONE OF THEM IS A FORMULA.**
`Chain660.agda`'s `levelin-from-keystone-and-hood` is green and takes:

- `A647.LsetCodeOrd`, which is `[LJ-1.646]`;
- `A653.HoodCompleteP φ₀` and `A653.HoodSoundP φ₀`, at ONE level-hood
  formula, which is `[LJ-1.653]`'s residue.

**NOTHING ELSE.** Step 2, step 4 and the fifth fact are all discharged
inside that term.

**AND `[LJ-1.653]` OFFERS A ROUTE THAT SKIPS THE KEYSTONE ALTOGETHER, AND
I DID NOT PRICE IT.** `levelin-from-hood-status`
(`agents/tasks/LJ-1-653/Probe653.agda:319-328` at the top level) takes
`HoodExistsP φ₀` and `HoodSoundP φ₀` and returns `LevelIn`, with neither
step 2 nor step 4 nor the keystone in the chain. **If `HoodExistsP` is
reachable, `[LJ-1.646]` may not be on the critical path at all.** That
is the widest unmeasured term I can see from here and I make no claim
about it: the mathematician names the probe.

**TAKE THE FRAME, DO NOT COPY THE TELESCOPE.** `Probe660.agda:86` and
`Chain660.agda:70` apply `src/L/BoundedSubset.lagda.md:903` itself. Any
probe at this consumer should do the same. It costs nothing and it makes
`carriers-agree` a `refl`.

**AND ONE WARNING ABOUT `UnionKit`.** Applying it costs 2.11 s and up to
0.29 GiB of frame (section 8). A probe that only needs the general
telescope should not apply it. A probe that needs the theorem's own
`x` must, and should budget for it.

**WHAT THIS TASK DOES NOT SETTLE.** It does not build `[LJ-1.646]` in
either form. It does not touch `cover`, whose `γ ∈ˢ C.πX` and
`C.π y ∈ˢ Lset γ` conjuncts are still unmeasured (`[LJ-1.654]` section
5). It does not price `HoodExistsP`, `HoodSoundP` or `HoodCompleteP`. It
does not refute `HullClosedLset` outright, only the route to it and the
fact that would close it. It does not edit `src/`.

## W4 (DD13)

Nothing was retired. No module moved to `archive/`. No dead fragment was
deleted. `dev/ARCHIVE.md` gains no row from this task.

## SCOPE

I wrote only these paths, all inside the brief's SCOPE (write):

- `agents/tasks/LJ-1-660/Probe660.agda`
- `agents/tasks/LJ-1-660/lj-1.660-report.md`
- `agents/tasks/LJ-1-660/review-of-step2-unconditioned.md`
- `agents/tasks/LJ-1-660/runs/` (`run.sh`, `FLOOR.agda.txt`,
  `HOLES.agda.txt`, `NO-FEED.agda.txt`, `NO-THEOREM.agda.txt`, and
  32 `.out` records)

**ONE PATH IS OUTSIDE THE BRIEF'S WRITE LIST AND I NAME IT RATHER THAN
HIDE IT: `agents/tasks/LJ-1-660/Chain660.agda`.** The brief's scope
names `Probe660.agda` and not a second `.agda` file. I wrote it because
the standing coder clause orders a restructuring in the same dispatch
when the caliber is the constraint, and 85 % of the cap in one file
(section 7) is that constraint. It is inside the task home, acceptance
conjunct 1 runs it, and it is green. **If the program commits by
explicit path, this path must be added or the file is left
uncommitted.**

Nothing under `src/` was touched. No commit, no push. The temporary
`.agda` copies used to run the four slices were deleted, so no red
`.agda` remains under this task home.

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md`: READ, AND IT NAMED THIS TASK'S
  SHAPE HUNDREDS OF DISPATCHES EARLY.** At
  `archive/dev/LJ-dispatch-index.md:254`:

  > | LJ-1.178 | Build levelIn and cover | BUILT, THEOREM DOES NOT DERIVE | Two of three facts discharged and the debt moves to the STAGE. New wall: Devlin's (a) at the AMBIENT carrier |

  "the debt moves to the STAGE" is exactly this task's finding at a
  different site: a fact that discharges a hypothesis does not always
  delete it. I also read `archive/dev/LJ-dispatch-index.md:236`:

  > | LJ-1.160 | Read the 845-line level substrate against levelIn and cover | THE WALL IS BYPASSED, 16 LINES | Both hypotheses from one crossing face at the collapse image. The wall term is absent |

  which is the earliest record that `levelIn` and `cover` travel
  together, and it is why section 4 keeps `cover` as a hypothesis of
  `FeedTheSite` rather than quietly dropping it.

- **`archive/dev/JOURNAL.md`: READ, and it settled a question about
  section 3.** At `archive/dev/JOURNAL.md:329`:

  > 0.0039. `hull-closed` gives the criterion at HULL parameters, which is what

  `hull-closed` at hull parameters is the rule `[LJ-1.654]` spends
  through `lift-to-hull` and the rule `[LJ-1.647]` showed is NOT needed
  when a code is in hand. This task needs neither: it moves no witness
  into the hull and it names no formula. Recorded so the next reader
  does not look for one.

- **`archive/dev/JOURNAL-archived.md`: READ, and it is a warning I
  acted on.** At `archive/dev/JOURNAL-archived.md:1525`:

  > ordinal-conditioned kit that replaces it, 26 lines, is a hidden term the recon never priced.

  An ordinal-conditioned replacement whose cost was never priced is the
  same failure mode as an ordinal-conditioned keystone whose consumer
  cost is asserted rather than measured. Section 4 prices this one at
  the four sites instead of asserting it.

- **`archive/dev/DECISIONS-archived.md`: READ, for W2.** At
  `archive/dev/DECISIONS-archived.md:48`:

  > | D29 | Generic writing is a first-class discipline, considered at three named moments |

  D29's second moment binds a BUILD brief to say whether the content is
  generic and why. Section 6 answers it: this task wrote no new
  mathematics at all, and every step it spends was already generic in
  its own file.

- **`dev/ARCHIVE.md`: OPENED AND DECLINED.** At `dev/ARCHIVE.md:3`:

  > The registry of Bedrock's retired modules. One entry per module, written at

  This task retired no module and archived nothing, so the registry has
  nothing to give it and gains no row from it. See W4 above.

## LITERATURE USED

- **`dev/literature/level-formula-slot-roles.md`: READ, AND IT IS THE
  LITERATURE FINDING OF THIS TASK.** At
  `dev/literature/level-formula-slot-roles.md:26`:

  > | 4 | Devlin 5.2 (a) | `Φ(z,v,γ)` with `∀v∀γ [v = L_γ ↔ ∃z Φ(z,v,γ)]` | 3 in `Φ`, ONE closed | `z` at position 0 | `v` at 1, `γ` at 2 | **VALUE, ORDINAL** | `_build/literature/dev2.txt:1186-1191` |

  Every row of that table gives the free slots the roles VALUE and
  ORDINAL. **No source states level-hood at an arbitrary set.** So the
  un-ordinal keystone that the brief's obligation is equivalent to is
  not the orthodox statement, and the ordinal conditioning `[LJ-1.647]`
  added is not an accident of that task. Section 9 acts on this.

- **`dev/literature/devlin-II5.md`: READ, AND IT EXPLAINS WHY THE ROUTE
  IS CIRCULAR.** At `dev/literature/devlin-II5.md:201`:

  > π : ⟨X, ∈⟩ ≅ ⟨M, ∈⟩, and the transitive-fixing clause π ↾ Y = id ↾ Y for

  The collapse is an ISOMORPHISM and not merely a surjection. An
  isomorphism transports a structural property in BOTH directions, so a
  reflection lemma cannot be a source of that property. That is the
  informal content of `the-two-holes-are-one`, and the file is where I
  checked it before I built the term.

- **`dev/literature/truncation-and-selection.md`: READ, AND IT LICENSES
  ONE STEP OF SECTION 3.** At
  `dev/literature/truncation-and-selection.md:92`:

  > HoTT Book Lemma 3.9.1: if `P` is a mere proposition then `P ≃ ∥P∥`.

  `unconditioned→keystone` returns a truncated Σ and
  `keystone→unconditioned` eliminates one into `⟨ Lset y ∈ˢ M ⟩`, which
  is a mere proposition, so `PT.rec` applies with no choice principle.
  This is why the equivalence in section 3 costs nothing and why the
  keystone may be truncated.

- **`dev/literature/digest.md`: NOT USED, declined.** At
  `dev/literature/digest.md:1`:

  > # Digest: the orthodox form of the rud route, pinned from the collected literature

  It pins the rud route and its J-side Skolem hull. This task is
  entirely inside the Def-side hull as `src/L/Hull.lagda.md` builds it,
  and I read no further than the title line. Taking anything from it
  here would be transfer by analogy.

- **`dev/literature/geology.md`: NOT USED, declined.** At
  `dev/literature/geology.md:1`:

  > # Geology dossier: set-theoretic geology sources and the five questions

  Set-theoretic geology sources for `[L6]`. Nothing in mantles, grounds
  or the approximation property bears on an ordinality slot inside the
  Skolem hull.
