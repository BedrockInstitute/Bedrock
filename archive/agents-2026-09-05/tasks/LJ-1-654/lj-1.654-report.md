# LJ-1.654 report: does the collapse reflect ordinality

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.654
obligation: agents/tasks/LJ-1-654/Probe654.agda::PiReflectsOrd
verdict: **GO. `PiReflectsOrd` IS TRUE AND IT IS BUILT.** The ordinal
conditioning can be discharged downstream, so the un-ordinal keystone is
preferable and not mandatory.

The obligation is green and metered (`runs/meter-obligation.out`,
`pass exit=0 3.28 s`, `0 UNRESOLVED of 1`, `probe_red=False`). Every
other name in the probe is green too (`runs/meter-names.out`,
`0 UNRESOLVED of 12`).

**READ THESE FOUR SENTENCES BEFORE YOU QUEUE ANYTHING.**

1. **THE FACT IS TRUE AND THE PRICE IS 120 LINES.** The proof proper is
   120 non-blank non-comment lines, inside the brief's estimate of 60 to
   130. It was green on the first attempt (`runs/w3-1.out`).
2. **`[LJ-1.649]`'s FIFTH HYPOTHESIS IS NOW DISCHARGED, BY IMPORT AND
   NOT BY COPY.** `fifth` (`agents/tasks/LJ-1-654/Probe654.agda:366`) inhabits
   `LJ-1-649.Probe649`'s own `PiReflectsOrd`, and
   `levelin-discharged` (`agents/tasks/LJ-1-654/Probe654.agda:374`) is `[LJ-1.649]`'s
   `levelin-from-647` with that hypothesis gone. Agda checked the match
   in the same process (`runs/p-1.out`, both modules named).
3. **THE HULL'S DEFINABLE CLOSURE IS LOAD BEARING, NOT THE COLLAPSE
   ALONE.** `[LJ-1.649]` section 4.1 was right to be careful. Red slice
   1 measures the direct route: it leaves THREE holes and every one is a
   hull membership for a set with no reason to be a hull member
   (`runs/no-hull-1.out`).
4. **THE FORWARD DIRECTION IS ALSO BUILT, AND IT IS MUCH CHEAPER.** It
   is 34 lines and it needs no hull closure at all
   (`agents/tasks/LJ-1-654/Probe654.agda:315-352`). Section 5 says why the sweep asked for it.

Written as a skeleton before any Agda beyond the floor and filled as
each answer landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-654/`. Agda ran under the caliber the program set on
this pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier, ONE Agda process at
a time. I did not set `GHCRTS`. Nothing is postulated, the probe carries
`--safe`, the delivered probe carries no hole, and nothing lands in
`src/`. The probe is a raw `.agda` file, so it carries no ` ```agda `
fence, counts 0 in-fence lines, and the ratio bar cannot fire on it.

**NO HEAP WALL WAS MET ANYWHERE IN THIS TASK.** The highest peak of any
run is 1,003,814,912 bytes against the 2,147,483,648-byte wide cap,
which is 47 % of it. That run is `runs/p-final.out`, the delivered
bytes. The longest Agda run is 5.78 s (`runs/p-5.out`) against the caps
I set (600 s for the floor and the red slices, 900 s for the probe and
the miniature). The caps are wall-clock caps enforced by a perl alarm
(`runs/run.sh` carries the mechanism), because this macOS has no
`timeout` ([LJ-1.602], [LJ-1.610]).

**EVERY NUMBER BELOW IS MEASURED WITH A WARM `src/` INTERFACE CACHE**
(708 `.agdai` files under `_build/` at the start of the task). No number
here is a cold-cache number, and this report does not bound one.

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

`[LJ-1.649]` closed **GO** on its obligation
(`agents/tasks/LJ-1-649/lj-1.649-report.md:9-11`). It names no statement
FALSE. The standing coder clause is satisfied: the type I built is the
type that predecessor delivered, at
`agents/tasks/LJ-1-649/Probe649.agda:222-223`, and its file is green
(`agents/tasks/LJ-1-649/lj-1.649-report.md:297-303`, three forced
rechecks, exit 0 every time).

**I DID NOT COPY THAT TYPE. I IMPORTED IT.** `agents/tasks/LJ-1-654/Probe654.agda:49` imports
`LJ-1-649.Probe649`, and `fifth : P649.PiReflectsOrd`
(`agents/tasks/LJ-1-654/Probe654.agda:366-367`) inhabits the predecessor's own name. The
typechecker now answers the clause instead of my reading of it.
`runs/p-1.out` shows both modules checked in one process.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection and it does not start phase 3.
No Boundary clause is in conflict.

## 2. THE FLOOR, MEASURED BEFORE ANY PROOF

The standing coder clause orders a floor before a heavy object. I ran
it. `runs/FLOOR.agda.txt` is the frame, the obligation stated, and a
HOLE where the term goes. It is `.agda.txt` and not `.agda`, because
every `.agda` under a task home is a verification target of the
acceptance run (`scripts/pod/facts.py:489`, `verification_target`).

**THE FRAME COSTS 0.74 GiB AND 3.13 s.** Three forced rechecks, the
interface deleted before each: 3.13 s, 3.08 s, 3.15 s. Median wall
**3.13 s**. Median peak RSS **799,719,424 bytes**. Exit 42 every time,
with ONE error and it is the hole. `runs/floor-1.out` records it as
`[UnsolvedInteractionMetas]` at line 83, column 19 to 23, of the
reproduced copy. The evidence is the `.out`, because the `.agda` copy
was deleted.

**THE IMPORT TRIM.** I started from `[LJ-1.649]`'s import set
(`agents/tasks/LJ-1-649/Probe649.agda:34-46`) and added exactly what the
proof names. The additions are `FOL.Syntax`,
`FOL.Manipulation.Relabelling` (for `mapFo`), `Cubical.Data.Sum`,
`Cubical.Data.Empty` and **`L.BoundedSubset`**, for `module HullExt`
alone. The last one is the expensive one and section 6 prices it: it is
0.36 GiB of the frame's 0.74.

**The frame is not the problem here.** The delivered probe is 1.00 GiB
and 3.91 s, so the whole proof adds 0.19 GiB over the floor. This object
is not heavy and the floor proved it before any proof was attempted.

## 3. THE PROOF

### 3.1 Why the collapse alone does not do it

`IsOrd A` is `isTransV A × ((x : S) → ⟨ x ∈ˢ A ⟩ → isTransV x)`
(`src/L/Constructible.lagda.md:141-142`). So the obligation asks two
things of `y`, and both quantify over sets that are **members of members
of a hull member**.

**THE HULL IS NOT TRANSITIVE.** So those sets are not hull members. The
collapse's two transport lemmas both demand hull membership:
`π∈-fwd` wants the lower endpoint in the carrier
(`src/V/Collapse.lagda.md:102`) and `π∈-bwd` wants BOTH endpoints in
it (`src/V/Collapse.lagda.md:282-283`). `[LJ-1.649]` section 4.1 flagged
this and did not price it
(`agents/tasks/LJ-1-649/lj-1.649-report.md:241-244`).

**I MEASURED IT RATHER THAN ARGUED IT.** `runs/NO-HULL.agda.txt` is the
obvious route: cross with `π∈-fwd`, use the range's transitivity, come
back with `π∈-bwd`, and no hull extraction anywhere. It leaves THREE
holes and everything else closes (`runs/no-hull-1.out`, three
`[UnsolvedInteractionMetas]` at `65.23-34`, `66.30-41`, `67.30-41`).
Every hole is a hull membership.

### 3.2 The cure, and W2 (DD4)

The cure is the hull's own definable closure. A GLOBAL witness of a
defect can be replaced by a HULL witness of the SAME defect, and only
then does the crossing to the range become legal.

**W2 IS ANSWERED BY ONE TERM.** `lift-to-hull`
(`agents/tasks/LJ-1-654/Probe654.agda:121-123`) is the whole of it, and it is generic in the
formula:

```
lift-to-hull : (φ : Formula Code 1) (a : ASt.SL) → Sat a φ
             → ∥ Σ[ b ∈ ASt.SL ] (⟨ fst b ∈ˢ M ⟩ × Sat b φ) ∥₁
lift-to-hull φ a sat = H.hull-closed φ ∣ a , sat ∣₁
```

It is `H.hull-closed` (`src/L/Hull.lagda.md:415-417`) with the
truncation introduced, it is three lines, and it is instantiated THREE
times. Every use of the hull in this file goes through it. No second
proof of the same fact exists in the file, and the deadline did not
force a fixed form, so W2 raises no conflict to report.

The instances are three formulas, ten lines together
(`agents/tasks/LJ-1-654/Probe654.agda:131-148`):

| name | reading | where it is used |
|---|---|---|
| `φ-deep` | `∃t (w ∈ t ∧ t ∈ c) ∧ ¬ (w ∈ c)` | step 1, first pass |
| `φ-mid` | `d ∈ w ∧ w ∈ c` | step 1, second pass |
| `φ-bad` | `∃u ∃v ((v ∈ u ∧ u ∈ w) ∧ ¬ (v ∈ w)) ∧ w ∈ c` | step 2 |

### 3.3 Step 1: the collapse reflects transitivity

`trans-reflect` (`agents/tasks/LJ-1-654/Probe654.agda:163-226`, 56 lines) takes `y ∈ M` and
`isTransV (C.π y)` and returns `isTransV y`. LEM decides the goal, which
is a proposition, so only the negative branch does work.

`φ-deep` lands the LOWER endpoint in the hull. It also names an
intermediate set `t`, but `t` is the witness of an object-language `∃`
evaluated in the STAGE, so `t` is a stage member and not a hull member.
`φ-mid` is the second pass and it lands that intermediate set too. Now
both endpoints are inside `M`, the range's transitivity fires, and
`IE.π∈-bwd` carries the membership back to contradict the defect
`φ-deep` carried across.

**THE SECOND PASS IS NOT DECORATION, AND I MEASURED THAT TOO.**
`runs/NO-MID.agda.txt` is the same term with `φ-mid` deleted. It leaves
EXACTLY ONE hole, at `⟨ fst t ∈ˢ M ⟩` (`runs/no-mid-1.out`, one
`[UnsolvedInteractionMetas]` at `165.43-58`). One extraction per defect
is not enough; two are.

### 3.4 Step 2: every member of a hull member is transitive

`mem-trans` (`agents/tasks/LJ-1-654/Probe654.agda:239-287` in the delivered file, 46 lines)
has the same shape and one difference. The member `x ∈ y` is not a hull
member either, so the range's SECOND ordinal conjunct cannot be read at
it. `φ-bad` replaces `x` by a hull member `x'` that is still a member of
`y` and still carries the same non-transitivity. At `x'` the range's
second conjunct fires, and **step 1 turns it back into transitivity of
`x'`**, which `x'`'s own defect contradicts.

Step 1 is used here and nowhere reproved. That is the second half of the
W2 answer: two conjuncts, one reflection lemma.

### 3.5 The obligation

`PiReflectsOrd` (`agents/tasks/LJ-1-654/Probe654.agda:295-297`) is step 1 at the range's first
conjunct and step 2 at its second, and nothing else.

## 4. WHAT THE GO IS WORTH, MEASURED AND NOT ARGUED

`[LJ-1.649]`'s `levelin-from-647` took FOUR hypotheses
(`agents/tasks/LJ-1-649/Probe649.agda:227-230`). With `fifth` supplied
it takes THREE, and the remaining two objects are `[LJ-1.462]`'s step 2
in `[LJ-1.647]`'s ordinal-conditioned form, and its step 4:

- `levelin-discharged` (`agents/tasks/LJ-1-654/Probe654.agda:374-377`), green.
- `levelin-discharged-ord-commute` (`agents/tasks/LJ-1-654/Probe654.agda:383-386`), green,
  and it is the variant a consumer is more likely to be able to supply,
  because `[LJ-1.477]` closed NO-GO on the UNconditioned commute
  (`agents/tasks/LJ-1-477/lj-1.477-report.md:273-275`).

**THE BRIEF'S QUESTION IS ANSWERED IN THE BRIEF'S OWN TERMS.** GO
deletes a hypothesis from four consumers. The ordinal conditioning CAN
be discharged downstream. So the UN-ordinal keystone is not mandatory,
and `[LJ-1.646]` may be priced as preferable rather than as the only
route.

## 5. BEYOND THE OBLIGATION: THE FORWARD DIRECTION

The brief asked for the REFLECTION only. **The sweep found that the four
consumer sites need the FORWARD direction as well, so I priced it while
the frame was live.** Every one of the four carries `levelIn` beside a
`cover`, and `cover` PRODUCES `IsOrd γ` at a `γ ∈ˢ C.πX`
(`src/L/BoundedSubset.lagda.md:918`). That is a range-side conclusion
from hull-side data, which is preservation and not reflection.

`trans-preserve` and `PiPreservesOrd` (`agents/tasks/LJ-1-654/Probe654.agda:315-352`) are 34
lines and they are green. **They need no hull closure at all**, and the
reason is exact: `π-member` hands back preimages that are ALREADY hull
members (`src/V/Collapse.lagda.md:63-64`), where a member of a hull
member is not. Injectivity is the only tree fact they spend.

`pi-ord-iso` (`agents/tasks/LJ-1-654/Probe654.agda:354-356`) states the two directions as one.
It is the ordinal half of the isomorphism reading that
`C.InjExt.iso` gives for membership
(`src/V/Collapse.lagda.md:299-301`), and it is what
`dev/literature/devlin-II5.md:200-201` asserts of the Collapsing Lemma.

**I DO NOT CLAIM THIS CLOSES `cover`.** `cover` also demands
`⟨ C.π y ∈ˢ Lset γ ⟩` and a `γ ∈ˢ C.πX`, and I measured neither. The
claim here is narrower: the ordinal conjunct of `cover` is no longer
unbuilt.

## 6. THE THREE RED SLICES, AND WHAT EACH ONE PRICES

All three are `.agda.txt` and all three are red by design. The `.agda`
copies used to run them were deleted, so no red file remains under this
task home. Each carries its own reproduction recipe at the head.

| slice | holes | what it measures |
|---|---|---|
| `runs/NO-HULL.agda.txt` | 3 | The collapse alone does not do it. Every hole is a hull membership |
| `runs/NO-MID.agda.txt` | 1 | One extraction per defect is not enough. The hole is `⟨ fst t ∈ˢ M ⟩` |
| `runs/NO-INJ.agda.txt` | 1 | Injectivity is spent at ONE site, and `L.BoundedSubset` is imported for it alone |

**RED SLICE 3 ALSO PRICES THE IMPORT.** With `L.BoundedSubset` not
imported at all, the whole file still closes except one application, and
the peak RSS falls from 881,246,208 bytes to 519,012,352
(`runs/w3-2.out` against `runs/no-inj-2.out`). So the one tree fact
`[LJ-1.649]` section 4.1 named second costs **0.34 GiB of frame** and
**one line of proof**. A cheaper structure extensionality for this hull
would change that one line.

## 7. THE SWEEP (C-42), RUN THOUGH NO REFUTATION LANDED

C-42 fires on a refutation. **No refutation landed here**, so the law
does not bite. I ran the sweep anyway, because `[LJ-1.649]` counted four
sites and the count is what this GO is priced against.

**`[LJ-1.649]`'s COUNT OF FOUR IS CONFIRMED.** The `levelIn` hypothesis
occurs at exactly four live sites in `src/`:

- `src/L/BoundedSubset.lagda.md:917` (`module Condense`)
- `src/L/BoundedSubset.lagda.md:1671` (`module Co`)
- `src/L/StageBound.lagda.md:80` (`module Co`)
- `src/L/StageBound.lagda.md:106` (an anonymous `module _`)

**AND EVERY LINE NUMBER `[LJ-1.649]` GAVE IS RIGHT.** I re-read all
eight. `agents/tasks/LJ-1-649/lj-1.649-report.md:262-263` cites the
`cover` companions at `:919`, `:1673`, `:82`, `:108`, which are the
CONTINUATION lines and not the binder lines. That is correct for what it
says, because `IsOrd γ` occurs on the continuation line and not on the
binder. The binder lines are `:918`, `:1672`, `:81`, `:107`.

**AND THE SWEEP FOUND ONE THING `[LJ-1.649]` DID NOT SAY.** `cover` does
not CONSUME range-side ordinality. It PRODUCES it. Section 5 is that
finding built rather than reported.

## 8. RUNS, EVERY NUMBER

Caliber `-A64m -I0 -M2g`, set on the pane by the program and untouched
here. ONE Agda process at a time, from the repository root, warm `src/`
cache. The `LJ-1-654` interfaces were deleted before every forced
recheck.

**The floor**, `runs/FLOOR.agda.txt`, red by design (one hole):

| run | wall s | peak RSS bytes | exit |
|---|---|---|---|
| `runs/floor-1.out` | 3.13 | 799,719,424 | 42 |
| `runs/floor-2.out` | 3.08 | 799,719,424 | 42 |
| `runs/floor-3.out` | 3.15 | 799,735,808 | 42 |

Median wall **3.13 s**, median peak RSS **799,719,424 bytes**.

**W3, the decisive miniature**, `runs/W3.agda`, green, 160 non-blank
non-comment lines of which 120 are the proof proper and 40 the frame:

| run | wall s | peak RSS bytes | exit |
|---|---|---|---|
| `runs/w3-1.out` | 4.49 | 881,246,208 | 0 |
| `runs/w3-2.out` | 4.18 | 881,246,208 | 0 |
| `runs/w3-3.out` | 4.11 | 881,278,976 | 0 |

Median wall **4.18 s**, median peak RSS **881,246,208 bytes**. `w3-1` is
the FIRST run of the proof and it was green on the first attempt.
`runs/w3-final.out` (4.05 s, 881,246,208 bytes, exit 0) re-checks the
same file after the red `.agda` copies were deleted.

**The delivered probe**, `Probe654.agda`, three forced rechecks after
the forward direction landed:

| run | wall s | peak RSS bytes | exit |
|---|---|---|---|
| `runs/p-6.out` | 3.97 | 1,003,814,912 | 0 |
| `runs/p-7.out` | 3.91 | 1,003,814,912 | 0 |
| `runs/p-8.out` | 3.91 | 1,003,814,912 | 0 |

Median wall **3.91 s**, median peak RSS **1,003,814,912 bytes**.
`runs/p-final.out` (5.08 s, 1,003,814,912 bytes, exit 0) is the
delivered bytes.

**The earlier probe runs, before the forward direction was added.**
`runs/p-1.out` (4.96 s, 902,594,560 bytes, exit 0) is the first run and
it typechecked `LJ-1-649.Probe649` in the same process, which is where
`fifth` was first accepted. `runs/p-2.out`, `p-3.out` and `p-4.out` are
its three forced rechecks (4.39, 4.40, 4.27 s; 957,808,640,
957,841,408, 957,841,408 bytes; exit 0). `runs/p-5.out` (5.78 s,
927,809,536 bytes, exit 0) is the first run WITH the forward direction,
and it too was green on the first attempt.

**The three red slices**, all `.agda.txt`, all by design:

| run | wall s | peak RSS bytes | exit | what it shows |
|---|---|---|---|---|
| `runs/no-hull-1.out` | 3.79 | 715,882,496 | 42 | THREE holes, all hull memberships |
| `runs/no-mid-1.out` | 3.76 | 764,624,896 | 42 | ONE hole, at `⟨ fst t ∈ˢ M ⟩` |
| `runs/no-inj-1.out` | 4.69 | 306,872,320 | 42 | ONE hole, at the backward membership |
| `runs/no-inj-2.out` | 3.28 | 519,012,352 | 42 | the same, forced recheck |
| `runs/no-inj-3.out` | 2.99 | 519,061,504 | 42 | the same, forced recheck |

For `no-inj` the median wall is **3.28 s** and the median peak RSS is
**519,012,352 bytes**. `no-inj-1` ran before its interfaces were
deleted and its 306,872,320-byte peak is the odd one of the three; I
report it and I do not use it.

**The meters:**

- `runs/meter-obligation.out`: `pass exit=0 3.28 s`,
  `0 UNRESOLVED of 1`, `probe_red=False`.
- `runs/meter-names.out`: twelve names, `0 UNRESOLVED of 12`, 3.38 s,
  `probe_red=False`.

This worktree has no `.venv`. The meter ran as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py`.

**The individual gates**, run while I worked, as the Boundary orders:
`lint-prose.py --check`, `lint-agda.py --check`,
`check-probes.py --check` (`clean, 9930 tracked files`) and
`check-fences.py --check` (`clean, 103 masters`) all pass. I did NOT run
`make check`: its `typecheck` target runs the whole tree under its own
caliber, and the standing coder clause forbids me a second caliber.
The Boundary makes `make check` the gate before a commit, and I do not
commit.

**Against the brief's estimate.** The brief priced W3 at "60 to 130
lines", basis `[LJ-1.649]`'s 2.59 s assembly in the same frame. The
proof proper is **120 non-blank non-comment lines** and the frame is 40
more. The delivered probe is 217 non-blank non-comment lines over 404
total, and the extra over the miniature is the forward direction (34),
the predecessor discharge (11) and the comments.

**Two things the brief guessed and the measurement corrected.** The
brief's basis sentence said the frame "is the same one" as
`[LJ-1.649]`'s. It is not: this task adds `L.BoundedSubset`, and that
import alone is 0.34 GiB (section 6). And `[LJ-1.649]`'s assembly was
2.59 s where this floor alone is 3.13 s. Neither correction changes the
verdict.

## 9. WHAT THE NEXT BRIEF NEEDS

**`[LJ-1.646]` IS NOW A PREFERENCE AND NOT A GATE.** `[LJ-1.649]`
section 7 said the un-ordinal `lset-code` was "worth that price" because
it deletes the fifth fact from four consumers. That price is now paid
another way, and it cost 120 lines. The ordinal-conditioned keystone
costs nothing downstream any more. If `[LJ-1.646]` is expensive, this
task is the reason it may be re-priced or dropped.

**`levelIn` NOW REDUCES TO EXACTLY TWO OBJECTS AT EVERY CONSUMER**, and
neither is this task's:

- step 2, `HullClosedLsetOrd`, which `[LJ-1.647]` reduced to the
  keystone
- step 4, `PiCommuteLset` or `PiCommuteLsetOrd`, on which `[LJ-1.477]`
  closed NO-GO at the join of the two computation laws
  (`agents/tasks/LJ-1-477/lj-1.477-report.md:273-275`)

**STEP 4 IS THE WIDEST UNMEASURED TERM I CAN SEE FROM HERE**, and
`levelin-discharged-ord-commute` is the reason to attack the
ORDINAL-conditioned form of it first: it is a weaker statement, it costs
the consumer nothing extra, and `[LJ-1.477]`'s NO-GO was measured
against the UNconditioned one. I did not price it and I do not claim it
is reachable. The mathematician names the probe.

**`cover` IS HALF BUILT NOW.** Its `IsOrd γ` conjunct is
`PiPreservesOrd` (section 5). What remains unmeasured at `cover` is
`⟨ γ ∈ˢ C.πX ⟩` and `⟨ C.π y ∈ˢ Lset γ ⟩`. A brief that attacks `cover`
should take `PiPreservesOrd` as delivered and not reprove it.

**TAKE `lift-to-hull`, DO NOT REPROVE IT.** It is three lines and it is
generic in the formula (`agents/tasks/LJ-1-654/Probe654.agda:121-123`). Any obligation that
must move a global witness into the hull is an instance of it. This task
found three instances; there will be more.

**ONE WARNING ABOUT THE IMPORT.** This probe imports `L.BoundedSubset`
for `module HullExt` alone, and that costs 0.34 GiB of frame. A consumer
inside `L.BoundedSubset` itself pays none of it, because `HullExt` is
already in scope there (`src/L/BoundedSubset.lagda.md:1235`). So the
number in section 8 is a PROBE number and it is not the number this
proof would cost at its consumer site. I did not measure the consumer
site.

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md`: READ.** At
  `archive/dev/LJ-dispatch-index.md:47`:
  `| LJ-1.13 | Build: the collapse at an EXTENSIONAL carrier | DELIVERED +96 | isExt at :31, InjExt at :220. Trivial Inj kept per D-27. F2 corrected: the induction is the same, Xtr was dead code |`
  This row is the provenance of the exact module this task's proof
  spends, `C.InjExt` at `src/V/Collapse.lagda.md:220`, and the line
  numbers it records still hold today. I also read
  `archive/dev/LJ-dispatch-index.md:236`:
  `| LJ-1.160 | Read the 845-line level substrate against levelIn and cover | THE WALL IS BYPASSED, 16 LINES | Both hypotheses from one crossing face at the collapse image. The wall term is absent |`
  It is the earliest record I found that `levelIn` and `cover` travel
  together, which is what section 5 acts on.
- **`archive/dev/JOURNAL-archived.md`: NOT READ, declined.** I grepped
  it for `isExt`, `π∈-bwd` and `InjExt` and it returns nothing. It has
  no bearing on this obligation.
- **`archive/dev/JOURNAL.md`: NOT USED, declined.** Its four hits for
  "collapse" are the other sense of the word, for example
  `archive/dev/JOURNAL.md:412`:
  `collapsed to `⊤̇`, and its bounded clause layer is priced at 470 to 610 lines.`
  That is a formula collapsing, not the Mostowski collapse. Nothing
  there is about this task.
- **`dev/ARCHIVE.md`: NOT USED, declined.** It records no retired
  `Collapse` or `Hull` module (zero grep hits for either), and this task
  retires nothing, so clause W4 has nothing to register.
- **`archive/dev/ORCHESTRATION.md`: NOT USED, declined.** It is the
  archived operating document. It carries nothing about the collapse or
  the hull (zero grep hits for either) and it binds no rule today.

## LITERATURE USED

- **`dev/literature/devlin-II5.md`: READ.** At
  `dev/literature/devlin-II5.md:201`:
  `π : ⟨X, ∈⟩ ≅ ⟨M, ∈⟩, and the transitive-fixing clause π ↾ Y = id ↾ Y for`
  This is the sentence that says the collapse is an ISOMORPHISM and not
  only a surjection, which is why `PiReflectsOrd` had to be TRUE and not
  merely plausible before I started. `[LJ-1.649]` section 4.1 pointed
  here and I checked the line myself.
- **`dev/literature/truncation-and-selection.md`: READ.** At
  `dev/literature/truncation-and-selection.md:143`:
  `the reason: "a proposition-valued goal absorbs the truncation"`
  This is the law the whole proof runs on. Every extraction in this file
  eliminates a `∥ ∥₁` into `Empty.⊥`, which is a proposition, so
  `PT.rec` applies and no choice principle is needed. NINE `PT.rec`
  calls, five in `trans-reflect` and four in `mem-trans`, are that one
  law.
- **`dev/literature/digest.md`: NOT USED, declined.** Its title line
  says it pins the orthodox form of the rud route. This task touches no
  rud function, and I did not read past that line.
- **`dev/literature/terms-2026-08.md`: NOT USED, declined.** It is a
  terminology dossier for the owner's naming ruling. This task adds no
  term and writes no glossary entry.
- **`dev/literature/geology.md`: NOT USED, declined.** It is the
  set-theoretic geology dossier, mantles and grounds. Nothing in it
  bears on the hull, the collapse, or ordinality.
