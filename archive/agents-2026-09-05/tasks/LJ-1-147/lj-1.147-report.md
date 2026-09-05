# LJ-1.147 report: seal `satGraphAt`, and measure what the seal buys

**Status: COMPLETE. The seal LANDED and the tree is GREEN.** Two masters
changed, nothing deleted, nothing committed, nothing pushed. Every consumer
typechecked. Every negative below is marked MEASURED or INFERRED.

## 0. THE ANSWER, in six lines

1. **THE SEAL LANDED GREEN and the wing improved.** Wing **217.50 s to
   200.41 s**, two runs each side, load beside every figure.
   `src/L/Condensation.lagda.md` **126.42 s to 111.20 s, minus 15.2 s**.
2. **`unfolding` COST NOTHING. MEASURED, and this was the task's whole
   point.** The one block that carries it,
   `L.Condensation.SatGraphAgree`, went **8,057 ms to 7,861 ms**. Its two
   sealed definitions went **5,509 ms to 5,340 ms**. **The widest unmeasured
   term of `[LJ-1.145]` closes at MINUS 169 ms.**
3. **THE CURE IS BIGGER THAN PRICED, and it is bigger OFF the wing.**
   `L/Coding/Powerset` **minus 60 percent** and `L/Choice/Adequate` **minus 62
   percent**. Across the 16 masters measured, **minus 38.8 s**.
4. **DD4 VERIFIED BY MEASUREMENT: the AC side got FASTER, not slower.**
   `L/Choice/Internal` plus `L/Choice/Adequate`, **24.18 s to 14.09 s, minus
   41.7 percent**. One edit, both trophies, no consumer edited.
5. **IT STILL DOES NOT CLOSE THE GAP.** The wing lands at **0.01752 s/line
   against the 0.0136 bar, 1.29x**, down from 1.40x. **17.2 s of a 62.0 s
   gap, 27.7 percent.**
6. **AND HERE IS THE STING, which nothing before this run could see.** All
   four masters that got faster off the wing are **INSIDE the AC baseline
   cone**. Recalibrating the bar on the tree the seal produced moves it from
   0.0136 to about **0.01214**, and the wing then reads **1.44x, WORSE than
   the 1.40x it started at**. **INFERRED**, from four measured module savings
   applied to the recorded cone figure; section 8.2 says what would settle it.

## 0.1 The method, fixed before the first run

**The protocol is `scripts/check-ratio.py`'s**, at the ledger's own caliber
`GHCRTS="-A64m -I0 -M8g"` (`dev/ledger.toml:2632`), which the tool reads from
`ratio.ac_baseline_ghcrts` and passes to `check-timing.time_module`
(`scripts/check-ratio.py:143`). Every module is timed COLD with its
dependencies WARM: the tool moves that module's own `.agdai` aside and puts it
back (`scripts/check-timing.py:254-271`).

**Three instruments, each run before and after:**

1. the whole declared wing, 12 masters, which contains
   `src/L/Condensation.lagda.md`;
2. the four masters OUTSIDE the wing that the seal touches:
   `L/Coding/Graph`, `L/Coding/Powerset`, `L/Choice/Internal`,
   `L/Choice/Adequate`. The last two are the AC wing (C-40);
3. `agda --profile=definitions` on `src/L/Condensation.lagda.md`, cold, which
   is what MEASURES the four `SatGraphAgree` definitions that carry the
   `unfolding` block.

**ONE agda process throughout, cap never raised.** The load is recorded beside
every figure and the run count is stated with it.

### 0.1.1 THE INSTRUMENT MOVED UNDER THIS TASK, and that is a finding

**MEASURED.** `scripts/check-ratio.py` was being REWRITTEN by a sibling
dispatch while this task's first BEFORE run was in flight. `git status` at
19:23 shows **237 changed lines** in that file and a new
`scripts/tests/test_ratio_noise.py`, and this task's second invocation died at
19:15 with `TypeError: unsupported operand type(s) for +=: 'float' and 'list'`
on a traceback whose printed source lines did not match the file on disk.
**That lost the first non-wing group's four figures.**

**A before/after measurement whose instrument changes between the two halves
measures the instrument.** So every figure below run 1 comes from
`agents/tasks/LJ-1-147/measure.py`, a pinned harness that calls the two
canonical functions rather than copying them (C-26):
`scripts/check-timing.py:217` `time_module` and `scripts/ledger.py` `count`.
**Both were verified AT HEAD by `git hash-object` at the head of every run**,
and the harness prints that verdict. The caliber still comes from
`dev/ledger.toml`, which is also unmodified.

## 0.2 Machine load and run count, beside every figure

| run | instrument | when | load 1m start / end | result |
|---|---|---|---|---|
| BEFORE 1 | `check-ratio.py` | 19:10 to 19:14 | 3.93 / 4.49 | wing 214.25 s, `Condensation` 124.53 s |
| BEFORE A | pinned harness | 19:28 to 19:33 | 3.49 / 4.40 | wing 217.37 s, `Condensation` 125.67 s, non-wing 49.78 s |
| BEFORE B | pinned harness | 19:33 to 19:38 | 4.44 / 5.31 | wing 217.62 s, `Condensation` 127.17 s, non-wing 49.58 s |
| BEFORE profile | `agda --profile=definitions` | 19:38 to 19:40 | 4.64 / 5.50 | `real 128.40`, total 126,324 ms |
| the seal applied, 21 consumers typechecked | `agda` | 19:41 to 19:46 | — | all exit 0 |
| AFTER A | pinned harness | 19:46 to 19:50 | 6.52 / 4.01 | wing 201.20 s, `Condensation` 111.33 s, non-wing 28.25 s |
| AFTER B | pinned harness | 19:50 to 19:54 | 4.01 / 3.50 | wing 199.62 s, `Condensation` 111.07 s, non-wing 27.72 s |
| AFTER profile | `agda --profile=definitions` | 19:54 to 19:56 | 3.50 / — | `real 111.29`, total 109,118 ms |

**THE MACHINE WAS NOT QUIET, and I say so.** A sibling dispatch
(`[LJ-1.148]`) ran `check-ratio.py --module src/L/BoundedSubset.lagda.md`
repeatedly during this task: seen at 19:27 with `ps`, PID 99820. **My harness
REFUSED to measure beside it** (`runs/before-A.txt`, first attempt) and every
figure above was taken after it went quiet, confirmed by `pgrep -x agda`
returning empty for 30 consecutive seconds before each run started.

**I ran ONE agda process at a time throughout, at `GHCRTS="-A64m -I0 -M8g"`,
never raised the cap, and hit NO heap wall.**

**The pinned harness reproduces `check-ratio.py`**: 217.37 s against 214.25 s
on the wing (1.5 percent) and 125.67 s against 124.53 s on the master (0.9
percent). Two different instruments, two runs, one tree.

Raw output: `agents/tasks/LJ-1-147/runs/`.

## 1. THE BEFORE FIGURES

**BEFORE A, pinned harness, one run, wing** (`runs/before-A.txt`):

| module | lines | seconds | s/line |
|---|---:|---:|---:|
| `src/V/Collapse.lagda.md` | 335 | 1.79 | 0.0053 |
| `src/L/Hull.lagda.md` | 431 | 2.89 | 0.0067 |
| `src/V/Presentation.lagda.md` | 18 | 0.69 | 0.0382 |
| `src/FOL/Count.lagda.md` | 620 | 1.69 | 0.0027 |
| `src/L/StageCardinal.lagda.md` | 482 | 2.31 | 0.0048 |
| **`src/L/Condensation.lagda.md`** | **6,445** | **125.67** | **0.0195** |
| `src/L/Ordinal/SquareLaw.lagda.md` | 775 | 7.90 | 0.0102 |
| `src/L/Ordinal/StageArith.lagda.md` | 75 | 0.93 | 0.0124 |
| `src/L/BoundedSubset.lagda.md` | 1,409 | 15.78 | 0.0112 |
| `src/L/Condensation/TwelveAgree.lagda.md` | 309 | 26.17 | 0.0847 |
| `src/L/Condensation/UpperAgree.lagda.md` | 268 | 11.35 | 0.0424 |
| `src/L/Condensation/LowerAgree.lagda.md` | 265 | 20.20 | 0.0762 |
| **AGGREGATE** | **11,432** | **217.37** | **0.0190** |

**BEFORE A, non-wing, the four masters the seal touches:**

| module | lines | seconds | s/line | wing? |
|---|---:|---:|---:|---|
| `src/L/Coding/Graph.lagda.md` | 99 | 6.34 | 0.0641 | no, the sealed master |
| `src/L/Coding/Powerset.lagda.md` | 395 | 19.10 | 0.0484 | no |
| **`src/L/Choice/Internal.lagda.md`** | 780 | 8.42 | 0.0108 | **AC wing** |
| **`src/L/Choice/Adequate.lagda.md`** | 563 | 15.91 | 0.0283 | **AC wing** |
| AGGREGATE | 1,837 | 49.78 | 0.0271 | |

## 2. THE SEAL, and how many `unfolding` blocks it needed

**Two masters changed. NOTHING was deleted.**

**`src/L/Coding/Graph.lagda.md:203-219`.** `satGraphAt` goes into an `opaque`
block of its own at `:203`. `GraphWitAt` moves ABOVE it, unchanged, because
`graphAt-in`'s type names it. The two readers `graphAt-in` and `graphAt-out`
go into a second block, `opaque unfolding satGraphAt`, which follows the house
pattern at `src/L/Constructible.lagda.md:225-227` and
`src/L/Axioms/Separation.lagda.md:196`: the seal, then its official unfolding.

**`src/L/Condensation.lagda.md:6880-6907`.** `SatGraphAgree.out` and
`SatGraphAgree.back` go into ONE `opaque unfolding satGraphAt` block.

**THE COUNT: ONE `unfolding` block outside the sealing master, over TWO
definitions. MEASURED, by typechecking every consumer.** `[LJ-1.145]`
projected an `unfolding` line at each of five masters
(`lj-1.145-report.md:340-346`). **Three of those five need none**, because
every other consumer builds or reads a witness through `graphAt-in`,
`graphAt-out`, `graphAt-holds`, `graphAt-unique` or `graphAt-value`, which are
function applications and never look inside.

**The lines. MEASURED by `scripts/ledger.py`:** `L/Coding/Graph` 99 to 111,
`L/Condensation` 6,445 to 6,451. **Plus 18 in-fence lines, minus none**,
against `[LJ-1.145]`'s projection of about 25 across five masters.
**Fourteen of the 18 are the two code comments** that record why the seal is
there; four are the three `opaque` keywords and the one `unfolding`. **No line
was deleted to improve a ratio (P-q, DD24).**

## 3. THE MASTER AND THE WING, before and after

**Every figure is the pinned harness, cold, warm dependencies,
`GHCRTS="-A64m -I0 -M8g"`. TWO runs before, and the after column names its run
count beside it.**

### 3.1 The wing

| module | BEFORE A | BEFORE B | AFTER A | AFTER B | delta of means |
|---|---:|---:|---:|---:|---:|
| `V/Collapse` | 1.79 | 1.84 | 1.90 | 1.09 | -0.32 |
| `L/Hull` | 2.89 | 2.92 | 2.77 | 2.72 | -0.16 |
| `V/Presentation` | 0.69 | 0.70 | 0.67 | 0.62 | -0.05 |
| `FOL/Count` | 1.69 | 1.71 | 1.61 | 1.56 | -0.12 |
| `L/StageCardinal` | 2.31 | 2.45 | 2.28 | 2.26 | -0.11 |
| **`L/Condensation`** | **125.67** | **127.17** | **111.33** | **111.07** | **-15.22** |
| `L/Ordinal/SquareLaw` | 7.90 | 7.88 | 7.97 | 7.90 | +0.05 |
| `L/Ordinal/StageArith` | 0.93 | 0.94 | 0.94 | 0.94 | +0.01 |
| `L/BoundedSubset` | 15.78 | 15.96 | 16.03 | 15.84 | +0.07 |
| `L/Condensation/TwelveAgree` | 26.17 | 25.73 | 25.26 | 25.54 | -0.55 |
| `L/Condensation/UpperAgree` | 11.35 | 11.33 | 11.32 | 11.32 | -0.02 |
| `L/Condensation/LowerAgree` | 20.20 | 18.97 | 19.13 | 18.77 | -0.64 |
| **WING** | **217.37** | **217.62** | **201.20** | **199.62** | **-17.09** |
| wing s/line | 0.0190 | 0.0190 | 0.0176 | 0.0175 | |
| wing against the bar | 1.40x | 1.40x | 1.29x | 1.28x | |

### 3.2 The four masters outside the wing, TWO of them the AC side

| module | BEFORE A | BEFORE B | AFTER A | AFTER B | delta of means |
|---|---:|---:|---:|---:|---:|
| `L/Coding/Graph`, the sealed master | 6.34 | 6.33 | 6.30 | 6.30 | -0.04 |
| **`L/Coding/Powerset`** | **19.10** | **19.24** | **7.63** | **7.56** | **-11.58, minus 60 pc** |
| `L/Choice/Internal`, AC | 8.42 | 8.40 | 8.33 | 8.05 | -0.22 |
| **`L/Choice/Adequate`, AC** | **15.91** | **15.62** | **5.99** | **5.81** | **-9.87, minus 63 pc** |
| GROUP | 49.78 | 49.58 | 28.25 | 27.72 | **-21.70** |

**ACROSS ALL 16 MASTERS: 267.18 s to 228.40 s, minus 38.78 s.** Two runs each
side, means compared.

### 3.3 The load, and why the saving is a floor rather than a ceiling

**The AFTER run was measured on a BUSIER machine than the BEFORE runs.** Load
1m at the head of `L/Condensation`: **3.26 in BEFORE A, 4.53 in BEFORE B,
5.97 in AFTER A.** A busier machine reads SLOWER, so the measured saving is
the conservative end. **MEASURED, not inferred: the loads are in
`runs/before-A.txt`, `runs/before-B.txt` and `runs/after-A.txt` beside every
module.**

**The two BEFORE runs agree to 1.2 percent on the master and 0.1 percent on
the wing**, so the instrument is not the source of a 15-second move.

### 3.4 `[LJ-1.148]` landed mid-task, and it does not move this delta

`[LJ-1.148]` committed at `a37e3fd` while this task ran, and its finding is
that the instrument's error is **a fixed cost of about 0.9 s on the FIRST
Agda invocation of a series, a BIAS rather than noise**. **It does not affect
the comparison above, for two reasons, and both are checkable.**

1. **Every one of my four runs pays it at the same place**: `V/Collapse` is
   module 1 of the wing series in all four. `L/Condensation` is module 6 and
   pays none of it.
2. **My harness predates that fix and does not discard a warm-up run**, so the
   penalty is present on BOTH sides of the comparison rather than on one.

**The tell is in the table.** `V/Collapse` reads 1.79, 1.84, 1.90 and 1.09
across the four runs, a 0.8 s spread on a 1.8 s module, while every larger
module holds to about 1 percent. **That is `[LJ-1.148]`'s 0.9 s, visible in my
data, sitting exactly where it predicts.**

## 4. WHAT `unfolding` COST. MEASURED, and the answer is NOTHING

**The instrument:** `agda --profile=definitions src/L/Condensation.lagda.md`,
cold (own interface moved aside and restored), `GHCRTS="-A64m -I0 -M8g"`,
exit 0, **ONE run per side**. Before at 19:38, `real 128.40`, load 4.64 rising
to 5.5. After at 19:54, `real 111.29`. Raw:
`runs/profile-before.txt`, `runs/profile-after.txt`.

### 4.1 The block that carries the `unfolding`

| definition | BEFORE | AFTER | delta |
|---|---:|---:|---:|
| `SatGraphAgree.back` | 3,470 ms | 3,331 ms | **-139** |
| `SatGraphAgree.out` | 2,039 ms | 2,009 ms | **-30** |
| the two together | **5,509 ms** | **5,340 ms** | **-169** |
| `SatGraphAgree.body-back` | 1,037 ms | 1,015 ms | -22 |
| `SatGraphAgree.body-out` | 1,010 ms | 1,009 ms | -1 |
| **whole `SatGraphAgree` module** | **8,057 ms** | **7,861 ms** | **-196** |

**MEASURED: an `opaque unfolding` block at this scale costs NOTHING.** The
two definitions that must open the seal are 3.1 percent CHEAPER behind it.
**A 169 ms move on a 126-second check is not a saving I claim; it is a
saving I refuse to call a cost.** The abort criterion "`unfolding` costs back
what the seal saves" is **REFUTED. MEASURED.**

**Why, INFERRED and not measured:** the block does not re-elaborate anything.
It restores the definition's visibility for two definitions in one module,
and those two definitions then see exactly the term they saw before the seal
existed.

### 4.2 What the seal bought, in the same run

| bucket | BEFORE | AFTER | delta |
|---|---:|---:|---:|
| **whole check** | 126,324 ms | 109,118 ms | **-17,206** |
| `Miscellaneous` | 62,609 ms | 57,747 ms | -4,862 |
| named definitions | 61,397 ms | 49,020 ms | -12,377 |
| **the `out`/`back` family, 77 definitions** | **35,880 ms** | **23,662 ms** | **-12,218, minus 34 percent** |
| `LeafAgree.out` | 9,833 ms | **1,306 ms** | **-8,527, minus 87 percent** |
| `LeafAgree.back` | 4,289 ms | **1,307 ms** | **-2,982, minus 70 percent** |
| `ExInAgree.back` | 2,426 ms | 1,084 ms | -1,342 |

**`[LJ-1.145]` named `LeafAgree.out` as the master's single most expensive
definition and diagnosed 65 percent of it as ONE coercion. MEASURED here: 87
percent of it went away.** The diagnosis was right and its share was
conservative.

**ONE definition moved the wrong way: `MemAgree.back`, 650 ms to 1,603 ms,
plus 953. MEASURED, one run, and I do not explain it.** It is 7.8 percent of
the named saving and does not change any verdict.

**`Miscellaneous` fell 4,862 ms as well, and the obvious explanation is
REFUTED. MEASURED.** `[LJ-1.145]` read that bucket as module telescopes plus
interface production, and I expected the interface to shrink. It did not:
`_build/2.8.0/agda/src/L/Condensation.agdai` is **5,374,019 bytes before and
5,373,338 after, minus 681 bytes, 0.013 percent.** **So the 4,862 ms is
type-checking outside every definition, not interface production.** That is
`[LJ-1.145]`'s "22,000 ms of type-checking happens OUTSIDE every definition",
and the seal takes a fifth of it. **The mechanism is INFERRED: the same
coercion is paid in module-application instantiation, where no definition name
carries it.**

## 5. THE CONSUMERS. C-40, and this is the rule the task turned on

**`L.Coding.Graph` has 21 transitive consumers**, computed from
`scripts/ledger.py`'s own import graph, not from a grep. **EVERY ONE was
typechecked at `GHCRTS="-A64m -I0 -M8g"`, one process at a time. ALL exit 0.**

| consumer | verdict | seconds, AFTER mean of 2 |
|---|---|---|
| `src/L/Coding/Powerset.lagda.md` | **exit 0** | 7.60 (was 19.17) |
| `src/L/Coding/Sequence.lagda.md` | exit 0 | not timed |
| `src/L/Coding/Uniform.lagda.md` | exit 0 | not timed |
| `src/L/Hierarchy.lagda.md` | exit 0 | not timed |
| `src/L/Model.lagda.md` | exit 0 | not timed |
| `src/L/Hull.lagda.md` | exit 0 | 2.75 (was 2.91) |
| `src/L/BoundedSubset.lagda.md` | exit 0 | 15.94 (was 15.87) |
| `src/L/Condensation.lagda.md` | **exit 0** | 111.20 (was 126.42) |
| `src/L/Condensation/TwelveAgree.lagda.md` | exit 0 | 25.40 (was 25.95) |
| `src/L/Condensation/UpperAgree.lagda.md` | exit 0 | 11.32 (was 11.34) |
| `src/L/Condensation/LowerAgree.lagda.md` | exit 0 | 18.95 (was 19.59) |
| `src/L/Choice/Before.lagda.md` | exit 0 | not timed |
| `src/L/Choice/Faithful.lagda.md` | exit 0 | not timed |
| **`src/L/Choice/Internal.lagda.md`** | **exit 0** | 8.19 (was 8.41) |
| `src/L/Choice/Limit.lagda.md` | exit 0 | not timed |
| `src/L/Choice/Order.lagda.md` | exit 0 | not timed |
| `src/L/Choice/Table.lagda.md` | exit 0 | not timed |
| `src/L/Choice/Transversal.lagda.md` | exit 0 | not timed |
| **`src/L/Choice/Adequate.lagda.md`** | **exit 0** | 5.90 (was 15.77) |
| **`src/Landmarks.lagda.md`**, the AC trophy | **exit 0** | not timed |
| **`src/Everything.lagda.md`**, the whole tree | **exit 0** | not timed |

**MEASURED NEGATIVE: no consumer went red and no consumer needed an
`unfolding` that I did not already add.** `src/Everything.lagda.md` was
typechecked, never edited.

**I did not touch the three `*Agree` masters** (`[LJ-1.144]` and `[LJ-1.145]`
both ruled their fate waits on this measurement). They are timed above only
because they sit in the declared wing, and all three moved by less than one
second.

## 6. THE WING AGAINST THE BAR

| | seconds | lines | s/line | against the 0.0136 bar |
|---|---:|---:|---:|---:|
| BEFORE, mean of 2 runs | 217.50 | 11,432 | 0.01903 | **1.40x** |
| AFTER, mean of 2 runs | 200.41 | 11,438 | 0.01752 | **1.29x** |

**To sit ON the bar the wing may spend 155.58 s. It spends 200.41 s.**

- gap BEFORE: **62.0 s**
- gap AFTER: **44.8 s**
- **closed: 17.2 s, 27.7 percent of the gap.**

`[LJ-1.145]` projected 21 s off the master and about 40 percent of a 55.3 s
gap. **MEASURED: 15.2 s off the master, and 27.7 percent of a gap that today's
machine reads as 62.0 s rather than 55.3 s.** The projection was 38 percent
high on the master and its share of the gap was 44 percent high. **Its CLASS
was right: it named one conversion, one cure and one site, and all three
held.**

## 7. THE AC SIDE. DD4, and it is a MEASUREMENT and not an argument

**The brief asked me to verify that the seal is generic by measuring the AC
side before and after. I did, twice each side.**

| AC master | BEFORE mean | AFTER mean | delta |
|---|---:|---:|---:|
| `src/L/Choice/Internal.lagda.md` | 8.41 | 8.19 | -0.22 |
| `src/L/Choice/Adequate.lagda.md` | 15.77 | 5.90 | **-9.87, minus 63 percent** |
| **together** | **24.18** | **14.09** | **-10.09, minus 41.7 percent** |

**MEASURED: the seal makes the AC side FASTER. It is not a trade.** One edit
in shared upstream machinery serves both trophies, no consumer was edited, and
`src/Landmarks.lagda.md`, which states both trophies, is green.

**Why `Adequate` and not `Internal`, INFERRED.**
`src/L/Choice/Adequate.lagda.md:477` states the coercion this seal kills:
`hgraph` is named at the folded type inside a `DenoteOf` tuple that the caller
builds. `src/L/Choice/Internal.lagda.md` reaches the same formula only through
`graphAt-in` and `graphAt-out`, which are function applications, so it had
almost nothing to save. I did not profile either master.

**The same shape explains `L/Coding/Powerset` at minus 60 percent.**
`src/L/Coding/Powerset.lagda.md:549` splits `⟨ δ ⊨ DefBody w ⟩` and hands the
middle component to `graphAt-unique`, which is `LeafAgree.out`'s pattern
exactly.

## 8. WHAT REMAINS OF THE GAP, and the sting in the tail

### 8.1 The 44.8 s that is left

**MEASURED, from the AFTER profile.** After the seal, the master's remaining
109.1 s is: `Miscellaneous` 57.7 s (52.9 percent), the `out`/`back` family
23.7 s (21.7 percent), everything else 25.7 s.

**The largest remaining term is still not a definition.** No single definition
is above 3.4 s; the largest are `SatGraphAgree.back` 3.33 s,
`PropAgree.subB2T-back` about 3.1 s and `SatGraphAgree.out` 2.01 s.
**MEASURED NEGATIVE: there is still no dominant place to cut**, which is
`[LJ-1.145]` section 4.6 confirmed on the cured tree.

**What would close more, and I price NONE of it because I measured none of
it.** The three candidates, in the order the profile ranks them:

1. **`Miscellaneous` at 57.7 s.** The interface is NOT the term (measured,
   section 4.2), so it is telescope and module-application elaboration.
   `[LJ-1.145]` counted **135 module applications** in the master.
2. **The `out`/`back` family still at 23.7 s over 77 definitions.** The seal
   cured the `satGraphAt` crossing. **Whether the same coercion exists at
   `isCodeAt`, `DefinesAt` or `twelveAt` is UNMEASURED**, and the same probe
   that settled this one would settle those in one run each.
3. **`src/L/Condensation/TwelveAgree.lagda.md` at 0.0817 s/line**, six times
   the bar and untouched by the seal.

### 8.2 THE STING: the bar moves too, and it moves the wrong way. INFERRED

**All four masters that got faster off the wing are INSIDE the AC baseline
cone.** MEASURED with `scripts/ledger.py`'s own closure of
`src/Landmarks.lagda.md`: `L/Coding/Graph`, `L/Coding/Powerset`,
`L/Choice/Internal` and `L/Choice/Adequate` are all in the 73-master cone.

**So the seal makes the DENOMINATOR of DD24's bar cheaper as well.**

| | rate | bar at 1.15x | the wing at 0.01752 |
|---|---:|---:|---:|
| recorded baseline | 0.011828 | 0.01360 | 1.29x |
| **after the seal, INFERRED** | **about 0.01056** | **about 0.01214** | **about 1.44x** |

**Basis, stated so it can be attacked:** the recorded rate implies 203.26 s
over 17,185 cone lines; the four cone masters I measured save **21.7 s**
between them; the cone gains 12 lines. 181.6 s over 17,197 lines is 0.01056.

**Why it is INFERRED and not MEASURED.** I measured four of the cone's 73
masters. **The other 69 are unmeasured**, and 15 of them also import
`L.Coding.Graph`. If any of them saves as well, the bar drops further.

**So the wing improved in seconds and may be judged WORSE in ratio.** That is
P-q's law at a new site: **a shared upstream cure helps the baseline more, per
line, than it helps the wing.** It is not a reason to refuse the cure, because
both wings got faster in absolute seconds and DD5's constraints are absolute.
**It IS a reason not to quote 1.29x.**

**What settles it: `.venv/bin/python scripts/check-ratio.py --recalibrate`, on
a quiet machine.** It times all 73 cone masters cold and prints the figure for
the ledger. **One run, and the whole of 8.2 becomes MEASURED.** I did not run
it because it is the orchestrator's figure to write (the tool says so at
`scripts/check-ratio.py:171-175`) and because a sibling held the machine.

## 9. THE LAW THIS MEASURES, for the orchestrator to number or refuse

`[LJ-1.145]` proposed a law and could not close it. **This run closes it, and
adds the half that was missing.**

**Proposed law.** *Seal the machine formula, not the consumer's alias.* When
an object-language formula appears as a CONJUNCT of larger formulas that
consumers split, the split reduces the conjunct's type while every consumer's
signature names it folded, and the conversion checker walks the whole tree at
every crossing. **Sealing the conjunct at ITS OWN definition makes both sides
the same stuck head.** The `unfolding` blocks that the two readers then need
**cost nothing**, so the cure has no other end to pay at.

**The measurement, 2026-08-13, `[LJ-1.147]`, on the delivered tree.** One
`opaque` on `src/L/Coding/Graph.lagda.md:203`, one `opaque unfolding` at
`src/L/Condensation.lagda.md:6881`, **18 lines added and none deleted**:

| | before | after |
|---|---:|---:|
| the single site the diagnosis named, `LeafAgree.out` | 9,833 ms | **1,306 ms** |
| the `out`/`back` family, 77 definitions | 35,880 ms | 23,662 ms |
| **the block that carries the `unfolding`** | **8,057 ms** | **7,861 ms** |
| the master, cold, mean of 2 runs | 126.42 s | 111.20 s |
| the AC side, two masters, mean of 2 runs | 24.18 s | **14.09 s** |

**The transferable part, and it is the reason this is a law and not a note:**
**three of the five masters that name the sealed formula needed NO
`unfolding`**, because they reach it through named readers. **So the price of
a seal is set by how many definitions look INSIDE the formula, not by how many
name it.** `[LJ-1.145]` priced it by the second count and was 28 percent
high on lines as a result.

**P-t is the parent and this sharpens it.** P-t licenses sealing a built
formula "wherever its consumers do not need to see inside". This says where
the seal GOES when the consumers are two layers down, and it says the cost of
the exception is zero.

## 10. LITERATURE (DD18)

**Nothing in the literature governs elaboration cost.** The term cured here is
a property of Agda 2.8.0's conversion checker.

## 11. ARCHIVE USED

- **`agents/tasks/LJ-1-145/lj-1.145-report.md`, read WHOLE.** **TOOK:** the
  cure and its site at `:289-291`; the arithmetic and its three steps at
  `:318-336`, of which step 4 is the INFERRED one this task closes; the widest
  unmeasured term at `:351-359`, which is section 4 above; the line projection
  at `:340-346`, which I measured 28 percent high; the two refutations at
  `:102-153` and `:189-228`, which I did NOT revisit; and `:404-414`, the
  ruling that the three `*Agree` masters wait on this measurement.
- **`agents/tasks/LJ-1-144/lj-1.144-report.md:1-60`.** **TOOK:** the same
  ruling from the other side, and its BUILD recommendation, which this task
  does not touch. Section 5 above gives it the number it was waiting for.
- **`dev/LESSONS.md`, read whole at each entry.** P-t at `:2619`, **TOOK** the
  licence to seal a built formula, which is the whole cure. P-q at `:2651`,
  **TOOK** the rule that a line lever is not a seconds lever, which is why 18
  lines were added and none removed, and section 8.2 is P-q at a new site.
  P-s at `:2587`, **TOOK** the refusal to divide a slice rate, which is why
  section 8.2 is marked INFERRED. P-m at `:2478` and P-l at `:2323`, for the
  content classes. **C-40 at `:3620`, TOOK the action clause literally**: 21
  consumers, section 5. C-12 at `:2093`, one process at the cap. D-1 at
  `:1038`, rules 1 to 6, read fresh: the harness is tracked in
  `agents/tasks/LJ-1-147/` and is never deleted.
- **`dev/PLAN.md:182`, DD24.** **TOOK:** the bar is a ratio so the content
  must be the same KIND of content, which is why nothing was deleted, and the
  clause that the baseline belongs to ONE tree, which is section 8.2.
- `dev/ledger.toml`, the `[ratio]` table. **TOOK:** the caliber
  `-A64m -I0 -M8g`, `ac_baseline_module_rate = 0.011828` over 17,185 lines,
  `tolerance = 1.15`, and the 12-master `gch_wing` list. Every run above uses
  them.
- `scripts/check-ratio.py:120-145` and `scripts/check-timing.py:217-276`.
  **TOOK:** the exact protocol, which the pinned harness calls rather than
  copies.
- `src/L/Constructible.lagda.md:211-243` and
  `src/L/Axioms/Separation.lagda.md:192-197`. **TOOK:** the house pattern for
  a seal and its official unfolding, which the Graph edit follows.
- `agents/tasks/LJ-1-148/LJ-1.148.md:1-60`, read to identify the sibling
  holding the machine. Nothing taken.

## 12. NEGATIVES, classified as the brief asks

- **`unfolding` costs back the saving: REFUTED. MEASURED.** Minus 169 ms on
  the two definitions that carry it, minus 196 ms on their module. Section 4.1.
  **This was the task's abort criterion and it did not fire.**
- **A consumer goes red: DID NOT HAPPEN. MEASURED.** 21 of 21 at exit 0,
  including `src/Landmarks.lagda.md` and `src/Everything.lagda.md`. Section 5.
- **The seal makes the AC side slower: REFUTED. MEASURED.** The AC side is
  41.7 percent faster. Section 7.
- **The cure closes DD24's gap: NO. MEASURED.** 27.7 percent of it. The wing
  is 1.29x the bar, down from 1.40x. Section 6.
- **The seal shrinks the interface: REFUTED. MEASURED.** Minus 681 bytes of
  5,374,019. Section 4.2.
- **`[LJ-1.145]`'s 21 s projection: 38 percent HIGH on the master. MEASURED.**
  15.2 s. But it under-counted the tree: the total across 16 masters is
  38.8 s, and 10.1 s of that is the AC side it did not price. Section 3.
- **`[LJ-1.145]`'s 25-line projection: 28 percent HIGH. MEASURED.** 18 lines,
  and 14 of those are comments I chose to write.
- **The recalibrated bar makes the wing read WORSE: INFERRED.** Four of 73
  cone masters measured; 69 unmeasured. Section 8.2. **One
  `check-ratio.py --recalibrate` run settles it.**
- **`MemAgree.back` at plus 953 ms: MEASURED, one run, UNEXPLAINED.**
  Section 4.2.
- **The mechanism (a split reduces, the signature folds, so the checker
  walks): INFERRED.** It is `[LJ-1.145]`'s explanation and this run is
  consistent with it. The timings are measured; the story is not.
- **Whether the same coercion exists at `isCodeAt`, `DefinesAt` or `twelveAt`:
  UNMEASURED.** Section 8.1.

## 13. WHAT I DID NOT DO

- **I did not touch the three `*Agree` masters.** They are now measured on the
  cured tree: `TwelveAgree` 25.40 s, `UpperAgree` 11.32 s, `LowerAgree`
  18.95 s, all within 0.7 s of their pre-seal figures. **The seal does not
  change their verdict.** `[LJ-1.144]` and `[LJ-1.145]` can be decided now.
- **I did not commit and did not push.** Two masters are modified, plus this
  report and the harness under `agents/tasks/LJ-1-147/`.
- **I did not run `make check`.** The brief reserves it for the orchestrator.
  I typechecked `src/Everything.lagda.md` instead, which covers the whole
  import closure.
- **I did not write the ledger.** Section 8.2 names the figure that is owed
  and the one command that produces it.
