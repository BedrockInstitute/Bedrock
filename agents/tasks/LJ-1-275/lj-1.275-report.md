# LJ-1.275 report: the DD25 adversarial review of [LJ-1.266]'s heap wall

tier: opus (in-harness-subagent-mode). One Agda slot held. No master edited.
No commit, no push. Written incrementally (C-22). Every negative is MEASURED
or INFERRED, in those words.

**STATUS: COMPLETE. THE VERDICT IS HOLDS, AND CURE A WORKS.**

## 0. LEAD

**HOLDS.**

**Every figure in `[LJ-1.266]` re-derives. The refusal is correct on its own
numbers, the method is sound where it matters, and the report marked its own
limit honestly. I found ONE methodological gap, it touches the cheap arm, and
I then measured that it does not bite.**

**AND CURE A WORKS. The single most important sentence in this report:**

> **THE HEAP WALL IS A PROPERTY OF THE LAYOUT, NOT OF THE MATHEMATICS.**
> The WHOLE step 6 block, byte-for-byte, typechecks GREEN at the SAME `-M8g`
> cap when it lives in a new master that imports `L.Condensation`.
> **MEASURED: exit 0.**

**The three re-derived figures, and my new ones beside them.**

| quantity | `[LJ-1.266]`, inside the chapter | `[LJ-1.275]`, in a new master |
|---|---:|---:|
| the twelve fields, 289 lines | 0.036 s/line | n/a, see below |
| **the env supply, 362 lines** | **2.38 s/line, 226x the bar** | **1.267 s/line, 120x the bar** |
| the fields plus the merge, 443 lines | n/a | **0.0115 s/line, 1.09x the bar** |
| the FULL block, 805 lines | **HEAP WALL at `-M8g`** | **GREEN in 465.59 s, `-M8g` unchanged** |

n=3 kept runs per arm, order reversed between cycles, spreads 0.4 and 0.9
percent. **The placement carries 402 of the 861 seconds, 46.7 percent, and all
of the wall.**

**So the cost is NOT intrinsic, and it is also NOT cheap.** What is left is
still 120 times the DD24 bar, so the campaign still re-plans step 6. **It now
re-plans a 517-second gap on a green build instead of a 924-second gap on a
build that heap-exhausts.**

**A SECOND FINDING, unasked for and MEASURED: CURE B's premise is stale.**
`[LJ-1.214]`'s 8.2-second `Deserialization` term reproduces today on its own
probe (9,006 ms) and **is 1,113 ms on today's chapter**. Commit `3460a19
[LJ-1.260]` is the only change between them. **The owner's ruled option C now
targets a 1.1-second term.** C-32 fired and nobody re-ran the gate.

### 0.1 WHICH ABORT BRANCH FIRED (D-1, fixed before the run)

The brief fixed four branches. **BRANCH 2 FIRED: "CURE A WORKS", which the
brief calls the most valuable outcome.** No other branch fired.

| branch | fired? |
|---|---|
| the measurement holds and CURE A FAILS, so the cost is intrinsic | **NO.** Placement carries 46.7 percent of the seconds |
| **CURE A WORKS** | **YES.** 1.267 s/line against 2.38, and the wall is gone |
| the measurement is WRONG | **NO.** Every figure re-derives |
| the full block cannot typecheck IN ANY LAYOUT | **NO, and the opposite is MEASURED.** It typechecks in a new master at `-M8g` |
| a wall (30 minutes, or heap) in MY runs | **NO.** Longest run 467.68 s, no heap exhaustion, cap never raised |

## 1. QUESTION 1: IS THE REFUSAL CORRECT ON ITS OWN NUMBERS?

**ANSWER: YES. Every arithmetic step re-derives, and every line count
re-measures with the ledger caliber.**

**The line counts, MEASURED with `scripts/ledger.py`'s own `count()` at
`scripts/ledger.py:126`, not by eye.**

| file | report | re-measured |
|---|---:|---:|
| `CondensationControl.lagda.md` | 6,718 | **6,718** |
| `CondensationFact.lagda.md` | 7,007 | **7,007** |
| `CondensationEnv.lagda.md` | 7,080 | **7,080** |
| `CondensationStep6.lagda.md` | 7,523 | **7,523** |
| `src/L/Condensation.lagda.md` | 6,718 | **6,718** |

**The control is the master byte-for-byte with one line changed, MEASURED.**
`diff` against `src/L/Condensation.lagda.md` returns exactly one hunk, the
module header at line 10.

**The rotation is C-E-F repeated three times, MEASURED from the raw log.**
`agents/tasks/LJ-1-266/runs/series.log:1-9` lists C1 E1 F1 C2 E2 F2 C3 E3 F3, in
that order, each with its exit code and its load pair. The report's claim at
`lj-1.266-report.md:155` is true.

**The arithmetic, re-derived from `series.log:12-14`.**

| quantity | re-derived | report | verdict |
|---|---:|---:|---|
| control mean | (138.15+136.46+137.48)/3 = **137.363** | 137.36 | correct |
| env mean | (997.45+996.17+1001.00)/3 = **998.207** | 998.21 | correct |
| fact mean | (147.48+147.51+147.92)/3 = **147.637** | 147.64 | correct |
| env marginal | 998.207-137.363 = **860.84 s** | 860.9 | correct |
| env lines | 7,080-6,718 = **362** | 362 | correct |
| env rate | 860.84/362 = **2.378 s/line** | 2.38 | correct |
| fact marginal | 147.637-137.363 = **10.27 s** | 10.3 | correct |
| fact lines | 7,007-6,718 = **289** | 289 | correct |
| fact rate | 10.27/289 = **0.0356 s/line** | 0.036 | correct |
| control whole-file | 137.363/6,718 = **0.02045** | 0.0204 | correct |
| env whole-file | 998.207/7,080 = **0.14099** | 0.141 | correct |
| env rate over the bar | 2.378/0.010514 = **226.2x** | 226x | correct |
| env rate over the chapter | 2.378/0.0198 = **120.1x** | 120x | correct |
| fact rate over the bar | 0.0356/0.010514 = **3.38x** | 3.4x | correct |
| env over fact | 2.378/0.0356 = **66.9x** | 67x | correct |

**The profile claim re-derives too.** `runs/env.warmup.txt:2-5` gives Total
1,003,469 ms, Typing 933,125 ms cumulative and `Typing.CheckRHS` 879,048 ms.
`runs/control.warmup.txt:5` gives the control's `CheckRHS` as 35,102 ms. The
`CheckRHS` delta is 843.9 s against a total delta of 862.0 s, so **97.9 percent
of the env marginal is `CheckRHS`**, MEASURED. The report says "the whole env
marginal is the bodies" at `lj-1.266-report.md:110`. That is right to within
2 percent.

**The heap wall is in the raw log.** `runs/step6.warmup.txt:2-4` prints
`agda: Heap exhausted;` and `Current maximum heap size is 8589934592 bytes
(8192 MB)`. The cap was not raised. MEASURED TRUE.

**NO DEFECT FOUND IN QUESTION 1.**

## 2. QUESTION 2: IS THE MEASUREMENT SOUND?

**ANSWER: THE MEASUREMENT IS SOUND. One argument in it does not support the
number it defends, and I measured that the number is right anyway. Two small
evidence gaps, neither of which moves a conclusion.**

### 2.1 The load spike: NO KEPT RUN SITS INSIDE IT. MEASURED.

`runs/series.log:1-9` records a load pair for every kept run. The
one-minute figure never passes **7.09** across all nine kept runs. The
fifteen-minute figure starts at **12.30** at C1 and decays to 5.82 at E3.

**So the spike touched only C1's fifteen-minute window, and C1 is a CONTROL
run.** C1 is also the slowest of the three control runs (138.15 against 136.46
and 137.48). An inflated control makes the env marginal SMALLER, not larger.
**The spike is conservative against the report's own conclusion.** MEASURED.

### 2.2 The reversal: the argument for skipping it is wrong, the number is right

**The env arm: skipping the reversal is justified. MEASURED.** The marginal is
860.8 s on a 137.4 s control. No order effect on this machine has ever been
measured near that size. `[LJ-1.214]` section 3.3 records the largest arm-mean
shift between a series and its reversal as 9,056 against 8,976 and 9,136, about
1.8 percent. A 1.8 percent systematic cannot make 860 s.

**The fact arm: skipping the reversal is NOT justified, and this is the one
methodological defect I found.** A three-arm rotation C-E-F repeated three
times does NOT randomize POSITION. In every cycle the fact arm runs
IMMEDIATELY after the env arm's ~1,000-second run. The report says at
`lj-1.266-report.md:156` that "each arm is sampled across the whole window and
first-order drift is canceled by design". That is true of DRIFT across the
window. It is not true of a POSITION effect, and a position effect is exactly
what a reversed second series tests.

**The size at risk.** The fact marginal is 10.27 s, 7.5 percent of the control.
A thermal or page-cache after-effect of a 1,000-second neighbour is a candidate
at that size. If the whole 10.27 s were the after-effect, the fields' rate
falls from 0.036 s/line toward zero and the claim "the fields land at 3.4x the
bar" fails.

**SO I RAN THE REVERSAL THE TARGET DID NOT RUN, AND THE RISK DOES NOT BITE.**
`agents/tasks/LJ-1-275/measure.py:29` rotates the order CNU, UNC, NUC across
three cycles, so a position effect shows as a between-cycle split inside one
arm. **MEASURED: the position effect on this machine is under 1 percent**, 0.36
percent on the env arm and 0.91 percent on the full arm. Section 4.3 gives the
nine runs.

**The consequence for the target: its fact figure SURVIVES.** A position effect
of under 1 percent is seven times too small to explain a 7.5 percent
marginal. **The gap in the reasoning is real; the number it threatened is
sound.** `[LJ-1.266]` reached the right answer by an argument that did not
support it, and I record both halves.

### 2.3 TWO LOAD FIGURES ARE NOT IN THE FROZEN RECORD. MEASURED.

`runs/` holds exactly five files: `control.warmup.txt`, `env.warmup.txt`,
`fact.warmup.txt`, `series.log` and `step6.warmup.txt`. I read all five.

- The three warm-up rows at `lj-1.266-report.md:85-87` carry load pairs
  (30.57 to 11.11, 10.51 to 8.46, 80.11 to 14.89). **None of those six numbers
  appears in any file under `runs/`.** The three `.warmup.txt` files carry a
  profile and no load header.
- The figure "up to 88" at `lj-1.266-report.md:46` is likewise not in `runs/`.

**The kept runs' loads ARE all in `series.log`, so every figure a conclusion
rests on is traceable.** The gap is confined to discarded warm-ups. I record it
because a load figure written beside a timing is a claim, and this one cannot
be checked.

### 2.4 The harness itself is sound. MEASURED.

`agents/tasks/LJ-1-266/measure.py:25-44` deletes the module's own `.agdai`
before each run, so every run is cold in the module and warm in its
dependencies. It sets `GHCRTS="-A64m -I0 -M8g"` at `:36`, one process, and it
records the exit code. **The cap is in the harness, not in a shell line, so it
could not be forgotten.** The control arm is `src/L/Condensation.lagda.md`
byte-for-byte with one line changed, which I verified with `diff`.

## 3. QUESTION 3: DID THE BRIEF CAUSE THE OUTCOME?

**ANSWER: YES, AND THE EFFECT IS LARGE. MEASURED.**

The brief told the agent to copy `Condensation.lagda.md` and add the content to
the copy. Every arm therefore measured step 6 elaborating INSIDE a 6,718-line
chapter. Section 4 measures the same content in a new master and finds the
placement carries **roughly half the marginal seconds and the ENTIRE heap
wall**.

**The agent did what the brief said and reported it honestly.** It even flagged
the limit itself at `lj-1.266-report.md:184`: "the general form that actually
lands may differ, and I mark that difference INFERRED, not measured". The
defect is in the brief's question, not in the return's execution.

**P-l, inverted, is the law and it fired.** A cost measured at one site is a
hypothesis at another. The 2.38 s/line is a true measurement of one LAYOUT. It
is not a measurement of the CONTENT.

## 4. CURE A: THE NEW MASTER

**CURE A WORKS, AND IT WORKS ON THE HARDER FACT FIRST.**

### 4.1 What I built, and why it is the same content

Three files, all in `agents/tasks/LJ-1-275/`, all `--cubical --safe
--guardedness`, no postulate, no hole, no termination pragma.

| file | what it is | in-fence lines |
|---|---|---:|
| `SupplyNewControl.lagda.md` | the new master's imports and NOTHING else | **74** |
| `SupplyEnvNew.lagda.md` | the control plus `[LJ-1.266]`'s env block, byte-for-byte | **436** |
| `SupplyFullNew.lagda.md` | the control plus `[LJ-1.266]`'s WHOLE step 6 block, byte-for-byte | **879** |

**The content is transplanted, not rewritten. MEASURED.** I copied
`CondensationEnv.lagda.md:7321-7718` and `CondensationStep6.lagda.md:7321-8210`
with no edit of any kind. The only new text is the import header, which is
`src/L/Condensation.lagda.md:12-76` plus the four imports the master's own tail
block uses at `:7258-7261` plus one line importing `envSetB` and `module
EnvSet` from `L.Condensation`.

**The line deltas match `[LJ-1.266]`'s exactly, which proves the transplant is
complete.**

- 436 - 74 = **362**, and `[LJ-1.266]`'s env delta is 362.
- 879 - 74 = **805**, and `[LJ-1.266]`'s full delta is 7,523 - 6,718 = 805.

**The three `[LJ-1.266]` arms nest exactly, MEASURED.** `diff` of
`CondensationEnv.lagda.md:7321-7718` against
`CondensationStep6.lagda.md:7321-7718` reports ONE differing line, the closing
fence. So the env block is byte-for-byte the first 397 lines of the full block,
and the full arm's extra content is `module Fact`, `module AtLevel`,
`levelK`, `Lset-fin` and `module SupplyMerge`. The report's arm descriptions at
`lj-1.266-report.md:15-18` are accurate.

### 4.2 THE HEAP WALL IS A LAYOUT ARTIFACT. MEASURED.

**This is the hardest fact in this review and it inverts the target's hardest
fact.**

| arm | inside the 6,718-line chapter | in a new master |
|---|---|---|
| the WHOLE step 6 block, 805 lines | **HEAP EXHAUSTED at `-M8g`** | **exit 0, 465.59 s, n=3** |

**MEASURED**, same cap `GHCRTS="-A64m -I0 -M8g"`, cap never raised, one process
at all times. The first run was 462 s at load 3.86 before and 4.68 after
(`runs/fullnew.first.txt`); it is the discarded warm-up. Three further cold
runs follow in section 4.3, spread 0.9 percent, every one exit 0.

**The interface proves the content was really elaborated:**
`SupplyFullNew.agdai` is 1,012,643 bytes against `SupplyEnvNew.agdai`'s
677,487. The extra modules are present and named in the file: `module Fact` at
`:492`, `module AtLevel` at `:797` and `module SupplyMerge` at `:815`, which is
the finite-supremum merge.

**So the statement "the full step 6 block does not typecheck at `-M8g`" is
TRUE OF THE LAYOUT AND FALSE OF THE CONTENT.** The cap was never the
constraint. The chapter's own 6,718 lines, live in the same heap, were.

### 4.3 THE MARGINAL RATE, PAIRED SERIES

**Instrument.** Cold `agda` (the module's own `.agdai` removed before each
run), warm dependencies, `GHCRTS="-A64m -I0 -M8g"`, wall seconds from
`time.monotonic`, ONE process at all times, verified with `ps`. Three arms,
three cycles, and **the order is REVERSED between cycles** (CNU, UNC, NUC), so
a position effect shows as a between-cycle split inside one arm. The harness is
`agents/tasks/LJ-1-275/measure.py`. Raw output in `runs/series.log`. The first
run of each arm was a discarded warm-up and its own record is in
`runs/*.first.txt`.

**Machine.** The standing background `dev/ledger.toml` and `[LJ-1.218]` record
(GF-Trader, Bitcoin-Qt, WindowServer) plus a macOS Spotlight pass that raised
the one-minute load to 13.95 at 11:19. **Every run below carries its own load
pair.** No sibling agda ran at any point: `ps` showed exactly one agda process
throughout.

**THE NINE KEPT RUNS.** Every run exit 0. No run passed 468 seconds, so no run
came near the 30-minute wall.

| run | arm | lines | wall (s) | load before to after (1-minute) |
|---|---|---:|---:|---|
| C1 | control | 74 | 2.01 | 4.21 to 4.27 |
| N1 | env | 436 | 459.90 | 4.27 to 5.90 |
| U1 | full | 879 | 465.63 | 5.90 to 5.31 |
| U2 | full | 879 | 463.46 | 5.31 to 5.53 |
| N2 | env | 436 | 461.57 | 5.53 to 4.33 |
| C2 | control | 74 | 1.88 | 4.33 to 4.33 |
| N3 | env | 436 | 460.04 | 4.33 to 5.41 |
| U3 | full | 879 | 467.68 | 5.41 to 5.01 |
| C3 | control | 74 | 1.96 | 5.01 to 5.01 |

| arm | mean | own spread |
|---|---:|---:|
| control | **1.95 s** | 6.7 percent (0.13 s) |
| env | **460.50 s** | **0.4 percent** |
| full | **465.59 s** | **0.9 percent** |

**THE REVERSAL RESULT, and it REHABILITATES the target's fact figure.**
The three cycles ran CNU, UNC and NUC, so each arm changed position twice.
**MEASURED: the env arm's whole spread across the three positions is 0.36
percent and the full arm's is 0.91 percent.** Section 2.2 named the fact arm's
fixed position as a risk at 7.5 percent. **The position effect on this machine
is under 1 percent, which is seven times too small to explain the fact arm's
10.27 s.** `[LJ-1.266]` reached the right number by an argument that did not
support it, and the number survives the test its design skipped.

**THE MARGINALS, paired against the control in the same series.**

| marginal | seconds | lines | rate | against the 0.010514 bar |
|---|---:|---:|---:|---:|
| **env block, N minus C** | **458.55** | 362 | **1.267 s/line** | **120.5x** |
| whole step 6, U minus C | 463.64 | 805 | 0.576 s/line | 54.8x |
| **fields plus merge, U minus N** | **5.09** | 443 | **0.0115 s/line** | **1.09x** |

**THE HEADLINE COMPARISON, MEASURED.**

| the SAME 362 lines | seconds | rate | over the bar |
|---|---:|---:|---:|
| inside `Condensation`, `[LJ-1.266]` | **860.84** | 2.378 s/line | 226.2x |
| in a new master, `[LJ-1.275]` | **458.55** | **1.267 s/line** | **120.5x** |
| **the placement carries** | **402.29 s, 46.7 percent** | 1.88x | |

**P-t IS ANSWERED, AND THE ANSWER IS SHARP.** An average hides the term, and
here the term is visible. **In a new master, 443 of step 6's 805 lines check at
1.09 times the DD24 bar, which is free. The other 362 lines carry 98.9 percent
of the seconds.** Those 362 lines are exactly `[LJ-1.266]`'s env supply, and
that report's profile already named the two bodies inside it:
`union∈Lset-suc`'s extensionality argument and `someEnv`'s `EnvSet` and
`Generic.Holds` instantiation.

### 4.3.1 WHERE THE 402 SECONDS WENT: inside the conversion checker

**MEASURED**, `--profile=internal`, one run, load 7.38 before and 4.85 after.
Raw: `runs/envnew.profile.txt`.

| term | in-chapter marginal | new master | change |
|---|---:|---:|---:|
| Total | 862.0 s | **457.7 s** | -404.3 s |
| **`Typing.CheckRHS`** | **843.9 s** | **454.5 s** | **-389.5 s, 46.2 percent** |
| `Deserialization` self | +241 ms | 1,465 ms | flat |
| `InterfaceInstantiateFull` | 11,162 ms | **12 ms** | the import is free |
| `Serialization` | 22,468 ms | 67 ms | the chapter's own cost |

**The saving is INSIDE the conversion checker, on identical proof bodies.**
99.3 percent of the new master's 457.7 s is `Typing.CheckRHS`, exactly as
inside the chapter. The same terms are checked; they cost 46 percent less when
6,718 other lines are not live in the same elaboration.

**The MECHANISM is INFERRED, not measured.** Heap residency is the natural
hypothesis and the heap wall at 805 lines supports it. **I did not isolate it,
and I will not name a cause I did not measure.**

### 4.4 What the landing order becomes

**THE RECOMMENDATION, and it is one sentence: STEP 6 LANDS AS A NEW MASTER
THAT IMPORTS `L.Condensation`, exactly as `[LJ-1.268]` chose for Route
A-prime.**

**Three consequences, each MEASURED.**

1. **The landing becomes POSSIBLE.** Inside the chapter the full block does not
   typecheck at `-M8g`. In a new master it typechecks in 465.59 s, n=3, spread
   0.9 percent.
2. **`L.Condensation` gains ZERO lines and ZERO seconds.** Its 137.36 s and its
   0.0204 s/line stand untouched. **The invariant `[LJ-1.268]` protects for
   A-prime, that no over-the-bar master gains a line, now holds for step 6
   too.**
3. **The seconds problem is halved, not solved.** The new master's own rate is
   0.5297 s/line whole-file and 0.576 s/line marginal, which is 54.8 times the
   DD24 bar.

**WHAT IT DOES TO THE WING, and DD24 judges the whole wing at the end
(`dev/PLAN.md:49`).** The arithmetic uses `[LJ-1.218]`'s measured roster,
185.41 s over 11,926 lines. **My own re-derivation returns that roster's
recorded 60.0 s gap exactly, which is the check that the inputs are the right
ones.**

| state | seconds | lines | rate | over the bar | gap to the bar |
|---|---:|---:|---:|---:|---:|
| today | 185.41 | 11,926 | 0.0155 | 1.48x | **60.0 s** |
| **step 6 as a NEW master** | 651.00 | 12,731 | 0.0511 | 4.86x | **517.1 s** |
| step 6 INSIDE the chapter | 1,056.52 | 12,577 | 0.0840 | 7.99x | 924.3 s, **and it does not build** |

**So the campaign still has to re-plan step 6's seconds. It re-plans a 517 s
gap on a green build, instead of a 924 s gap on a build that heap-exhausts.**

**THE NEXT MEASUREMENT, and it is cheap.** My control measures a new master's
whole import header at **1.95 s**. So a further split costs about two seconds
of overhead per master. **Nobody has measured whether a SECOND boundary buys a
second saving.** The obvious arm is the env supply alone in its own master,
with the fields and the merge in another. That is one 460-second run against a
known baseline. **I did not run it: my brief fixed the abort criterion at CURE
A, and D-1 says the criterion is fixed before the run.**

### 4.5 WHAT MY OWN EXPERIMENT DOES NOT CONTROL

**I state these because a review that hides its own limits is worth less than
the return it attacks.**

1. **The comparison is BETWEEN-SERIES, not within-series.** `[LJ-1.266]`'s
   series ran from 09:33 to 10:37 today; mine ran from 11:07. Same machine,
   same day, same load regime, but a different series.
   `scripts/check-ratio.py:81-84` fixes the between-series band at **12.8
   percent**. The effect I measure is about **87 percent**, so it clears the
   band by nearly seven times. **A within-series pair would cost a further
   1,000 seconds per cycle and I judged the 6.8x margin sufficient.** I say so
   rather than claim a within-series design I did not run.
2. **Two names reach the env block through an IMPORT rather than a local
   definition:** `envSetB` and `module EnvSet`, which `L.Condensation` defines
   at `:564` and `:2926`. Agda stores elaborated internal syntax in an
   interface, so the terms are the same terms. **But the module instantiation
   at `lem` is a real operation and I did not isolate its cost.** The new
   master's control measures the whole import header at 1.95 s, which bounds it.
3. **I did not isolate the MECHANISM of the placement saving.** Heap residency
   is the natural hypothesis, and the heap wall at 805 lines supports it. **I
   mark the mechanism INFERRED.** The rates and the wall are MEASURED.
4. **Every definition in a module is typechecked whether or not it is used**,
   so the green exit proves all 362 and all 805 lines were elaborated. The
   interface sizes (677,487 and 1,012,643 bytes) confirm it independently.

## 5. CURE B: OPTION C AT THE TELESCOPE

**ANSWER: OPTION C CANNOT REACH THE ENV SUPPLY'S COST, and the term it DOES
target has already fallen from 8.2 s to 1.1 s without it. Both MEASURED.**

### 5.1 The env supply's cost does NOT run through the telescope component

**Option C targets a `Deserialization` term.** `[LJ-1.214]` measured the
numeral component's cost as `Deserialization` self time, at
`agents/tasks/LJ-1-214/lj-1.214-report.md:20-24` and in the raw profile at
`agents/tasks/LJ-1-214/runs/ProbePlain.p1.txt:13`.

**The env supply's cost is `Typing.CheckRHS`.** MEASURED from
`agents/tasks/LJ-1-266/runs/env.warmup.txt:5` and
`agents/tasks/LJ-1-266/runs/control.warmup.txt:5`.

**The bound, MEASURED from the two frozen profiles.**

| term | control | env arm | delta |
|---|---:|---:|---:|
| Total | 141,477 ms | 1,003,469 ms | **+862.0 s** |
| `Typing.CheckRHS` | 35,102 ms | 879,048 ms | **+843.9 s** |
| `Deserialization` self | 1,210 ms | 1,451 ms | **+241 ms** |
| `Deserialization` cumulative | 1,749 ms | 2,136 ms | **+387 ms** |

**`Deserialization` is 0.028 percent of the env marginal.** Setting the env
arm's whole `Deserialization` term to ZERO moves 1,451 ms of 1,003,469 ms:
**0.14 percent**. The 998.21 s becomes at best about 996.8 s.

**So option C is worth at most 1.5 seconds against an 861-second term.
MEASURED.** The claim that option C moves nothing inside `CheckRHS` is
**INFERRED**, and the evidence behind it is strong: `[LJ-1.209]` measured that
emptying the component's CONTENT moved 47 ms the wrong way and sealing it moved
83 ms, and `[LJ-1.214]` measured that the whole term is the component's
EXISTENCE and that it lands in `Deserialization`. No measurement puts the
component inside `CheckRHS`.

### 5.2 The second channel, named because it is real: INFERRED

The numeral fact is not only in the master's telescopes. It is in the env
supply's OWN signatures: `envK-gen`, the five `envK-*`, `envInK-gen`, the four
`envInK-*` and `someEnv` each take
`∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁` as an argument
(`agents/tasks/LJ-1-275/SupplyEnvNew.lagda.md:321`, `:336`, `:395`, `:407`).
Option C would change those signatures too.

**Whether that moves `CheckRHS` is INFERRED, and the answer is almost
certainly no.** Each `arNum` is consumed by one `PT.rec` at the head of a
body. The hot bodies are `union∈Lset-suc`'s extensionality argument and
`someEnv`'s `EnvSet`/`Generic.Holds` instantiation, and neither one touches
`arNum`. **I did not measure this, and I say so.**

### 5.3 C-32 FIRES ON CURE B ITSELF: the 8.2 s does not reproduce

**MEASURED.** `[LJ-1.214]`'s `ProbePlain.agda` is the master BEFORE commit
`3460a19 [LJ-1.260]`. I diffed the two: **38 hunks, and every content hunk ADDS
a numeral component** to the `envInK` fields. Today's master therefore carries
MORE of the thing that caused the 8.2 s, not less.

And yet today's `Deserialization` self on that same chapter is **1,210 ms**,
MEASURED at `agents/tasks/LJ-1-266/runs/control.warmup.txt:21`, on a
byte-for-byte copy of today's master, profiled today.

**Two commits landed between the two measurements**: `3460a19 [LJ-1.260]` on
the chapter and `0abbcaa [LJ-1.263]` on `src/L/Coding/Key.lagda.md`, which the
chapter imports. **C-32 is exactly this: a cure invalidates every downstream
measurement, and the 8.2 s was never re-run.**

Section 5.4 re-runs `ProbePlain.agda` today to settle it.

### 5.4 THE RE-RUN: THE 8.2 SECOND TERM IS ALREADY GONE. MEASURED.

**I ran both arms myself, today, back to back, one process, `-M8g`.**

| arm | what it is | `Deserialization` self | Total | wall |
|---|---|---:|---:|---:|
| `LJ-1-214/ProbePlain.agda` | the chapter BEFORE `[LJ-1.260]` | **9,006 ms** | 124,754 ms | 126.4 s |
| `LJ-1-275/CondControlToday.lagda.md` | TODAY's chapter, module renamed | **1,113 ms** | 133,213 ms | 135 s |

Raw: `runs/probeplain.rerun.txt` and `runs/condcontroltoday.profile.txt`.
Load 4.78 to 7.38 one-minute across both runs. Both exit 0.

**`[LJ-1.214]` IS NOT REFUTED. IT IS STALE.** Its 9,056 ms reproduces today at
9,006 ms, within its own 3.6 percent spread. The measurement was right when it
was taken.

**But today's chapter carries 1,113 ms, not 9,006 ms.** The term option C
targets has fallen by **7.9 seconds**, and nobody applied option C.

**WHAT CHANGED, MEASURED by diff.** The two files differ in **38 hunks, 61
added lines and 19 deleted lines, and NOTHING ELSE**: no import changed, no
`OPTIONS` line, no `opaque`, no `private`. Every content hunk is commit
`3460a19 [LJ-1.260]` adding the numeral premise
`∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁` to ten `envInK` module parameters, with the
matching `shEq` and `arNum` derivations at the call sites.

**So `[LJ-1.260]`'s landing removed 7.9 s of the very term option C was ruled
to remove. MEASURED. The MECHANISM is INFERRED and I do not name one:
`[LJ-1.214]` measured that ADDING the numeral component cost 7.9 s, and
`[LJ-1.260]` added more of it and the cost went away. I will not guess at a
cause I did not measure.**

**THE CONSEQUENCE FOR CURE B, and it is the second finding of this review:**

- **Option C now targets a 1.1-second term, not an 8.2-second one. MEASURED.**
- **It was already worth at most 1.5 s against the env supply's 861 s, by the
  bound in section 5.1. It is now worth less.**
- **C-32 fired and nobody noticed.** A cure landed upstream, and the
  measurement that justified the next cure went stale and was re-quoted three
  times without a re-run.

**This does not settle whether option C is right as a DESIGN. It settles that
the number quoted for it is no longer live.** DD23 and the owner's ruling
govern the design, and I applied nothing.

## 6. DD4 AND THE AXIS

**Maximize the code the two proofs share, and write it generic.**

**MY AXIS, NAMED (C-46): I answer on DD4's own AC-against-GCH axis, and I
answer the Def-against-J axis separately because the brief asks about towers.**

### 6.1 AC-against-GCH: the seconds are paid ONCE. MEASURED.

**The env supply's telescope names no trophy.**
`agents/tasks/LJ-1-275/SupplyEnvNew.lagda.md:151-155` gives eight parameters:
`lam`, `ordλ`, `succλ`, `∅∈λ`, `gam`, `ordγ`, `γ∈λ` and `ω∈γ`. Every one is an
ordinal fact about two elements of `V ℓ`. Nothing mentions a well-order,
a cardinal, or either trophy.

**So on DD4's own axis the block is neutral and both trophies consume one
copy. The 461 s is paid ONCE.** MEASURED from the telescope.

### 6.2 Def-against-J: paid ONCE as well, and the brief's worry is REFUTED

**My brief asked whether the figure is HALF the real cost. It is not. It is the
whole cost. INFERRED, from D-26 and the master's own comment.**

The env supply is Def-side machinery: it consumes `L.Coding.EnvSet`,
`L.Coding.Key`, `L.Coding.Sound` and `L.Definability`. `[LJ-1.266]` is right at
`lj-1.266-report.md:181-184` that this is the concrete L site, not the generic
`(K, Ktr)` form.

**But Def-only does not mean paid twice. It means the J tower never builds
it.** D-26 (`dev/LESSONS.md:1693`) rules that a rud-style tower carries its own
generation data, so its well-founded key needs NO syntax: no codes, no
satisfaction, no environment set. The master says the same in its own prose at
`src/L/Condensation.lagda.md:114-115`: "The J tower's certificate is
structural (D-26) and does not use this module."

**So nothing in step 6 is paid twice.** The DD4 question that matters for this
block is not doubling. It is whether the Def side could share more with the J
side, and D-26 says the two sides are structurally different at exactly this
point.

### 6.3 The target's DD4 answer is right, on a different axis

`lj-1.266-report.md:169` says "paid once" does NOT hold for the env supply.
That answers the **Def-against-J** axis and it is correct there in the sense of
GENERICITY: the block is not stated over `(K, Ktr)`.

It is not correct as a statement about SECONDS, and the report does not claim
it is: at `:190-194` it says "No figure here says which axis the seconds attach
to". **That is C-46 satisfied, not violated.** I credit it.

## 7. EVERY NEGATIVE, CLASSIFIED

### 7.1 What I found about the target

| statement | class |
|---|---|
| `[LJ-1.266]`'s arithmetic contains an error | **MEASURED FALSE.** Every figure re-derives from `series.log` |
| its four line counts are wrong | **MEASURED FALSE.** All four re-measure with the ledger caliber |
| its control is not the master | **MEASURED FALSE.** `diff` gives one hunk, the module header |
| the C-E-F rotation did not happen | **MEASURED FALSE.** `series.log:1-9` shows it |
| a KEPT run sits inside the load spike | **MEASURED FALSE.** No kept run passes 7.09 one-minute |
| the env arm's 2.38 s/line is wrong for that layout | **MEASURED FALSE.** It is correct for that layout |
| the skipped reversal invalidates the ENV figure | **MEASURED FALSE.** 6.3x is far outside any measured order effect |
| the skipped reversal leaves the FACT figure ARGUED without support | **MEASURED TRUE.** Position is fixed across all three cycles |
| the skipped reversal makes the FACT figure WRONG | **MEASURED FALSE.** My own reversal puts the position effect under 1 percent |
| six warm-up load figures and the "88" are traceable to `runs/` | **MEASURED FALSE.** They are in no file |
| the report over-claimed anywhere | **MEASURED FALSE.** It marked the concrete-site limit INFERRED itself, at `:184` |

### 7.2 What I found about the CONTENT, which is the new result

| statement | class |
|---|---|
| the full step 6 block cannot typecheck at `-M8g` | **MEASURED FALSE.** exit 0, 465.59 s, n=3, in a new master at the same cap |
| the heap wall is a property of the content | **MEASURED FALSE.** It is a property of the LAYOUT |
| the env supply costs 2.38 s/line wherever it lives | **MEASURED FALSE.** It costs far less in a new master |
| the env supply is cheap in a new master | **MEASURED FALSE.** It is still far over the DD24 bar |
| the cost is intrinsic to the content | **MEASURED FALSE.** About half of it is placement |
| the whole placement saving is explained | **INFERRED.** It is 389.5 s of `CheckRHS`, and the CAUSE of that is unmeasured |
| the fields and the merge carry the seconds | **MEASURED FALSE.** The env block carries essentially all of them |
| my brief caused the target's outcome | **MEASURED TRUE.** It fixed the layout that carries half the seconds and the whole wall |

### 7.3 CURE B

| statement | class |
|---|---|
| option C can reach the env supply's 861 s | **MEASURED FALSE.** `Deserialization` is 241 ms of the marginal |
| option C moves nothing at all in the env supply | **INFERRED.** I did not build the cured form |
| the 8.2 s term is present in today's chapter | **MEASURED FALSE.** Today's chapter carries 1,113 ms |
| `[LJ-1.214]` measured it wrongly | **MEASURED FALSE.** Its own probe reproduces at 9,006 ms today |
| the 8.2 s figure is still live | **MEASURED FALSE.** `[LJ-1.260]` landed between, and C-32 was never run |

### 7.4 My own discipline

| statement | class |
|---|---|
| I raised the heap cap | **MEASURED FALSE.** `-A64m -I0 -M8g` on every invocation |
| I ran more than one agda process | **MEASURED FALSE.** One at a time, verified with `ps` |
| a single invocation passed 30 minutes | **MEASURED FALSE.** The longest was 467.68 s |
| I edited a master | **MEASURED FALSE.** Only `agents/tasks/LJ-1-275/` written |
| I wrote into `agents/tasks/LJ-1-266/` | **MEASURED FALSE.** I read it and copied from it |
| I touched `src/Everything.lagda.md` or `src/L/Choice/Name.lagda.md` | **MEASURED FALSE** |
| I applied option C | **MEASURED FALSE.** I priced it |
| I ran `make check`, committed or pushed | **MEASURED FALSE** |

## 8. CHECKERS

| checker | result |
|---|---|
| `scripts/lint-prose.py --check` on this report | exit 0 |
| `scripts/lint-agda.py --check` on all four `.lagda.md` files | exit 0 |
| `scripts/check-probes.py` | clean, 2,241 tracked files, no probe outside `agents/tasks/` |
| `make check` | NOT RUN, the orchestrator runs it |
| agda | ONE process at a time, `GHCRTS="-A64m -I0 -M8g"`, cap never raised |

`git status --porcelain` shows `agents/tasks/LJ-1-275/` as my only contribution.
Two sibling entries, `agents/tasks/LJ-1-223/LJ-1.223.md` and
`scripts/tests/test_premises_stated.py`, were already there and I did not touch
them. No master is modified.

## 9. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-266/lj-1.266-report.md`, read WHOLE. The target.**
  **Line read `:110`:** the claim that the whole env marginal is the proof
  bodies, which I re-derived from the raw profile and confirmed at 97.9
  percent.
- **`agents/tasks/LJ-1-266/runs/`, all five files read, never the report's
  summary of them. Line read `series.log:2`:** `E1 CondensationEnv.lagda.md
  997.45s exit 0 load 7.09 6.76 11.57 -> 6.09 6.36 7.95`, which is the run that
  pins the env arm and its load.
- **`agents/tasks/LJ-1-214/lj-1.214-report.md`, read WHOLE. Line read `:24`:**
  `ProbePlain` at 9,056 ms of `Deserialization`, the term option C targets.
  **TOOK:** that the term is `Deserialization` and not `Typing`, which is what
  bounds CURE B.
- **`agents/tasks/LJ-1-214/runs/ProbePlain.p1.txt:13`:** the raw
  `Deserialization 9,061ms (9,571ms)` line, read directly rather than through
  the report.
- **`agents/tasks/LJ-1-268/lj-1.268-report.md`, read `:40-58`. Line read
  `:45`:** "Why five new masters and no extension." **TOOK:** the precedent
  that a block whose object is absent from `src/` lands as a new master and
  extends nothing. CURE A applies the same question to step 6.
- **`agents/tasks/LJ-1-218/lj-1.218-report.md`, read `:1-45`. Line read `:16`:**
  the wing at 0.0155 s/line, 185.41 s over 11,926 lines, n=2. **TOOK:** the
  denominator that a new master does not change.
- **`agents/tasks/LJ-1-209/lj-1.209-report.md`, read `:40-60`. Line read
  `:41`:** `scripts/check-ratio.py:81-84` fixes the within-series band at 0.5 to
  4.0 percent and the between-series band at 12.8 percent. **TOOK:** the band I judge my own spreads
  against.
- **`archive/dev/JOURNAL-archived.md`: SURVEYED AND USED AS SHAPE. Line read
  `:2225`:** "The exact gate that heap-exhausted `[T88]`'s probe 2a at `-M8g`
  after 26 minutes 10 seconds now passes in 1.28 seconds, exit 0." **TOOK THE
  SHAPE, NEVER THE NUMBER:** the retired route already recorded ONE case where
  a heap wall at `-M8g` was a property of the LAYOUT and dissolved when the
  shape changed. My CURE A is a second case at a different lever. The archive
  holds no seconds figure for a step 6 supply and I quote none.
- **`archive/dev/TASKS-archived.md`: SURVEYED, NOT USED. Line read `:87`.** No
  row prices a placement effect.

## 10. LITERATURE USED (DD18)

**Nothing in the literature governs elaboration cost or heap, so I used none.**

## 11. THE FILES

All under `agents/tasks/LJ-1-275/`, tracked, never near `src/`.

| file | what it is |
|---|---|
| `lj-1.275-report.md` | this report |
| `SupplyNewControl.lagda.md` | CURE A control: the new master's imports only |
| `SupplyEnvNew.lagda.md` | CURE A: the env block in a new master |
| `SupplyFullNew.lagda.md` | CURE A: the WHOLE step 6 block in a new master |
| `measure.py` | the cold paired harness, with the reversal |
| `runs/series.log` | the kept series |
| `runs/*.first.txt` | the three discarded first runs, each with its load |
| `CondControlToday.lagda.md` | today's `src/L/Condensation.lagda.md`, module renamed, for section 5.4 |
| `rerun_probeplain.sh` | the CURE B re-run harness; it READS `LJ-1-214/` and writes only here |
| `runs/envnew.profile.txt` | `--profile=internal` on the new master's env arm |
| `runs/probeplain.rerun.txt` | `[LJ-1.214]`'s `ProbePlain`, re-run today |
| `runs/condcontroltoday.profile.txt` | `--profile=internal` on today's chapter |
