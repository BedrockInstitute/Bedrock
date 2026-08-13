# LJ-1.148 report: the instrument's noise, measured

## 0. THE SHORT VERSION

1. **The caliber question is settled and `[LJ-1.144]` is wrong.** Both runs
   used `-A64m -I0 -M8g`. The code makes any other outcome impossible.
2. **The noise is not a percentage. It is a FIXED cost of about 0.9 s on the
   first Agda invocation of a series.** MEASURED on two modules whose sizes
   differ twentyfold.
3. **So it is a BIAS, not noise, and it points one way.** A `--module` verdict
   pays it in full; the baseline pays it once over 79 masters. The bar and the
   thing judged against it were measured differently.
4. **Averaging cannot remove a bias.** All three options in the brief treat
   the problem as random. I overrule all three and add a discarded warm-up run.
5. **The residue is real but smaller:** 12.8 percent between separate series,
   about 1 percent within one.
6. **Both verdicts the brief called fragile survive.** `StageArith` and
   `BoundedSubset` are solid UNDER once the first-run penalty comes off.

## 1. THE CALIBER VERDICT: SAME INSTRUMENT. MEASURED, from the source

**`[LJ-1.144]` is wrong and the orchestrator is right. The two runs used the
identical `GHCRTS`.**

### The code has exactly one source of GHCRTS, and no fork

`scripts/check-ratio.py` calls `measure()` at two places and NEITHER can
select a different caliber:

- `scripts/check-ratio.py:326` (the `--recalibrate` path):
  `ghcrts = cfg.get("ac_baseline_ghcrts")`, used at `:330`.
- `scripts/check-ratio.py:454-455` (the `--module` path AND the declared-wing
  path, which are one code path): `ghcrts=cfg.get("ac_baseline_ghcrts")`.

Both read ONE ledger key. `measure()` passes it to the timer, and
`scripts/check-timing.py:247` applies it:

    env = dict(os.environ, GHCRTS=ghcrts or "-M8g")

**So `--module` cannot run at a different caliber from `--recalibrate` inside
one ledger state. No code path allows it.**

### The ledger value was the same for both runs

`dev/ledger.toml:2632` declares `ac_baseline_ghcrts = "-A64m -I0 -M8g"`.

MEASURED, by reading the value out of each commit with
`git show <commit>:dev/ledger.toml`:

| commit | `ac_baseline_ghcrts` |
|---|---|
| `096d49a`, `f48ffd7` | `-A64m -I0 -M16g` |
| `21446f2` `[LJ-1.128]` | `-A64m -I0 -M8g` |
| `8f55b4b`, the tree `[LJ-1.135]` measured on | `-A64m -I0 -M8g` |
| `HEAD` | `-A64m -I0 -M8g` |

The 16g-to-8g change landed at `21446f2`, which is BEFORE `8f55b4b`. So both
runs read `-A64m -I0 -M8g`. `[LJ-1.135]` states the same thing itself at
`agents/tasks/LJ-1-135/lj-1.135-report.md:184-186`.

### Where `[LJ-1.144]` went wrong, and it is worth naming

`[LJ-1.144]` cited the ledger's recorded 22.3 percent cost of a missing
`-A64m -I0` (`agents/tasks/LJ-1-144/lj-1.144-report.md:317-318`). That figure
is real, and it is about a caliber neither run used.

`[LJ-1.135]`'s report DOES contain the string `-M16g`, at
`agents/tasks/LJ-1-135/lj-1.135-report.md:299`. It belongs to the CONTROL run
in the `f48ffd7` worktree, where `[LJ-1.135]` edited that one line down to
`-M8g` so the control matched. It does not belong to the per-module table at
`:335-349`, which is the table `[LJ-1.144]` was reading. **Two calibers are
named in that report and the wrong one was attached to the table.**

### A REAL caliber trap exists in the same code family, and nobody has hit it

MEASURED, from the source, and reported because it is one edit from the defect
`[LJ-1.144]` described:

`scripts/check-timing.py:332` calls `time_module(path, cold=not args.warm)`
with NO `ghcrts`, so `:247` falls back to a bare `-M8g`. And because that line
is `dict(os.environ, GHCRTS=...)`, the keyword OVERRIDES the environment.
**So an agent that runs
`GHCRTS="-A64m -I0 -M8g" .venv/bin/python scripts/check-timing.py <master>`
gets a bare `-M8g` run, silently, whatever it exported.** That is deliberate
for `check-timing.py`, whose `[[hot]]` rows were measured at the bare cap and
whose `:236-245` says so. But the shell export is a no-op that reads like a
setting. It does NOT touch `check-ratio.py`, which passes its own value on
every path, so it does not affect the finding above.

## 2. THE NOISE: a FIXED first-run cost, not a percentage

**MEASURED.** `agents/tasks/LJ-1-148/probe-noise.py`,
`src/L/Ordinal/StageArith.lagda.md`, 75 in-fence lines, 25 cold runs in ONE
series, one Agda process, `-A64m -I0 -M8g`, load 3.15 to 3.57.

| | seconds | s/line | against the 0.0136 bar |
|---|---:|---:|---|
| run 1 | **1.811** | **0.02415** | **1.78x, OVER** |
| runs 2 to 25, mean | **0.787** | **0.01049** | **0.77x, UNDER** |
| all 25, mean | 0.828 | 0.01104 | 0.81x |

**The same module, the same tree, the same instrument, the same minute. Run 1
says OVER by 78 percent. Runs 2 to 25 say UNDER by 23 percent.**

The tail is TIGHT: 24 runs, spread 5.2 percent, min 0.775, max 0.816,
relative standard deviation **1.02 percent**. **The instrument is not
generally noisy. It has one systematic defect and the rest is quiet.**

### The penalty is PER-SERIES, not per-module. MEASURED

One invocation, two modules, three runs each:

| position in the series | module | spread |
|---|---|---:|
| first | `src/L/Ordinal/StageArith.lagda.md` | **79.0 percent** |
| second | `src/V/Presentation.lagda.md` | **2.0 percent** |

**Only the first Agda invocation of a series pays it.**

### It is a FIXED cost of about 0.9 s, and that is why module size decides

| module | lines | run 1 | tail mean | difference |
|---|---:|---:|---:|---:|
| `src/L/Ordinal/StageArith.lagda.md` | 75 | 1.811 | 0.787 | **+1.02 s** |
| `src/L/Ordinal/StageArith.lagda.md` | 75 | 1.700 | 0.864 | **+0.84 s** |
| `src/L/BoundedSubset.lagda.md` | 1,409 | 16.526 | 15.566 | **+0.96 s** |

**Two modules whose seconds differ twentyfold, one penalty of about 0.9 s.**
The BoundedSubset series is at
`agents/tasks/LJ-1-148/boundedsubset-series.txt`.

So the RELATIVE error is set by the module's size:

- a 0.8 s module is inflated by about **125 percent**;
- a 15.6 s module by about **6 percent**;
- a 30 s module by about **3 percent**.

### It decays with idleness, so a real run almost always pays it

MEASURED, five back-to-back series. The warm-up time is the penalty made
visible:

| series | warm-up s | verdict s/line |
|---|---:|---:|
| 1, after an idle gap | **1.68** | 0.0114 |
| 2 | 0.86 | 0.0107 |
| 3 | 0.81 | 0.0104 |
| 4 | 0.78 | 0.0106 |
| 5 | 0.78 | 0.0104 |

**Only series 1 paid.** But a second probe started 30 seconds after the first
finished DID pay it (1.700 against a tail of 0.864). **So the penalty returns
within tens of seconds of Agda idleness.** `check-ratio.py` is invoked once,
by hand, after exactly such a gap. **It therefore pays the penalty nearly
every time it is used.**

### THE CONSEQUENCE FOR DD24, and it is a BIAS

**`check-ratio.py --module X` runs one module once, so it pays the penalty in
full. `--recalibrate` runs 73 to 79 masters in ONE series, so it pays it once
across the whole set: about 0.9 s in 291 s, or 0.3 percent.**

**So the bar was measured almost penalty-free and every module was judged with
the penalty inside it.** That is unlike compared with unlike, in the same
instrument whose own comments already record two earlier versions of that
shape: the target set at `scripts/check-ratio.py:295-317` and the two rates at
`:565-612`. **This one is not the flags and not the target set. It is the
position in the series.**

**It is worst exactly where the brief said verdicts are fragile: the small
modules.**

### It explains the record

| source | StageArith s/line | against the bar |
|---|---:|---|
| `[LJ-1.135]`, one `--module` run | 0.0144 | **1.06x, OVER** |
| the orchestrator, one `--module` run | 0.0124 | 0.91x, UNDER |
| this task, warmed, eight series | 0.0104 to 0.0118 | **0.77x to 0.87x, UNDER** |

**The orchestrator's 20.1 percent was INFERRED and it is real, but it is not
day-to-day machine drift. It is two samples of one biased instrument at
different distances from the same fixed penalty.**

## 3. HOW MANY RUNS A VERDICT NEEDS

**The run count is NOT the binding constraint, and this is where I overrule
the brief's three options. All three treat the error as random. It is a bias,
and a bias does not average out.** The 25-run mean, 0.828, is still 5 percent
above the module's repeatable 0.787, and 250 runs would not fix it.

### The basis

| term | figure | basis |
|---|---:|---|
| first-run penalty | about **0.9 s fixed** | three series, two modules, section 2 |
| within-series repeatability, warmed | **1.02 percent** relative sd | 24-sample tail |
| between-series, warmed | **12.8 percent** range, 5.2 percent relative sd | eight series over about 40 minutes |

95 percent half-width on the mean of the warmed tail, from a relative standard
deviation of 1.02 percent:

| runs | half-width |
|---:|---:|
| 1 | 2.00 percent |
| 2 | 1.41 percent |
| 3 | 1.15 percent |
| 5 | 0.89 percent |
| 20 | 0.45 percent |

**Going from 3 runs to 20 buys 0.7 of a percentage point. Removing the
warm-up run buys up to 125.** And no number of within-series runs touches the
12.8 percent between-series term at all.

### THE ANSWER

**One warm-up plus THREE measured runs: four Agda invocations per module.**

- The warm-up removes the bias, which is the only large term.
- Three runs give a printable spread and put the within-series term under
  1.2 percent, well below the between-series 12.8.
- More than three is waste. Fewer than three prints a spread nobody can read.

**A verdict is trustworthy when the module sits more than about 13 percent
from the bar, and is a coin toss inside that.** DD24's tolerance is 1.15x, so
**the instrument's uncertainty is very nearly the whole tolerance.** That is
the finding the brief predicted, and it survives the correction.

**What it costs.** `StageArith` 3.4 s, `BoundedSubset` 62 s, the declared
twelve-module wing about 4x its current single-run cost. `--recalibrate` pays
ONE extra run on 291 s, which is 0.3 percent.

### Both verdicts the brief called fragile SURVIVE. MEASURED

| module | warmed s/line | against the 0.0136 bar | verdict |
|---|---:|---|---|
| `src/L/Ordinal/StageArith.lagda.md` | 0.0104 to 0.0118 | 0.77x to 0.87x | **UNDER, and outside the band** |
| `src/L/BoundedSubset.lagda.md` | 0.0110 to 0.0112 | 0.81x to 0.82x | **UNDER, and outside the band** |

The brief's `StageArith` figure of 0.91x carried the first-run penalty. The
true reading is further under, not nearer the edge. **The brief's mechanism
was right and its two examples both hold.**

## 4. WHAT I CHANGED IN THE TOOL

`scripts/check-ratio.py`, and `scripts/tests/test_ratio_noise.py` pins it.
**34 checks, all green. The whole `scripts/tests/` suite is green.**

1. **`--runs N`.** Times each module N times. The verdict uses the mean.
2. **A discarded warm-up run, ON BY DEFAULT, `--no-warmup` to revert.** One
   per SERIES, not per module, because the penalty is a property of the
   series. The discarded time is PRINTED, never hidden.
3. **`INSTRUMENT_SPREAD = 0.128`**, with its provenance in the source. It is
   the BETWEEN-series figure, because a verdict is one series on one occasion.
4. **Every row prints its run count and spread**, which is the orchestrator's
   option 1, and carries a `NOISE` tag when the band crosses the bar.
5. **The band is the LARGER of the row's own spread and the measured floor.**
   A series cannot see its own displacement: five series each spreading 0.6 to
   4.0 percent landed 12.8 percent apart. Using the within-series figure alone
   prints a confident band around a displaced mean.
6. **The aggregate gets its own spread**, measured by pairing the i-th run of
   every module, which is `[LJ-1.135]`'s method.

**The exit code is UNCHANGED in every case, and a test pins it in both
directions.** DD24's threshold and tolerance are the owner's. A `NOISE` tag is
information and never a ruling.

### Why I overruled the brief's three options

- **"Report the run count and the spread"** (the orchestrator's lean). Kept,
  but insufficient alone: a single run has NO spread, so the honest report is
  "unknown", and the row stays biased.
- **"Refuse a verdict within the noise band."** Refused. Withholding a verdict
  changes what the gate does, and DD24 is the owner's. The tag says the same
  thing and rules nothing.
- **"Require N runs."** Refused as the primary cure. It prices the wrong term:
  it is expensive and it does not remove a bias.

### The honest limit

- **The 12.8 percent is a LOWER bound.** One module, one machine, one day. The
  first value I set, 9.3 percent from five series, was broken by the sixth
  series within the hour. It may be broken again.
- **The BASELINE's own spread is not in the band.** `[LJ-1.135]` measured 5.5
  percent over four runs of the whole AC set. A row this tool calls solid may
  still be fragile once the bar's noise is counted. The tool says so at
  `scripts/check-ratio.py:176-187`.
- **The warm-up changes printed numbers**, downward, most on small modules.
  That is a correctness fix and not a threshold change, but a reader comparing
  against a figure recorded before today must know which instrument produced
  it.
- **I did not re-measure the baseline**, per the brief. `ac_baseline_module_rate
  = 0.011828` stands. **But it was measured WITHOUT a warm-up**, so it carries
  one penalty over 79 masters, about 0.3 percent. That is small and it is in
  the LENIENT direction. **Re-running `--recalibrate` with the warm-up would
  make both sides exact; it is an owner's call and I did not take it.**
- **The mechanism of the 0.9 s is not identified.** MEASURED that it exists,
  that it is per-series, that it is roughly fixed, and that it decays with
  idleness. **INFERRED, and only INFERRED: it looks like page-cache or dynamic
  loader cost on the Agda binary and the dependency interfaces.** I did not
  profile it, and nothing in the finding rests on the cause.

## 5. THE MACHINE, and every load I sampled

`agents/tasks/LJ-1-148/load-samples.txt`, 112 samples at 10-second intervals,
19:10:10 to 19:28:46. Load min 2.61, max 8.21, mean 4.29, median 4.21, on 16
logical cores and 12 performance cores.

**A sibling WAS running Agda and I did not measure through it.** MEASURED:
`agda src/L/Condensation.lagda.md`, two runs, **19:11:00 to 19:15:11**, load
3.72 to 8.21 with the peak of 8.21 at 19:13:11 as the second run started.
`check-ratio.py` refuses beside a live Agda process
(`scripts/check-ratio.py:128-139`) and it would have refused me. **I did not
bypass the guard and I never used `--assume-quiet`.**

**I used the block to build the tool change, which needs no Agda.** The
machine cleared at 19:15:21 and my first measurement started at 19:16:19.

Load during my own runs:

| what | load |
|---|---|
| StageArith, 25 runs | 3.15 to 3.57 |
| StageArith, five series | 3.11 to 3.51 |
| BoundedSubset, 6 runs | 4.37 to 6.09 |

**MEASURED: no sibling Agda process appeared during any of my measurements.**
Competitors throughout were Bitcoin-Qt at about 33 percent, a `claude
bg-spare` at about 26, and WebKit renderers. **This is the machine's normal
working state, not a quiet one, and I say so rather than claim a clean bench.**
The between-series 12.8 percent is measured ON that state, which is the state
every DD24 verdict has ever been taken in.

**I did not have to invoke the abort criterion.** The window was real and the
measurements fit inside it.

## 6. MEASURED or INFERRED, every negative

| claim | which |
|---|---|
| The two runs used the SAME GHCRTS | **MEASURED**, from the source and from `git show` on each commit |
| `[LJ-1.144]`'s caliber explanation is wrong | **MEASURED**: no code path forks the caliber |
| `check-timing.py` ignores an exported GHCRTS | **MEASURED**, `scripts/check-timing.py:247` and `:332` |
| The first Agda of a series costs about 0.9 s more | **MEASURED**, three series, two modules |
| The penalty is per-SERIES, not per-module | **MEASURED**, two modules in one series, 79.0 against 2.0 percent |
| The penalty is fixed rather than proportional | **MEASURED** across a twentyfold size range |
| It decays with idleness | **MEASURED**, five back-to-back series against a 30-second gap |
| The baseline carries it once over 79 masters | **MEASURED** by construction: one `measure()` loop, one warm-up |
| Within-series repeatability is about 1 percent | **MEASURED**, 24-sample tail |
| Between-series is 12.8 percent | **MEASURED**, eight series over about 40 minutes. **A LOWER bound** |
| Three measured runs is enough | **MEASURED**, from the standard error table in section 3 |
| StageArith and BoundedSubset are solid UNDER | **MEASURED**, eight and two series |
| The orchestrator's 20.1 percent | **INFERRED by the orchestrator**, and now EXPLAINED: it is the first-run bias, not daily drift |
| The cause of the 0.9 s | **INFERRED and unproven.** Nothing in the finding rests on it |
| A warmed `--recalibrate` would tighten the bar by about 0.3 percent | **INFERRED** from the penalty size over 291 s. I did not run it |
| The machine was quiet during my runs | **MEASURED**, 112 samples, no sibling Agda after 19:15:11 |

## 7. ARCHIVE USED (DD18)

- `agents/tasks/LJ-1-135/lj-1.135-report.md`, read whole. Took: the protocol
  section `:156-190` for the instrument and the GHCRTS statement at `:184-186`;
  the control-run deviation at `:290-303`, which is where `[LJ-1.144]`'s error
  came from; the per-module table at `:335-349`; the four-run spread at `:214`
  and its load table at `:233-245`. Its "is the machine too noisy" paragraph at
  `:257-267` is the model for section 5 here.
- `agents/tasks/LJ-1-144/lj-1.144-report.md:307-321`, the caliber claim, which
  this report refutes.
- `dev/ledger.toml:2513-2712`, the whole `[ratio]` block. Took
  `ac_baseline_ghcrts` at `:2632`, `ac_baseline_module_rate` at `:2712`,
  `tolerance` at `:2974`, `gch_wing` at `:3019-3043`, and the 11.2 percent
  control at `:2540-2545`.
- `dev/PLAN.md:182`, DD24 in full.
- `dev/LESSONS.md`: **C-28**, a threshold outliving its tree, which is the
  family this belongs to and the reason the tool must not rule; **C-32**, a
  cure invalidating downstream measurements, which is why the warm-up change
  is flagged as changing printed numbers; **P-s**, a slice rate not
  extrapolating, whose logic I reused to refuse seeding the band from a SUM's
  spread; **P-q**, **P-m**, **P-t**, on rate as a content-class certificate,
  which is what the first-run bias was corrupting; **P-l**, a comparable is a
  hypothesis and not a price; **C-12**, one Agda process, obeyed throughout;
  **C-22**, incremental deliverable, obeyed.
- `agents/tasks/archive/LJ-1-128/` **does not exist.** The 11.2 percent
  control survives in `dev/ledger.toml:2540-2545` and I read it there. The
  brief's ARCHIVE section names a path that is not in the tree.

## 8. LITERATURE (DD18)

Nothing in the literature governs measurement noise.

## 9. FILES

| file | what |
|---|---|
| `scripts/check-ratio.py` | the change |
| `scripts/tests/test_ratio_noise.py` | 34 checks, new |
| `agents/tasks/LJ-1-148/probe-noise.py` | the probe, tracked, not deleted |
| `agents/tasks/LJ-1-148/boundedsubset-series.txt` | the six-run series |
| `agents/tasks/LJ-1-148/load-samples.txt` | 112 load samples |

**Nothing under `src/` was touched. Nothing was committed or pushed.**
`dev/ledger.toml` was NOT edited: the measured band lives in
`scripts/check-ratio.py` beside `check-timing.py`'s `REGRESSION_FACTOR`, which
is the precedent for a tolerance constant in a script. **If the owner prefers
it in the ledger, that is a one-line move and a `cfg.get`.**
