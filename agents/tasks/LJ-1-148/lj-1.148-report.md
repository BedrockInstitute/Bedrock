# LJ-1.148 report: the instrument's noise, measured

STATUS: IN PROGRESS. Written incrementally.

## 1. THE CALIBER VERDICT: SAME INSTRUMENT. MEASURED, from the source

**`[LJ-1.144]` is wrong and the orchestrator is right. The two runs used the
identical `GHCRTS`, and the code makes any other outcome impossible.**

### The code has exactly one source of GHCRTS, and no fork

`scripts/check-ratio.py` calls `measure()` at two places and NEITHER can
select a different caliber:

- `scripts/check-ratio.py:230` (the `--recalibrate` path):
  `ghcrts = cfg.get("ac_baseline_ghcrts")`, used at `:233`.
- `scripts/check-ratio.py:396-397` (the `--module` path AND the declared-wing
  path, which are the same code): `ghcrts=cfg.get("ac_baseline_ghcrts")`.

Both read ONE ledger key. `measure()` passes it to the timer at
`scripts/check-ratio.py:174`, and `scripts/check-timing.py:247` applies it:

    env = dict(os.environ, GHCRTS=ghcrts or "-M8g")

**So `--module` cannot run at a different caliber from `--recalibrate` inside
one ledger state. There is no code path that would let it.**

### The ledger value was the same for both runs

`dev/ledger.toml:2632` declares `ac_baseline_ghcrts = "-A64m -I0 -M8g"`.

MEASURED, by reading the value out of each commit:

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
is real, and it is about a caliber that neither run used.

`[LJ-1.135]`'s report DOES contain the string `-M16g`, at
`agents/tasks/LJ-1-135/lj-1.135-report.md:299`. It belongs to the CONTROL run
in the `f48ffd7` worktree, where `[LJ-1.135]` edited that one line down to
`-M8g` so the control matched. It does not belong to the per-module table at
`:335-349`, which is the table `[LJ-1.144]` was reading. **Two calibers are
named in that report and the wrong one was attached to the table.**

### A REAL caliber trap does exist, in the same code family, and nobody has hit it yet

MEASURED, from the source, and reported because it is one edit away from the
defect `[LJ-1.144]` described:

`scripts/check-timing.py:332` calls `time_module(path, cold=not args.warm)`
with NO `ghcrts`, so `scripts/check-timing.py:247` falls back to a bare
`-M8g`. And because that line is `dict(os.environ, GHCRTS=...)`, the keyword
OVERRIDES the environment. **So an agent that runs
`GHCRTS="-A64m -I0 -M8g" .venv/bin/python scripts/check-timing.py <master>`
gets a bare `-M8g` run, silently, whatever it exported.** That is deliberate
for `check-timing.py` (its `[[hot]]` rows were measured at the bare cap, and
`:236-245` says so), but the shell export is a no-op that reads like a
setting. It does NOT affect `check-ratio.py`, which passes its own value on
every path, so it does not touch the finding above.

## 2. THE FINDING: the noise is not a percentage, it is a FIXED first-run cost

**MEASURED. `src/L/Ordinal/StageArith.lagda.md`, 75 in-fence lines, 25 cold
runs in one series, quiet machine, load 3.15 to 3.57, one Agda process, at
`-A64m -I0 -M8g`.** Full series:
`agents/tasks/LJ-1-148/probe-noise.py`, output in section 3.

| | seconds | s/line | against the 0.0136 bar |
|---|---:|---:|---|
| run 1 | **1.811** | **0.02415** | **1.78x, OVER** |
| runs 2 to 25, mean | **0.787** | **0.01049** | **0.77x, UNDER** |
| all 25, mean | 0.828 | 0.01104 | 0.81x |

**The same module, the same tree, the same instrument, the same minute. Run 1
says OVER by 78 percent. Runs 2 to 25 say UNDER by 23 percent.**

The tail is TIGHT: 24 runs spread 5.2 percent, min 0.775, max 0.816. **So the
instrument is not generally noisy. It has one systematic defect and the rest
is quiet.**

### The penalty is PER-SERIES, not per-module. MEASURED

One invocation, two modules, three runs each
(`check-ratio.py --module ... --module ... --runs 3`):

| position in the series | module | spread |
|---|---|---:|
| first | `src/L/Ordinal/StageArith.lagda.md` | **79.0 percent** |
| second | `src/V/Presentation.lagda.md` | **2.0 percent** |

**Only the first Agda invocation of a series pays.** It repeats: a second
probe started 30 seconds after the first finished paid it again (1.700 s
against a tail mean of 0.864, 1.97x), so it is not a page cache that decays.

### It is a FIXED cost of about 0.9 s, not a multiplier, and that changes everything

| series | run 1 | tail mean | difference |
|---|---:|---:|---:|
| probe, n=25 | 1.811 | 0.787 | **+1.02 s** |
| probe, n=4 | 1.700 | 0.864 | **+0.84 s** |

**So the RELATIVE error is set by the module's size.** At about 0.9 s of fixed
penalty:

- a 0.8 s module is inflated by about **125 percent**;
- a 17 s module by about **5 percent**;
- a 30 s module by about **3 percent**.

**This is the mechanism behind the whole finding, and it is not day-to-day
machine drift.**

### THE CONSEQUENCE FOR DD24, and it is a systematic bias, not noise

**`check-ratio.py --module X` runs ONE module ONCE, so it always pays the
penalty in full. `--recalibrate` runs 73 to 79 modules in ONE series, so it
pays it ONCE across the whole set, which is about 0.3 percent of 291 s.**

**So the bar is measured almost penalty-free and each module is judged with the
penalty included.** That is unlike compared with unlike, in the same instrument
whose comments already record two earlier versions of that same defect
(`scripts/check-ratio.py:174-197` on the target set, `:479-526` on the two
rates). This one is not the flags and not the target set. **It is the position
in the series.**

**It is worst exactly where the brief said the verdicts are fragile: the small
modules.** `StageArith` is 75 lines.

## 3. THE SERIES, in full

TO FILL: the 25-run table and the BoundedSubset series.

## 4. HOW MANY RUNS A VERDICT NEEDS

TO FILL.

## 5. WHAT I CHANGED IN THE TOOL, and its honest limit

TO FILL.

## 6. THE MACHINE, and every load I sampled

TO FILL.

## 7. MEASURED or INFERRED, every negative

TO FILL.

## 8. ARCHIVE USED

TO FILL.

## 9. LITERATURE

Nothing in the literature governs measurement noise.
