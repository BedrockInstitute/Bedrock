# [LJ-1.135] Re-measure `ac_baseline_module_rate`

Status: DONE. `ledger.py --check` is clean.

## 1. Headline

| term | old, 2026-08-11 | new, 2026-08-13 |
|---|---|---|
| `ac_baseline_module_rate` | 0.011057 | **0.014367** |
| `ac_baseline_module_lines` | 17,081 | **20,286** |
| seconds | 188.86 | **291.44**, mean of 4 |
| masters | 74 | **79** |

**Spread: 16.14 s over four runs, 300.28 to 284.14, which is 5.5 percent of
the mean.** Every run exited 0. I discarded nothing.

The rise is plus 29.9 percent, and **it is the opposite sign to what the brief
expected.** The brief said a wing module reads about 11 percent WORSE than it
is. It reads about 30 percent BETTER after this change, because the bar moves
with the baseline: 0.012716 s per line before, 0.016522 after, at DD24's 1.15
tolerance.

**Three findings the brief could not know, in the order that matters.**

1. **A control splits the rise.** The identical old tree, rebuilt today, costs
   6.9 percent more. The other 21.6 percent is content. Section 5.
2. **The content half is not the AC side getting worse.** Cone against cone,
   today against today, the AC side gained 179 lines and cost about the same
   seconds, 197.45 against 200.73. Section 5.
3. **The target set has drifted off the AC side.** 3,101 lines, 15.3 percent
   of the new denominator, sit outside the trophy cone and cost 32.3 percent
   of the seconds. Three of the six masters are `L/Condensation/*Agree`, and
   `src/L/Condensation.lagda.md` is IN the wing this baseline judges.
   Section 2 and section 6.

I wrote the figure the tool produces, because that is the figure the tool will
compare against, and a paper adjustment is what these guards exist to refuse.
**Finding 3 is an owner ruling and I did not take it.**

## 2. What the figure IS, and why it went stale twice over

`ac_baseline_module_rate` is the SECOND caliber in `dev/ledger.toml` `[ratio]`.
It is not a second opinion on `ac_baseline_seconds_per_line`.

- `ac_baseline_seconds_per_line` is a WHOLE-CONE rate: ONE cold build of
  `src/Landmarks.lagda.md`, its seconds spread over every line that build
  compiles (`dev/ledger.toml:2606`, `scripts/ledger.py:271-288`).
- `ac_baseline_module_rate` is a SUM OF SLICES: every AC master timed
  separately, each one cold with its dependencies warm
  (`scripts/check-ratio.py:159-200`, `recalibrate`).

`check-ratio.py` PREFERS the module rate for every verdict
(`scripts/check-ratio.py:294-296`: `judged = module_rate or baseline`). The
whole-cone rate is only the fallback, and the tool prints "NOT the caliber
these rows are measured at" when it has to use it
(`scripts/check-ratio.py:298-299`). So the module rate IS the DD24 bar in
practice.

The target set is DEFINED by the tool, not by the ledger:
`targets = [f for f in ledger_mod.countable_masters() if f not in wing]`
(`scripts/check-ratio.py:176-177`). `countable_masters()` is every tracked
`.lagda.md` under `src/` except the two catalogs (`scripts/ledger.py:92`,
`scripts/ledger.py:108-110`). `wing` is `ratio.gch_wing`
(`dev/ledger.toml:2952-2959`, 6 masters).

**MEASURED: that set is 79 masters and 20,286 in-fence lines today.** The
figure on record was taken over 73 masters and 17,081 lines. So "73 separate
builds" is the OLD count. Today it is 79.

### The provenance on record is wrong about its own date

The comment block above the figure says it was "measured 2026-08-10 by
`check-ratio.py --recalibrate`. 0.011472 s per line over 16,897 lines and
193.85 s, across 73 AC masters" (`dev/ledger.toml:2628-2650`). The figure
below that block is 0.011057 over 17,081 lines. The two do not match, because
**the block was never updated when the figure was replaced.**

MEASURED from git: `ac_baseline_module_rate` has three commits
(`git log -G ac_baseline_module_rate -- dev/ledger.toml`):

| commit | date | rate | lines | seconds |
|---|---|---|---|---|
| 096d49a `[LJ-0.5]` | 2026-08-10 | 0.011472 | 16,897 | 193.85 |
| f48ffd7 `[LJ-1.5]` | 2026-08-11 01:14 | **0.011057** | **17,081** | 188.86 |
| 21446f2 `[LJ-1.128]` | 2026-08-13 | unchanged | unchanged | prose only |

f48ffd7's own commit body carries the table: `module 0.011472 / 16,897 ->
0.011057 / 17,081  188.86 s`.

**So the live figure is from 2026-08-11, not 2026-08-10.** Two places say
otherwise: the comment block at `dev/ledger.toml:2628`, and `[LJ-1.128]`'s
note at `dev/ledger.toml:2805-2811` ("was taken 2026-08-10"). The brief
inherited the error from them.

The correction does not weaken the brief's case, it strengthens it.
2026-08-11 is the same day as the superseded whole-cone figure 0.007847, and
`[LJ-1.128]`'s control measured that day's machine as 11.2 percent faster than
today's. The machine-drift claim therefore applies to the module rate at full
strength.

### The target set is defined by SUBTRACTION, and it has drifted off the AC side

This is the finding I did not expect and it changes how the figure should be
read.

The two baselines pick their masters by opposite methods.

- The whole-cone denominator is built by CONSTRUCTION: the import closure of
  `src/Landmarks.lagda.md` (`scripts/ledger.py:271-284`). `[LJ-0.5]` made that
  change on 2026-08-10 and the ledger records why: "WHY NOT standing MINUS
  wing, which is what this used to compute" (`dev/ledger.toml:2596-2605`).
- The module-rate target set is still built by SUBTRACTION: every countable
  master that is not in `ratio.gch_wing` (`scripts/check-ratio.py:176-177`).
  **The module rate never got `[LJ-0.5]`'s fix.**

MEASURED today with `ledger.py`'s own graph functions:

| set | masters | lines |
|---|---|---|
| Landmarks cone, counted | 73 | 17,185 |
| module-rate targets | 79 | 20,286 |
| targets OUTSIDE the cone | 6 | **3,101** |

The six, with every master that imports them:

| lines | master | imported by |
|---|---|---|
| 1,409 | `src/L/BoundedSubset.lagda.md` | Everything only |
| 775 | `src/L/Ordinal/SquareLaw.lagda.md` | Everything only |
| 309 | `src/L/Condensation/TwelveAgree.lagda.md` | Everything only |
| 268 | `src/L/Condensation/UpperAgree.lagda.md` | Everything, TwelveAgree |
| 265 | `src/L/Condensation/LowerAgree.lagda.md` | Everything, TwelveAgree |
| 75 | `src/L/Ordinal/StageArith.lagda.md` | Everything only |

**Every one of them is reachable only through the catalog.** No trophy
statement depends on any of them, because `Landmarks` states both trophies and
its closure does not contain them. Five of the six are this phase's own work.

So 3,101 lines, **15.3 percent of the denominator**, are neither AC-cone
content nor declared wing. The subtraction sweeps them into a figure named
"the AC baseline", and `check-ratio.py` then judges wing modules against it.
Section 5 measures what they cost, so the owner can see the size of the bias
rather than argue about its direction.

### Nothing guards this pair

`validate_ratio_baseline` guards `ac_baseline_seconds_per_line` against
`ac_baseline_lines` only (`scripts/ledger.py:240-243` returns early unless
BOTH of those two exist, and `scripts/ledger.py:289-299` compares the cone).
**MEASURED: no code reads `ac_baseline_module_lines` at all.** The only hits
are the ledger row itself and the line where `--recalibrate` PRINTS it for a
human to paste (`scripts/check-ratio.py:198`). So the module pair has no
staleness guard, which is why it drifted 3,205 lines and 5 masters without
anything going red. See section 8.

## 3. Protocol

### Did I need all of them?

**Yes, and they are affordable. I did not sample.**

The figure is DEFINED as the sum over the whole target set
(`scripts/check-ratio.py:180-190`): every non-wing countable master, timed
cold with warm dependencies, summed, divided by the summed lines. A sample
would produce a number the tool itself can never reproduce, and
`--recalibrate` has no sampling mode to make one comparable.

The price is small, and the brief's "73 separate builds" reads as more than it
is. The record says 188.86 s of Agda for the old set (f48ffd7 commit body),
which is under four minutes. MEASURED today: one run is about five minutes.
Four runs plus two control runs plus one attribution run cost about 40 minutes
of machine time and bought an exact figure, a spread, and the decomposition in
section 5. A sample would have saved minutes and cost the definition.

MEASURED, and it corrects the brief: **the old set was 74 masters, not 73.**
74 masters at 17,081 lines is what f48ffd7's own tool reports, and 17,081 is
the number in the ledger row. The "73" belongs to the superseded 2026-08-10
figure.

### The instrument

- Tool: `.venv/bin/python scripts/check-ratio.py --recalibrate`. It writes
  nothing (`scripts/check-ratio.py:171-173`).
- `GHCRTS="-A64m -I0 -M8g"`, read by the tool from
  `ratio.ac_baseline_ghcrts` (`dev/ledger.toml:2626`) and passed to every
  child. C-12's cap is 8 GB and I never raised it.
- ONE Agda process at a time. `recalibrate` times its modules serially, and I
  ran one recalibrate at a time. `pgrep -x agda` exits 1 before each run, so
  the tool's own C-12 guard passed and I never used `--assume-quiet`.
- Each module is COLD by construction: `time_module` moves the module's own
  `.agdai` aside, runs `agda`, and restores it
  (`scripts/check-timing.py:242-268`). Dependencies stay warm.
- MEASURED before run 1: the tree is fully warm. Every one of the 79 targets
  has an interface under `_build/2.8.0/agda`; 300 interfaces on disk.
- Tree: HEAD `8f55b4b`, and `git status --porcelain -- src/` is EMPTY. So the
  working tree and HEAD agree on `src/`, and the lines the tool counts from
  the working tree (`scripts/check-ratio.py:150`) are HEAD's lines. MEASURED
  both ways: 20,286 and 20,286.
- `/usr/bin/time -l` wraps each whole run. Max RSS covers the children, and
  MEASURED: the instruction and cycle counters do NOT. See the last paragraph
  of section 4.

## 4. The runs

Current tree, HEAD `8f55b4b`, 79 masters, 20,286 in-fence lines.

| run | started | wall s | Agda sum s | rate | max RSS | exit |
|---|---|---|---|---|---|---|
| 1 | 13:55:53 | 300.44 | 300.28 | 0.014803 | 2.33 GiB | 0 |
| 2 | 14:01:34 | 286.43 | 286.26 | 0.014111 | 2.33 GiB | 0 |
| 3 | 14:06:52 | 295.25 | 295.08 | 0.014546 | 2.33 GiB | 0 |
| 4 | 14:24:37 | 284.34 | 284.14 | 0.014007 | 2.33 GiB | 0 |

**Mean 291.44 s. Spread 16.14 s, which is 5.5 percent of the mean.**
Rate at the mean: **0.014367**.

Run 4 brackets the two control runs, so the control sits inside the main
series in time and not after it. MEASURED: run 4 is the cheapest of the four
and the load was lowest then, so the series has no upward trend that would
make the mean an artifact of ordering.

TREE STABILITY, checked rather than assumed. HEAD moved from `8f55b4b` to
`bd64fba` during run 4, because the orchestrator committed. MEASURED:
`git diff 8f55b4b bd64fba -- src/` is EMPTY and `dev/ledger.toml` is untouched
by those two commits, so all four runs measured identical content. The tool
also printed 20,286 lines on every run.

I discarded nothing. All four runs are in the mean, per DD8 and per
`[LJ-0.5]`'s protocol note: run 1 is the slowest in this series as well, and
dropping it would define the bar as page-cache-warm and bias it LOW, which is
the wrong direction for a gate.

Load beside each run, from `uptime` and `ps -Ao pcpu,comm -r`:

| run | before | during | after | biggest competitors during |
|---|---|---|---|---|
| 1 | 3.49 | 6.05 | 5.58 | `/usr/bin/log` 98.4 percent, pCloud 48.7, Bitcoin-Qt 27.2 |
| 2 | 5.82 | 5.46 | 7.39 | Bitcoin-Qt 25.7, WindowServer 14.9, tor 5.5 |
| 3 | 6.62 | 5.49 | 4.84 | pCloud 57.0, `logd` 29.7, `log` 15.7 |
| 4 | 4.37 | 5.29 | 3.62 | Bitcoin-Qt 84.6, Warp 12.5 |
| control 1 | 4.06 | 2.78 | 4.34 | pCloud 44.7, Bitcoin-Qt 8.2 |
| control 2 | 4.29 | 3.77 | 4.41 | not sampled beyond `uptime` |
| six-module | 4.44 | -- | 4.13 | not sampled beyond `uptime` |

Dispatch-time load was 9.27 / 7.67 / 12.81. MEASURED at my first sample,
13:53: 6.65 / 7.21 / 12.40. **The machine got quieter while I worked**, and
the one-minute average fell from about 6.6 to about 4.0 by the last run.

MEASURED: the machine is NOT quiet and it is NOT saturated. Sixteen cores are
present, Agda uses about one, and the competitors take about two to three
more. MEASURED: I saw no `siriactionsd` process in any of my nineteen samples,
so the runaway `[LJ-1.134]` reported is gone. INFERRED, and only INFERRED: run
1 met the worst competition and is the slowest of the four, which is
consistent with contention but is NOT proof of cause.

**Is the machine too noisy for this figure to mean anything? MEASURED: no,
and the spreads are what settle it.** The main series spreads 5.5 percent over
four runs and the control spreads 0.7 percent over two. Both are small enough
to resolve a 29.9 percent effect and a 6.9 percent one. **I would not report a
2 percent effect from this machine today, and I do not.** Where a difference
falls inside a spread I say so: the cone-against-cone comparison in section 5
is the one place that happens, and it is marked.

CAVEAT on the `%CPU` column, stated because it would otherwise mislead: `ps`
reports a process's average over its whole life, and `recalibrate` starts a
new short-lived Agda every few seconds. So the Agda row reads 98.3 percent in
one sample and 35.2 in another without the load changing. The `uptime` figures
are the reliable ones.

MEASURED: peak resident set size 2.33 GiB, the maximum over all 79 child
processes. INFERRED: GHC turns on compacting collection above 30 percent of
the maximum heap, which is 2.4 GiB at `-M8g` and 4.8 GiB at the `-M16g` the
old figure was taken at. 2.33 GiB is under both, so the cap binds in neither
run and the two caps are one instrument here. The margin is 3 percent, which
is much thinner than the whole-cone measurement's (`[LJ-1.128]` measured
1.18 GiB there).

MEASURED and DISCARDED as unusable: `/usr/bin/time -l` reported 1.4009e9
instructions retired and 6.88e8 cycles for run 1. At 4 GHz that is 0.35 s of
work against a 300 s run, so these counters cover the Python parent only and
not the 79 Agda children. `[LJ-1.128]` could use the counters because it timed
ONE Agda process directly. I cannot, so this measurement has no
instructions-per-cycle evidence and I do not claim any.

## 5. The control, and what the rise actually is

**I ran the control.** `[LJ-1.128]` did the same thing and its finding is why
this section exists: a figure without a control cannot separate machine drift
from content drift.

METHOD. `git worktree add /tmp/lj1135/old-f48ffd7 f48ffd7`, which is the exact
tree the 0.011057 was measured on. I cold-built it once
(`agda src/Everything.lagda.md`, 176.96 s, exit 0, 82 interfaces) so its
dependencies were warm, then ran **that worktree's own `check-ratio.py`**, so
the instrument is the old one too. The current tree was never touched: a
worktree is a separate directory with its own `_build`.

ONE DEVIATION, and I made it deliberately. The old worktree's ledger declared
`ac_baseline_ghcrts = "-A64m -I0 -M16g"`, and C-12 caps me at 8 GB. I edited
that one line in the WORKTREE only, to `-M8g`, so the control ran at the same
cap as the main runs. MEASURED: peak resident set size 1.15 GiB in the
control. INFERRED: that is below 30 percent of the maximum heap at both caps,
so compaction never engages and the two caps are one instrument on this tree.
`[LJ-1.128]` reached the same conclusion by the same evidence.

### The control result

| tree | masters | lines | seconds | rate |
|---|---|---|---|---|
| f48ffd7, recorded 2026-08-11 | 74 | 17,081 | 188.86 | 0.011057 |
| f48ffd7, MEASURED today | 74 | 17,081 | **201.14 / 202.48**, mean 201.81 | 0.011815 |

Spread 1.34 s, which is 0.7 percent. **The identical tree, on the identical
instrument, costs 6.9 percent more today.**

That figure is MEASURED and it is NOT the 11.2 percent `[LJ-1.128]` measured
on the whole-cone instrument. The two are different instruments on different
days, so I report mine and do not reconcile them. Both say the same thing
about direction.

### The decomposition

| step | rate | change |
|---|---|---|
| recorded 2026-08-11 | 0.011057 | -- |
| same tree, today (control) | 0.011815 | **plus 6.9 percent, the MACHINE** |
| today's tree, today | 0.014367 | **plus 21.6 percent, the CONTENT** |

Total plus 29.9 percent. The two factors multiply: 1.0685 times 1.216 is
1.2993, which is the whole of the rise and nothing is left over.

### The content half is six masters, and they are not the AC side

Section 2 found six targets outside the Landmarks cone. I measured them, with
`check-ratio.py --module`, cold with warm dependencies, at the same GHCRTS:

| rate | lines | seconds | master |
|---|---|---|---|
| 0.0121 | 1,409 | 17.00 | `src/L/BoundedSubset.lagda.md` |
| 0.0111 | 775 | 8.59 | `src/L/Ordinal/SquareLaw.lagda.md` |
| **0.0993** | 309 | 30.68 | `src/L/Condensation/TwelveAgree.lagda.md` |
| **0.0899** | 265 | 23.82 | `src/L/Condensation/LowerAgree.lagda.md` |
| **0.0478** | 268 | 12.81 | `src/L/Condensation/UpperAgree.lagda.md` |
| 0.0144 | 75 | 1.08 | `src/L/Ordinal/StageArith.lagda.md` |
| **0.0303** | **3,101** | **93.99** | aggregate |

**They are 15.3 percent of the lines and 32.3 percent of the seconds.** Their
aggregate rate is 2.74 times the old baseline. The three `Condensation/*Agree`
masters carry it: 842 lines cost 67.31 s.

Subtract them and the remainder is exactly the Landmarks cone, 73 masters and
17,185 lines:

| set | seconds | lines | rate |
|---|---|---|---|
| all 79 targets | 291.44 | 20,286 | 0.014367 |
| the six outside the cone | 93.99 | 3,101 | 0.030309 |
| **the cone alone** | **197.45** | **17,185** | **0.011490** |

Now compare the cone against the control's cone. The control set is the cone
plus `StageArith`, which is byte-identical between the two trees (MEASURED: of
the masters present in both, only `L/Coding/EnvSet` and `L/Coding/Sound`
changed, by plus 130 and plus 49 lines). So the control's cone is about
201.81 minus 1.08, which is 200.73 s over 17,006 lines, a rate of 0.011803.

**MEASURED: cone against cone, today against today, the tree gained 179 lines
and cost slightly FEWER seconds, 197.45 against 200.73.** The AC side has not
become more expensive. P-q again, in the good direction, and it repeats
`[LJ-1.128]`'s reading of the same 179 lines.

CAVEAT, so nobody over-reads that pair. Both cone figures are INFERRED by
subtraction from two measurements taken in separate runs, and the run-to-run
spread on the whole set is 16 s. The 3.28 s gap sits inside that spread, so it
supports "about the same" and it does NOT support "cheaper".

**So the plus 21.6 percent of "content" is not the AC side getting worse. It
is 3,101 lines of phase-LJ-1 work that no trophy statement imports, entering a
figure named "the AC baseline" through a subtraction.**

## 6. What this does to the bar, and the one thing the owner must rule

`check-ratio.py` computes `bar = judged * tolerance`
(`scripts/check-ratio.py:294-297`), and `tolerance` is 1.15.

| | rate | DD24 bar |
|---|---|---|
| before | 0.011057 | 0.012716 |
| after | 0.014367 | **0.016522** |

**The bar gets 29.9 percent looser.** The brief expected the correction to
help a wing module that was being judged too harshly. It does, and it goes
further than that, so the direction has to be said plainly.

**A quarter of the loosening is content that the wing should not be judged
against.** Three of the six out-of-cone masters are
`src/L/Condensation/{Twelve,Upper,Lower}Agree.lagda.md`, at 0.0993, 0.0478 and
0.0899 s per line, and **`src/L/Condensation.lagda.md` is a declared wing
master** (`dev/ledger.toml:2993`). So this phase's own Condensation work now
sits on BOTH sides of the comparison: inside the wing that DD24 judges, and
inside the baseline DD24 judges it against. A bar that rises when the wing's
neighbours get expensive is not measuring the wing.

MEASURED, so the size of the choice is visible:

| baseline the owner could rule for | rate | bar |
|---|---|---|
| the tool as written, all 79 targets | 0.014367 | 0.016522 |
| the Landmarks cone only, 73 masters | about 0.011490 | about 0.013214 |

**I wrote the first one.** It is what `--recalibrate` measured and what
`check-ratio.py` will compare against tomorrow, and writing anything else
would put a number in the ledger that the instrument does not produce. The
second is an INFERRED figure from two runs, not a measurement of its own.

THE RULING I AM ASKING FOR, in one sentence: should `--recalibrate` select its
masters by the Landmarks cone, the way `[LJ-0.5]` already fixed the whole-cone
denominator (`scripts/ledger.py:271-284`), instead of by subtracting the
declared wing? A second, cheaper answer exists: declare the three `*Agree`
masters in `ratio.gch_wing`, where the other Condensation work already sits.
**Both are rulings, so I took neither.**

## 7. The ledger diff and `ledger.py --check`

TWO NUMBERS, ONE EDIT. `ac_baseline_module_rate` and
`ac_baseline_module_lines` change together, in one hunk, as `[LJ-1.5]` and
`[LJ-1.128]` both did. Nothing else in the file changes value.

```
-ac_baseline_module_rate = 0.011057
-ac_baseline_module_lines = 17081
+ac_baseline_module_rate = 0.014367
+ac_baseline_module_lines = 20286
```

The rest of the diff is provenance, and every part of it is required:

1. The comment block above the pair described the SUPERSEDED 2026-08-10
   measurement, not the figure underneath it. Rewritten with today's runs, the
   control, the decomposition and the out-of-cone finding.
2. The `[LJ-1.128]` paragraph inside `ac_baseline_provenance` said the module
   rate was "STALE ... and was NOT re-measured". It is re-measured now. That
   paragraph also carried three factual errors and the new text names them:
   the date (2026-08-10, actually 2026-08-11), the count (73 builds, actually
   74), and the direction word ("BELOW", while the row is above it).
3. The `1.45x` slice-against-cone figure was measured when both sides covered
   one set of masters. They no longer do, so the text now gives a
   set-consistent replacement, 1.31x, and marks it as arithmetic on two
   measurements.

MEASURED, both gates, after the edit:

```
$ .venv/bin/python scripts/ledger.py --check
ledger [thresholds SUSPENDED]: AC closure 19,993 against the retired 20,000 cap,
  reported and NOT enforced; re-arm is LJ-2.1 ...
ledger: declaration clean; standing 28,617 lines measured over 85 masters
EXIT 0

$ .venv/bin/python scripts/lint-prose.py dev/ledger.toml agents/reports/lj-1.135-report.md
EXIT 0
```

I did NOT run `make check`. The orchestrator runs it.

## 8. What I did not do, and one thing I recommend

**I did not change DD24's policy.** The threshold, the tolerance and the
question of whether a loaded baseline may stand are the owner's. I replaced a
measurement with a measurement.

**I did not touch `src/`.** No file under `src/` is modified by me. I did not
commit, push, checkout, stash, reset or clean.

**I did not edit `dev/PLAN.md` or `dev/JOURNAL.md`.** Both places are the
orchestrator's:

1. `dev/JOURNAL.md:275-277` records this figure as owed by `[LJ-0.5]`, which
   was true when written and is now discharged twice over.
2. `dev/PLAN.md:615` carries the `LJ-1.135` row and its 200-character summary
   says the figure reads "about 11 percent WORSE". MEASURED: 29.9 percent, and
   the sign of the correction is that the bar gets LOOSER. The row needs the
   number and the direction.

Inside `dev/ledger.toml` I fixed both stale places myself, at
`dev/ledger.toml:2628` and `dev/ledger.toml:2839`, in the same edit as the
figure.

**I cleaned up.** The control worktree at `/tmp/lj1135/old-f48ffd7` is removed
and `git worktree list` shows only the main tree. Nothing of mine remains
under `_build`: `recalibrate` restores every interface it moves aside
(`scripts/check-timing.py:259-268`), and MEASURED after my last run, the
project interface store holds the same 300 interfaces it held before I
started.

**RECOMMENDED, not implemented: a staleness guard on the module pair.**
`validate_ratio_baseline` guards the whole-cone pair only
(`scripts/ledger.py:240-243`). The module pair drifted by 3,205 lines and six
masters and nothing went red. A guard of the same shape would catch it.

I did NOT write one, for a reason that is a ruling and not a preference. The
whole-cone guard has a 50-line tolerance (`dev/ledger.toml:2778`) because a
real compression is hundreds of lines. This phase adds hundreds of lines per
week to the module set, so the same tolerance would turn `make check` red
every few days and force a 79-build re-measurement each time. **How often the
project can afford to re-measure this figure is a cost ruling, so it is the
owner's.** I report the gap and leave the number to the ruling.

## 9. Every negative in this report, marked

| negative | class |
|---|---|
| The AC side did NOT get more expensive per line | MEASURED, cone against cone, and the gap sits inside the spread |
| The rise is NOT mostly the machine | MEASURED by control: the machine is 6.9 of the 29.9 percent |
| The old figure was NOT taken on 2026-08-10 | MEASURED from git: f48ffd7, 2026-08-11 |
| The old set was NOT 73 masters | MEASURED: 74, at 17,081 lines |
| Six targets are NOT reachable from either trophy | MEASURED on the import graph: only `Everything` imports them |
| Nothing guards the module pair | MEASURED: no code reads `ac_baseline_module_lines` |
| The heap cap does NOT bind, at either 8g or 16g | INFERRED from a MEASURED 2.33 GiB peak and GHC's 30 percent rule |
| The machine is NOT too noisy to report this | MEASURED: spreads of 5.5 and 0.7 percent against effects of 29.9 and 6.9 |
| No `siriactionsd` runaway is present | MEASURED: absent from all nineteen `ps` samples |
| The instruction counters do NOT cover the Agda children | MEASURED: 1.4e9 instructions for a 300 s run |
| `src/` did NOT change during the four runs | MEASURED: `git diff 8f55b4b bd64fba -- src/` is empty |
| Run ordering did NOT bias the mean upward | MEASURED: the last run is the cheapest |
| I did NOT discard a run | statement of protocol |

## ARCHIVE USED

I surveyed the four archives and took NOTHING from them. This task measures
the live tree with a live tool, so the archived route's records cannot bear on
it.

- `archive/dev/DECISIONS-archived.md`: checked that no `D`-series ruling
  governs the ratio baseline. DD24 is the live ruling and it is in
  `dev/PLAN.md` section 3.
- `archive/dev/TASKS-archived.md`, `archive/dev/JOURNAL-archived.md`,
  `archive/dev/STATUS-archived.md`: not read. The figure I re-measure was
  first taken on 2026-08-10, after the archives closed on 2026-08-09.
- `archive/`: not read. No archived module enters `countable_masters()`, which
  reads git-tracked masters under `src/` only (`scripts/ledger.py:95-110`).

The live evidence I used instead:

- `dev/LESSONS.md` C-12 (heap cap), C-26 (a duplicated rule drifts), C-28 and
  C-32 (a threshold outliving its tree), P-m, P-q, P-s, P-t (rate as a
  content-class certificate).
- `agents/reports/lj-1.128-report.md`, for the control-run method and the
  machine-drift figure I test against.
