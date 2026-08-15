# LJ-1.322 report: price all three cost mechanisms in four flag runs

STATUS: COMPLETE against the decision table's fourth branch. Written
incrementally (C-22). Every figure comes from the raw `.out` file named beside
it, never from an excerpt (C-53). Every negative is marked MEASURED or
INFERRED, in those words. ASD-STE100 applies.

## THE BRANCH THAT FIRED: ALL THREE MISS

**All three ranked mechanisms are REFUTED at this site.**

| branch | measured | verdict |
|---|---|---|
| B cuts the file's own Total by 30 s or more | **B makes it at least 13 times SLOWER**, 1,840.76 s and unfinished against a 140.57 s control | **MISS, and the sign is backwards** |
| B misses and A2 shows `Serialization` plus `Import` at 30 percent or more | **16.25 percent**, 22,412 ms of 137,963 ms | **MISS** |
| B and A2 miss and C cuts 30 s or more while staying green | **C is RED**, exit 42, one `UnequalTerms` error | **MISS. The arm is UNMEASURABLE, not a wall** |
| **all three miss** | | **THIS ONE FIRED** |

**Two of the three misses are not near misses.** Rank 1 runs the wrong way by
a factor of at least 13. Rank 3 does not typecheck. Rank 2 is the only one that
merely falls short, and it falls short by nearly half.

**The ruling's fallback needs correcting before it is funded.** It sends the
project back to "C-50 triage on A1's charged rows, which already name
`satGraphB`, `twelveB` and `closedBS`". **A1 is the first per-definition
profile this file has ever had, and it charges those three definitions 258 ms
of 137,453 ms, which is 0.19 percent.** A1 names a different account: the
thirty `Agree` modules, at 36,600 ms. See the section below.

**The `RowTies` gate FIRES at 36.60 s against its 15 s floor**, so a `RowTies`
PROBE is funded by the ruling's own action 6.

## THE MACHINE WAS NOT QUIET, so every seconds figure is INDICATIVE

The brief holds a run to a quiet machine, and the abort criterion orders me to
say so and to report the runs as INDICATIVE rather than measured. **The machine
is not quiet. MEASURED.**

| moment | agda slots | load averages | the other load |
|---|---|---|---|
| 00:12, session start | 0 | 6.40 6.50 6.43 | `mediaanalysisd` 80.8 percent |
| 00:16, before A1 | 0 | 6.69 6.62 6.48 | `mediaanalysisd` 87.4 percent, `pCloud` 48.6 percent, two `GF-Trader` helpers at 23.8 and 18.7 percent |
| 00:19, before A2 | 0 | 5.92 6.56 6.50 | `mediaanalysisd` 90.5 percent, `pCloud` 50.3 percent, the same two helpers |

Per-run load averages, before and after each run, are in the run table below
and in `agents/tasks/LJ-1-322/timings.csv`.

The agda slot count was 0 before every run (C-12's command, the brief's).
**No other agda process competed. MEASURED.** The competition is three
non-agda applications that the repository does not control.

**What the noise does to the verdict.** Every run in this task ran in one
session against the same background. The decision table compares B and C
against A1, so a common noise floor partly cancels in the DIFFERENCE. It does
not cancel in an absolute figure, so A1's re-measure of 132.28 s is the figure
most damaged by the noise.

## Run figures

Raw output is `agents/tasks/LJ-1-322/runs/<label>.out`. Wall seconds are
`agents/tasks/LJ-1-322/timings.csv`.

| run | what | wall (s) | exit | profile Total (ms) | Miscellaneous (ms) | Misc share | slots before | slots after | load before | load after |
|---|---|---|---|---|---|---|---|---|---|---|
| **A1** | master, `--profile=definitions` | 140.39 | 0 | **137,453** | **80,111** | **58.3 percent** | 0 | 0 | 6.66 6.62 6.48 | 6.85 6.82 6.58 |
| **A2** | master, `--profile=internal` | 139.73 | 0 | **137,963** | **55** | **0.04 percent** | 0 | 0 | 5.92 6.56 6.50 | 16.66 9.99 7.84 |
| **B1** | master, `--no-syntactic-equality --profile=definitions` | **1,840.43, WALL** | 130 | **NONE** | **NONE** | **NONE** | 0 | 0 | 10.99 9.31 7.68 | 7.97 7.39 7.43 |
| **cbn** | copy, `--no-syntactic-equality` in the pragma | **1,840.76, WALL** | 130 | **NONE** | **NONE** | **NONE** | 0 | 0 | 4.97 7.00 7.35 | 6.08 6.95 7.27 |
| **cbl** | copy, `--lossy-unification` in the pragma | 669.39, **RED** | 42 | **NONE** | **NONE** | **NONE** | 0 | 0 | 5.83 6.84 7.22 | 14.39 9.20 7.73 |
| cb0 | copy, no flags, the control | 140.57 | 0 | none asked | none asked | none asked | 0 | 0 | 9.49 8.17 7.74 | 5.27 7.15 7.41 |
| R0 | master, no flags, restore after B1 | 141.76 | 0 | none asked | none asked | none asked | 0 | 0 | 9.49 8.00 7.65 | 7.36 7.66 7.56 |
| r1 | master, no flags, final restore | 142.29 | 0 | none asked | none asked | none asked | 0 | 0 | 12.15 9.05 7.72 | 9.39 8.88 7.84 |

**B and C have NO Total and NO `Miscellaneous` share, and that is a
measurement rather than an omission. MEASURED.** Agda prints its profile when
a run completes. **B1 and cbn were interrupted at the wall and cbl exited on a
type error, so none of the three ever printed a profile.** Their raw files are
100 to 480 bytes and hold the `Checking` line and, for cbl, the error. **A
figure that does not exist is not reported here** (C-53's discipline read the
other way round: I did not build a share out of an absence).

**The slot count was 0 before every run. MEASURED, with the brief's own
command.** No agda process of mine ever overlapped another, and the sibling
task ran none.

### A1, the baseline and the same-day control

- Raw file: `agents/tasks/LJ-1-322/runs/a1.out:2-3` for Total and
  Miscellaneous.
- **Total 137,453 ms, Miscellaneous 80,111 ms, 58.3 percent.** The share sits
  inside the 54 to 61 percent band C-53 records.
- **Same-run charged control**, read from the raw file:
  `L.Condensation.SatGraphAgree.back 3,576ms` at `runs/a1.out:4`, and
  `L.Condensation.PropAgree.subB2T-back 3,275ms` at `:5`. The instrument
  charged rows in this run, so a not-charged row in it means something.
- **One `Checking` line only.** `grep -c '^Checking' runs/a1.out` returns 1.
  **The dependencies stayed warm and only `L.Condensation` was elaborated.
  MEASURED.**
- **341 named definition rows, summing to 57,171 ms, which is 41.6 percent of
  Total.** The smallest row is 10 ms, so the profiler truncates below 10 ms and
  every sum over named rows in this report is a LOWER BOUND.
- **The re-measure of 132.28 s.** A1 reads 137.45 s by the profiler and
  140.39 s by the wall clock. That is 3.9 percent and 6.1 percent above the
  quoted figure. INDICATIVE, not measured, because of the machine load above.

### A2, rank 2's test, and it MISSES its 30 percent threshold

- Raw file: `agents/tasks/LJ-1-322/runs/a2.out`, which is 29 lines and is
  quoted whole in this task's evidence. Total and Miscellaneous are at `:2-3`.
- **Total 137,963 ms, Miscellaneous 55 ms, 0.04 percent.** `--profile=internal`
  has almost no dark bucket, which is what `[LJ-1.320]` R6 predicted when it
  called this mode the activity-side attributor. **The same file reads 58.3
  percent dark under `--profile=definitions` and 0.04 percent dark under
  `--profile=internal`, in two runs 3 minutes apart. MEASURED.**
- **One `Checking` line only.** Dependencies stayed warm. MEASURED.

| account | raw row | ms | share of 137,963 ms |
|---|---|---|---|
| `Serialization` self | `runs/a2.out:9` | 22,383 | 16.22 percent |
| `Import` | `runs/a2.out:28` | 29 | 0.02 percent |
| **`Serialization` plus `Import`** | | **22,412** | **16.25 percent** |
| the same, taking `Serialization`'s inclusive 22,558 ms | | 22,587 | 16.37 percent |
| `Typing.CheckRHS` | `runs/a2.out:5` | 34,207 | 24.79 percent |
| `Typing` inclusive | `runs/a2.out:4` | 84,556 | 61.29 percent |
| `Typing.CheckLHS` | `runs/a2.out:6` | 30,989 | 22.46 percent |
| `Typing.OccursCheck` | `runs/a2.out:7` | 12,853 | 9.32 percent |
| `InterfaceInstantiateFull` | `runs/a2.out:12` | 12,112 | 8.78 percent |

**`Serialization` plus `Import` is 16.25 percent against a 30 percent
threshold. Rank 2's test MISSES. MEASURED.** It misses by a wide margin, not
by a hair: the account would have to nearly double to pass. Adding
`InterfaceInstantiateFull`, which the brief does not name, still reads 25.0
percent and still misses.

**The comparable on record does not transfer, and this is the P-l pattern
again.** `[LJ-1.281]` measured 90.7 s of 100.8 s inside `Typing.CheckRHS`,
which is 90 percent. This file reads 24.8 percent in the same account. **The
two files do not share a cost shape**, so no figure from `[LJ-1.281]` prices
anything here.

**What A2 explains about A1's dark bucket.** A1's 80,111 ms of Miscellaneous
is not lost work. A2 attributes the same 138 s run to activities, and the
largest are `Typing` inclusive at 84,556 ms, `Serialization` at 22,383 ms,
`InterfaceInstantiateFull` at 12,112 ms, `Positivity` at 5,818 ms and
`DeadCode.DeadCodeReachable` at 5,341 ms. **The definitions profile has no
per-definition owner for most of this work, which is why its Miscellaneous row
is the empty account. MEASURED against the pair of runs.**

### B, and the flag's interface cost is a finding of its own

**`--no-syntactic-equality` invalidates the WHOLE dependency closure, not just
the module. MEASURED.** A1 and A2 each printed ONE `Checking` line. The first
run under this flag printed a `Checking` line for the cubical library and for
every src master it reached.

`[LJ-1.317]:93-99` marked this CAUTION INFERRED, from the 2.8.0 options page
listing `--syntactic-equality` under "Options that affect interface file
reloading". **It is now MEASURED, and at a scale the caution did not state.**

**Be precise about what "invalidates" means here.** What I measured is that a
command-line run under the flag RE-ELABORATES the closure: it printed a
`Checking` line for modules that A1 and A2 read from cache. **I did not measure
that it overwrites the cached interfaces**, and run R0 later suggests it did
not, at least not across an interrupt. See "WHAT THIS TASK LEAVES BEHIND".

### B1 HIT THE 30 MINUTE WALL, and here is the bisect

**Run B1 was `GHCRTS="-A64m -I0 -M8g" agda --no-syntactic-equality
--profile=definitions src/L/Condensation.lagda.md`. It did not finish.**

| fact | value |
|---|---|
| **elapsed seconds at the interrupt** | **1,840.43 s, which is 30 minutes 40 seconds** |
| exit code | 130, the interrupt |
| agda slots before and after | 0 and 0 |
| load averages before and after | 10.99 9.31 7.68, then 7.97 7.39 7.43 |
| resident memory at the interrupt | 2.35 GB, against an 8 GB cap. **The cap was never raised and heap was never the limit. MEASURED** |
| modules elaborated, in the raw file | **83: 77 cubical library modules and 6 src masters** |
| the last module it reached | `FOL.ZFStructure`, one of `L.Condensation`'s direct imports |

**The raw file undercounts and I say so.** `runs/b1.out` stopped growing at
10,758 bytes 30 minutes before the interrupt, so agda's stdout was block
buffered and the unflushed tail is lost. **83 is what the raw file proves. The
true count is higher by an unknown amount, at most about 55 more lines by the
buffer's size. INFERRED.**

**What the wall proves and what it does not.** It proves that a command-line
`--no-syntactic-equality` cannot price this file in one run on this tree,
because the flag first re-elaborates the whole closure. **It does NOT measure
the flag's effect on `L.Condensation` itself, which is what the decision table
asks about.** So the wall protocol's third clause applies: bisect.

### The bisect: put the flag in the FILE, not on the command line

**The flag is neither infective nor coinfective** (2.8.0 options page, read by
`[LJ-1.317]:101-102`), **and it is also a pragma option** (`:100`). **So a flag
written into one file's own OPTIONS line applies to that file alone and leaves
every dependency interface valid.** That turns a whole-closure rebuild into one
module's elaboration, which is exactly the quantity the decision table names:
"B cuts the file's own Total".

The instrument is `agents/tasks/LJ-1-322/CondProbe.lagda.md`, which is
`src/L/Condensation.lagda.md` with ONE line changed, the module name.
**`diff` between the two returns 4 lines. MEASURED.** The driver is
`agents/tasks/LJ-1-322/flagrun.sh`, which writes the flags into the OPTIONS
line, runs the file cold with dependencies warm, and restores the base OPTIONS
line afterwards.

**This costs one extra run, the copy's own flagless baseline**, because a copy
is not the master and its time must be measured, not assumed.

**THE COPY IS A FAITHFUL STAND-IN. MEASURED**, against three flagless runs of
the same content in one session:

| run | what | wall (s) |
|---|---|---|
| A1 | the master, `--profile=definitions` | 140.39 |
| R0 | the master, no flags, the restore run | 141.76 |
| cb0 | **the copy, no flags** | **140.57** |

The three agree inside 1.0 percent. **The copy's baseline is 140.57 s** and it
is the control the flag runs are read against. Each of the three printed
exactly ONE `Checking` line, so each measured one module's own elaboration.

### RANK 1 IS REFUTED, and the flag runs the WRONG WAY

**`--no-syntactic-equality`, applied to this module alone through its OPTIONS
pragma, does not cut this file's cost. It multiplies it by at least 13.**

| fact | value |
|---|---|
| baseline, run cb0 | 140.57 s, exit 0 |
| **flagged, run cbn** | **1,840.76 s and STILL NOT FINISHED at the 30 minute wall, exit 130** |
| **the ratio** | **at least 13.1 times SLOWER. MEASURED** |
| `Checking` lines in `runs/cbn.out` | 1, so the flag stayed inside the module and the bisect worked |
| resident memory at the interrupt | 3.13 GB against an 8 GB cap. Heap was never the limit |
| agda slots before and after | 0 and 0 |
| load averages before and after | 4.97 7.00 7.35, then 6.08 6.95 7.27 |

**The decision table asks whether B cuts the file's own Total by 30 s or more.
It does not cut it at all. The measured direction is the opposite one, and the
size is not marginal: at least plus 1,700 s against a hoped minus 30 s.**

**Why this is the right reading of the flag, and not a broken measurement.**
`--no-syntactic-equality` REMOVES a shortcut. The Agda 2.8.0 option is
`--syntactic-equality={N}`, which the manual describes as giving "the syntactic
equality shortcut `N` units of fuel", and `--no-syntactic-equality` sets the
fuel to zero. **Rank 1's hypothesis was that the shortcut was being spent
without paying back at this site.** The measurement says the opposite: **the
shortcut is carrying this file.** So the mechanism is real and its sign is
backwards from the hypothesis. The finding is worth more than the cure would
have been, because it says the file's cost is dominated by equality checks that
the shortcut currently discharges cheaply.

**Both wall runs agree on this.** B1, the command-line run, walled at 1,840.43 s
without finishing `L.Condensation`'s closure. cbn, the pragma run, walled at
1,840.76 s without finishing the module alone. The two are independent and they
point one way.

### RANK 3 IS UNMEASURABLE, because `--lossy-unification` goes RED

The brief fixes this in advance: if the run goes red, report the arm
UNMEASURABLE and not a wall, because the heuristic is documented sound but
incomplete.

**Run cbl exited 42 after 669.39 s with ONE error.** The whole raw file is
7 lines, `agents/tasks/LJ-1-322/runs/cbl.out`, and the error is:

```
CondProbe.lagda.md:6151.14-15: error: [UnequalTerms]
n != suc n of type ℕ
when checking that the expression f has type
KFacts _A_46186 (suc K) _N0_46188 ... (c ∷ γ)
```

**RANK 3 IS UNMEASURABLE AT THIS SITE. MEASURED.**

**The failure lands inside the `KFacts` region, which is the region rank 3 was
supposed to help.** Line 6151 is the closing brace of a `KFacts` record built
field by field, six lines above `module ShapesAgree`
(`src/L/Condensation.lagda.md:6157`), the first of the six `KFacts` consumers
the brief names. **The copy is line-for-line identical to the master there;
`diff` over `:6140-6162` returns nothing. MEASURED.** So the error is the
master's error under this flag, not an artifact of the copy.

**The documented caveat is what happened.** The 2.8.0 page says the heuristic
"will cause Agda to ignore some possible solutions to unification variables".
The error message shows exactly that: the checker refused `n` against `suc n`
where the full unifier finds the index. **So the flag cannot be landed here
even as a measurement, and no timing from cbl means anything**, because 669.39 s
is the time to reach a failure and never the time to check the file.

### The instrument could have resolved a 30 s effect, and this matters

The threshold is 30 s, which is 21.3 percent of the file's 140.6 s. **The
measured run-to-run spread of the same content in this one session is 1.35
percent**, over four flagless full checks: 140.39, 140.57, 141.76 and 142.29 s,
a range of 1.90 s.

**So the machine noise never came close to hiding a 30 s effect.** The runs are
marked INDICATIVE because the brief orders that on a loud machine, and the
marking is conservative here: a 30 s effect is 15 times the observed spread,
and the effects actually measured are plus 1,700 s and a type error.

## RowTies gate: the gate FIRES

The gate: sum A1's charges over the `KFacts` consumers and the thirty `Agree`
modules. At 15 s or more a `RowTies` PROBE is funded, not the build.

| account | rows | charge |
|---|---|---|
| the thirty top-level `*Agree` modules | 127 | **36,600 ms, 36.60 s, 26.6 percent of Total** |
| the six `KFacts` consumers alone (`ShapesAgree`, `ClosedAgree`, `ShapedAgree`, `WitnessAgree`, `SatGraphAgree`, `LeafAgree`) | subset of the above | **15,543 ms, 15.54 s** |

**36.60 s against a 15 s floor. The gate FIRES, and a `RowTies` PROBE is
funded.** The six `KFacts` consumers pass the floor on their own, at 15.54 s.
Both figures are LOWER BOUNDS, because the profiler drops rows under 10 ms.

**The 10 ms floor is an instrument fact and I re-derived it (C-44).** A1's
smallest named row is 10 ms. Across this project's other definitions profiles
the smallest row is 10 ms in every file that has one:
`agents/tasks/LJ-1-283/runs/warmup-profile.out`,
`agents/tasks/LJ-1-311/runs/key-e1.out`, `key-e2.out`, `name-e1.out`,
`agents/tasks/LJ-1-289/runs/c1.out`, `t1.out`, `t2.out`, `t5.out`, `t6.out`
and `w0.out`. **No row under 10 ms exists in any of them. MEASURED.** So the
profiler truncates at 10 ms, and every sum over its named rows understates.

The six consumers are the six brief line numbers: `:6160` is inside
`ShapesAgree` (`src/L/Condensation.lagda.md:6157`), `:6449` inside
`ClosedAgree` (`:6446`), `:6550` inside `ShapedAgree` (`:6548`), `:6578` inside
`WitnessAgree` (`:6576`), `:6847` inside `SatGraphAgree` (`:6844`) and `:7109`
inside `LeafAgree` (`:7107`). **All six are among the thirty `Agree` modules,
so the two accounts are not disjoint. MEASURED by my own read of the
declarations.**

## A second false premise: `satGraphB`, `twelveB` and `closedBS` are NOT the cost carriers

The ruling's last branch says that if all three mechanisms miss, the project
returns to C-50 triage on "A1's charged rows, which already name `satGraphB`,
`twelveB` and `closedBS`". The claim comes from
`agents/tasks/LJ-1-311/lj-1.311-report.md:116-119`, which reports
`[LJ-1.283]`'s triage as ranking those three as Condensation's "cost
carriers".

**A1 is the first per-definition profile of this file, and it REFUTES that
ranking. MEASURED, from the raw rows.**

| definition | raw row | charge |
|---|---|---|
| `SatGraphB.Δ₀-twelveB` | `runs/a1.out:88` | 96 ms |
| `SatGraphB.twelveB` | `runs/a1.out:116` | 61 ms |
| `SatGraphB.Δ₀-satGraphB` | `runs/a1.out:128` | 58 ms |
| `SatGraphB.satGraphB` | `runs/a1.out:189` | 32 ms |
| `Δ₀-closedBS` | `runs/a1.out:325` | 11 ms |
| **all five together** | | **258 ms, 0.19 percent of the 137,453 ms Total** |

**Where the charge actually sits**, aggregating A1's 341 named rows by their
top-level module:

| module | charge |
|---|---|
| `SatGraphAgree` | 8,594 ms |
| `PropAgree` | 4,816 ms |
| `LeafAgree` | 3,041 ms |
| `BinShapeClosed` | 2,866 ms |
| `ExInAgree` | 2,239 ms |
| `AllInAgree` | 2,233 ms |
| `WitnessAgree` | 2,211 ms |
| `ImpLeaf` | 2,046 ms |

**The `Agree` family is the charge, at 36,600 ms over 127 rows, and the three
named definitions are 258 ms.** The three names were carried forward from a
triage, never from a per-definition profile of this file, because no such
profile existed until A1. **A cure brief written against those three names
would target 0.19 percent of the run.**

## `--no-syntactic-equality` against `--safe`: they CO-EXIST

The brief calls this out because an incompatibility would make the cheapest
cure unavailable whatever it measures.

**Both flags co-exist with `--safe`. MEASURED.** The probe is
`agents/tasks/LJ-1-322/SafeProbe.lagda.md`, which carries the same OPTIONS
header as `src/L/Condensation.lagda.md:4`
(`{-# OPTIONS --cubical --safe --guardedness #-}`) and an empty body, so a red
result could only come from the option check.

| probe | command | result | raw file |
|---|---|---|---|
| P1 | `agda --no-syntactic-equality` on the `--safe` module | **rc 0, no option error** | `runs/p1-nse-safe.out` |
| P2 | `agda --lossy-unification` on the `--safe` module | **rc 0, no option error** | `runs/p2-lossy-safe.out` |

**A side finding from P2, and it is load bearing for run B.** P1 built the
probe's interface. P2 changed only the flag, and P2 still printed a `Checking`
line for the same unchanged module. **An option change invalidates a cached
interface. MEASURED**, from the two raw files.

## Standing facts re-derived (C-44)

| claim | verdict | how |
|---|---|---|
| DD24's bar is 0.010514 s per line | **VERIFIED.** The bar is `ac_baseline_module_rate` 0.009143 times the 1.15 tolerance | `dev/ledger.toml:292-297` |
| the gap is 60.0 s | **VERIFIED.** "at 11,926 lines the on-bar allowance is 125.4 s, the wing measures 185.41 s, and the gap is 60.0 s" | `dev/ledger.toml:302-304` |
| `src/L/Condensation.lagda.md` is 132.28 s | **RE-MEASURED at 137.45 s profiled and 140.39 s wall, INDICATIVE.** See A1 above | `runs/a1.out:2`; `timings.csv` |
| 132.28 s is 71.4 percent of the GCH wing's 185.41 s | **VERIFIED by my own arithmetic**, 0.7135. At A1's 137.45 s the share reads 74.1 percent, but the wing's 185.41 s was not re-measured today, so the two figures are not from one session | arithmetic |
| 117 module applications in that file | **VERIFIED by my own grep**, the same regex `^\s*module [A-Za-z0-9_.]* *= `, count 117 | this task's grep, and `agents/tasks/LJ-1-317/lj-1.317-report.md:39` for the regex |
| zero `no-eta-equality` in that file | **VERIFIED by my own grep**, count 0. MEASURED | this task's grep |
| the file is 6,718 non-blank in-fence lines | **VERIFIED by my own count**, which matches `[LJ-1.320]`'s | this task's awk |
| the thirty `Agree` modules | **VERIFIED by my own grep**, `^module [A-Za-z0-9]*Agree` returns exactly 30 | this task's grep |
| `[LJ-1.283]`'s raw files pre-answer the `RowTies` gate | **REFUTED. MEASURED.** See the section below | `agents/tasks/LJ-1-283/runs/` |

## A false premise in the brief: there is no existing Condensation profile

The brief orders me to read the raw `.out` files of `[LJ-1.283]`'s "existing
Condensation profile", and says that if they are current they pre-answer the
`RowTies` gate, cross-check A1, and may save a run.

**No such profile exists. MEASURED.**

- `agents/tasks/LJ-1-283/runs/` holds six `.out` files. **Only one carries a
  `Total` row**, `warmup-profile.out`, and its `Checking` line reads
  `LJ-1-283.ControlEnv`, which is that task's own probe miniature, not
  `src/L/Condensation.lagda.md`. The other five are one `Checking` line each,
  with no profile at all.
- Across the whole tree: `find agents/tasks -name '*.out'` returns 200 files.
  **Not one of them is a profile of `src/L/Condensation.lagda.md`.** The four
  that contain the string `Condensation` are ratio-suite outputs
  (`agents/tasks/LJ-1-291/baseline/suite-13-test_ratio_baseline.out:11`, and
  three siblings), which report cone membership and carry no timing row.

**So no run was saved, the gate had no pre-answer, and A1 has no cross-check
from the record.** A1 is the first per-definition profile of this file on
record.

## WHAT THIS TASK LEAVES BEHIND

**The interface cache is restored. MEASURED.** The final flagless check of
`src/L/Condensation.lagda.md` is run r1: exit 0, 142.29 s, ONE `Checking` line.
An earlier restore, R0, ran after B1's interrupt and also printed ONE
`Checking` line at 141.76 s.

**A finding about the interrupt, and it saved this task an hour.** After B1 was
interrupted 30 minutes into rebuilding the closure under
`--no-syntactic-equality`, **the flagless run R0 found every dependency warm
and re-elaborated only `L.Condensation`. MEASURED.** So an interrupted flagged
run left no flagged interface on disk for this tree. INFERRED, as the reason:
the interrupted run never completed, and Agda's writes did not survive it. **I
did not test this and it is not a claim about Agda in general.**

**`_build/` is clean.** `scripts/gate/check-build-manifest.py` exits 0 and
prints "every file in `_build/` declares a lifecycle": 556 toolchain, 23
protected, 2 runtime. **Every interface this task wrote is under
`_build/2.8.0/**`, which `dev/build-manifest.toml` declares `toolchain`. No
undeclared file was created. MEASURED.**

**`scripts/gate/check-probes.py` exits 0**, "no probe outside `agents/tasks/`
and no generated file". **Nothing was written outside
`agents/tasks/LJ-1-322/`. MEASURED**, by `git status --short`.

**No code was edited.** `src/` is untouched. The one file this task varied is
its own probe copy, and `flagrun.sh` restores that file's base OPTIONS line
after every run, so the committed probe carries the master's header.

**Files this task leaves**, all inside `agents/tasks/LJ-1-322/`:

| file | what it is |
|---|---|
| `lj-1.322-report.md` | this report |
| `runs/*.out` | the raw agda output of every run. **The evidence** |
| `timings.csv` | wall seconds, exit code, slots and load for every run |
| `measure.sh` | the master's run harness |
| `flagrun.sh` | the isolated-flag harness, the bisect |
| `CondProbe.lagda.md` | the master with ONE line changed, the module name |
| `SafeProbe.lagda.md` | the `--safe` compatibility probe |

## WHAT FOLLOWS, and the ruling names it

The ruling's fourth branch returns the project to C-50 triage on A1's charged
rows. **A1 now exists, so the triage can be done against a profile instead of
against a carried claim.** What A1 says:

1. **The cost is NOT concentrated.** The largest single definition is
   `SatGraphAgree.back` at 3,576 ms, which is **2.6 percent** of the
   137,453 ms Total. **This is the opposite of `[LJ-1.283]`'s EnvSupply, where
   one two-line definition carried 99.2 percent.** A one-definition cure of the
   kind that won 91 s at `Cardinal` and 476 s at `EnvSupply` has no target
   here. **MEASURED.**
2. **The cost IS concentrated by FAMILY.** The thirty `Agree` modules carry
   36,600 ms over 127 rows, 26.6 percent of Total and 64 percent of everything
   the profiler attributes. **A family-level cure is the shape that fits this
   profile**, which is what the `RowTies` gate was asking about, and the gate
   fires.
3. **The dark bucket is 58.3 percent and A2 says what is inside it.**
   `Typing` inclusive is 84,556 ms, 61.3 percent of the run, split
   `CheckRHS` 34,207, `CheckLHS` 30,989, `OccursCheck` 12,853. **So the
   unattributed half is type checking, not bookkeeping**, and a cure has to
   reduce elaboration work rather than interface work.
4. **The equality shortcut is load bearing.** Removing it costs at least
   plus 1,700 s. **INFERRED from that: this file's cost is dominated by
   equality checks that the shortcut currently discharges cheaply, and the
   remaining expensive ones are those it cannot.** That is a hypothesis for the
   next probe, not a price.

**I propose no cure. This task was funded to measure and it measured.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker. **This task writes no code**, so no shared
line moves.

**NAME THE AXIS (C-46).** DD4's axis is AC-against-GCH, fixed in code at
`scripts/measure/ledger.py:50`, which describes `--reuse` as "what the AC and
GCH closures share".

**I RE-RAN THE CLOSURE rather than quoting an older figure**, because the brief
records that `src/L/GCH.lagda.md` was restated last night by the `[LJ-1.323]`
ruling. **The restatement is real:** `git log` shows commit `ffb0811`,
"`[LJ-1.323]` The GCH trophy is restated as the L-internal cardinal equality",
as the newest commit on that file.

Today's re-run, from HEAD, using `ledger.py`'s own `import_graph` and
`closure` at `scripts/measure/ledger.py:392-416`:

| account | today |
|---|---|
| AC closure, root `src/L/Model.lagda.md` | 73 masters, 17,197 lines |
| GCH closure, root `src/L/GCH.lagda.md` | 48 masters, 8,889 lines |
| shared | 43 masters, 7,596 lines, 41.1 percent of the union |
| **`src/L/Condensation.lagda.md` in the AC closure** | **NO. MEASURED** |
| **`src/L/Condensation.lagda.md` in the GCH closure** | **NO. MEASURED** |

**`[LJ-1.320]`'s DD4 reading is VERIFIED, with one correction of wording.** The
file is in NEITHER trophy statement's closure, which I re-measured today after
the restatement. It IS a declared member of the GCH WING, the seconds account
that DD24 judges: `dev/ledger.toml:3106` opens `gch_wing` and
`src/L/Condensation.lagda.md` is one of its 12 members. **So the file is on the
judged side and in no shared statement closure. P-y's shared-code warning
therefore runs in the favorable direction: a cure here can cost no shared
code, and every second saved improves the DD24 ratio. VERIFIED.**

**The correction of wording.** A cure here does not "serve the GCH end" in the
sense of the trophy STATEMENT, because the statement does not import the file.
It serves the GCH WING's seconds account. The two are different objects and
`dev/ledger.toml:204` says why the statement figure is the weaker one: the GCH
closure is read from a statement "whose proof is not wired", so it
**UNDERSTATES**. **VERIFIED by my own read of that line.** Five masters import
Condensation today (`src/L/BoundedSubset.lagda.md`,
`src/L/Coding/EnvSupply.lagda.md`, and the three
`src/L/Condensation/*Agree.lagda.md`), and none of them is inside either
closure, which is consistent with a proof that is not yet wired to the
statement.

## ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-320/lj-1.320-ruling.md`, read WHOLE.** TAKEN: the
  decision table at `:210-215` and the `RowTies` gate at `:220-225`, which this
  report applies without change. Also taken: the four-run order at `:188-202`.
  NOT TAKEN: nothing was refused, but its action-4 sentence about
  `[LJ-1.283]`'s "existing Condensation profile" (`:204-207`) is REFUTED by my
  own read of that directory. See the false-premise section above.
- **`agents/tasks/LJ-1-317/lj-1.317-report.md`.** ONE line read that bears:
  `:93-99`, the CAUTION that `--syntactic-equality` sits under "Options that
  affect interface file reloading", so a clean rebuild is needed for a fair
  measurement. **That caution is now MEASURED, not INFERRED**, and it decided
  this task's run design for B and C. Also taken: the 117-application regex at
  `:39`, which I re-ran.
- **`agents/tasks/LJ-1-283/lj-1.283-report.md`.** ONE line read that bears:
  `:14-16`, "One `--profile=definitions` run charges 475,710 ms of 479,311 ms,
  99.2 percent ... to ONE two-line definition". **That is the CONCENTRATED
  shape, and A1 measures the opposite shape at this site**: the largest single
  definition here is 3,576 ms of 137,453 ms, which is 2.6 percent. Also read:
  its `runs/` directory, whole, which is where the false premise was found.
- **`agents/tasks/LJ-1-311/lj-1.311-report.md`.** ONE line read that bears:
  `:125-126`, "`[LJ-1.309]`'s premise was FALSE: the raw profile always carried
  the row." **This report obeys the resulting law**: every figure above is read
  from the raw `.out` file named beside it, and the two profile files are short
  enough that A2's is quoted whole.
- **`archive/dev/TASKS-archived.md`**, taken as SHAPE and never as a claim. ONE
  line read that bears: `:245`, "Profile the carried sequence's 174.62 s: where
  does the time go? CONCENTRATED then NO-GO: top 11 carry 71.4 pct". **The
  retired route ran this same seconds crisis and its profiles came back
  CONCENTRATED.** The shape at this site is different, and that difference is
  the finding, not the resemblance.

## LITERATURE USED (DD18)

The corpus is a proof assistant's, delivered by
`agents/tasks/LJ-1-317/lj-1.317-report.md`.

- **agda#5801**, rank 1's mechanism. USED as the reason to test
  `--no-syntactic-equality`.
- **agda#1646**, rank 2's mechanism. USED as the reason to read `Serialization`
  and `Import` under `--profile=internal`.
- **agda#6509 and the 2.8.0 lossy-unification page**, rank 3. USED for the
  "sound but not complete" caution, which is why run C is reported as a
  measurement and never as a landed cure.
- **The 2.8.0 command-line options page.** USED for two claims: that
  `--syntactic-equality` affects interface file reloading, now MEASURED true at
  a large scale, and that the page gives no list of options forbidden with
  `--safe`, which is why this task probed the question instead of reading it.

**Does any source state a figure I can compare mine against? NO. MEASURED.**
The three issues describe mechanisms and symptoms and state no timing for a
comparable file, and the 2.8.0 pages state no timings at all. The only figure
in the corpus is this project's own, `[LJ-1.281]`'s 90.7 s of 100.8 s in
`Typing.CheckRHS`, and A2 measures 24.8 percent at this site against that
90 percent, so it does not transfer (P-l).
