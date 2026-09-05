# LJ-1.201 report: adversarial review of `[LJ-1.185]`'s negative verdict

tier: opus (deepseek-subagent-mode), DD25 adversarial row. Written incrementally
(C-22). **STATUS: COMPLETE.** I edited no master, no brief and no report. I ran
no Agda. I did not commit and I did not push. Every negative below is marked
**MEASURED** or **INFERRED**.

## 0. LEAD

**UPHELD BUT MISATTRIBUTED.**

**The STOP is right and the reason given for it is wrong: `[LJ-1.185]` refutes
`[LJ-1.177]` correctly, but it then declines to price a cure because "the
instrument cannot resolve it", when the true reason is that nobody has ever
measured a lever on `Typing.OccursCheck`.**

### 0.1 The review in five lines

| claim | verdict |
|---|---|
| **the double subtraction** | **UPHELD, MEASURED.** I re-derived both derivations from the raw files. `[LJ-1.155]`'s 41,326 ms of subtracted phases contains `DeadCode` at 5,297 ms. Section 1.1 |
| **the residue is 17.8 s today** | **UPHELD for the run, OVERSTATED as a figure.** Its own tool reproduces 17,839 ms with a 2.5 percent spread. That spread is WITHIN one series. The same estimator gave 21.2 s and 21.9 s at the same master on the two prior days. Section 1.2 |
| **the 0.25 percentage point fit** | **OVERSTATED, MEASURED.** Its four columns are two: `A+C = B+D` is an identity, so each pair gives ONE check and not two. And the fit has SIX more counter-examples, not one, two of them at this master. Section 1.2 |
| **instantiation is 0.9 percent** | **UPHELD, MEASURED.** The probe D minus probe C delta reproduces to the millisecond. The conclusion survives a tenfold transfer error. Section 1.3 |
| **no cure could be shown to have worked** | **OVERTURNED, MEASURED.** The `+-12.8` percent band is a ONE-MODULE BETWEEN-SERIES figure. `[LJ-1.185]` used a WITHIN-SERIES paired design itself in section 2.9 and then denied that design in section 3.3. Section 2.2 |

### 0.2 What changes because of this review

**Do not rule the residue term SPENT.** It is UNPRICED, not spent. The probe
`[LJ-1.185]` designed in its own section 8.2 costs about ten seconds a run, and
it is the one thing that would price the lever. **The report declined to build
it BECAUSE of the argument this review overturns.**

## 1. QUESTION 1: IS THE REFUSAL CORRECT ON ITS OWN NUMBERS?

### 1.1 The double subtraction. UPHELD, MEASURED

**I re-derived both derivations from the tracked raw files. `[LJ-1.185]` is
correct.**

`agents/tasks/LJ-1-155/runs/src_L_Condensation.int1.txt:10-36` prints every
phase. I summed the phases that are not `Typing` and are not `Miscellaneous`:

```
Serialization 18,525 + DeadCode 5,297 + Positivity 5,021
+ InterfaceInstantiateFull 3,435 + Coverage 3,332 + Parsing 2,632
+ Deserialization 1,689 + Scoping 653 + Highlighting 351
+ Termination 332 + Import 31 + Injectivity 28            = 41,326 ms
```

**That is `[LJ-1.155]:135-137`'s own 41,326 ms exactly, and `DeadCode` is inside
it.** `agents/tasks/LJ-1-155/runs/src_L_Condensation.defs1.txt:10-11` gives
`Miscellaneous` 62,594 ms, so `62,594 - 41,326 = 21,268 ms`, which is
`[LJ-1.155]:136`.

`agents/tasks/LJ-1-177/lj-1.177-report.md:259-265` then writes that "`DeadCode`
is only 5,297 ms of it" and takes "the other 16 s". **MEASURED FALSE. The 5,297
ms was already removed.** I checked the counter-case: a sum WITHOUT `DeadCode`
is 36,029 ms and gives a residue of 26,565 ms, not 21,268 ms.

**One correction of emphasis against `[LJ-1.185]`'s own headline.** The
arithmetic error made `[LJ-1.177]`'s lever SMALLER, not absent. The term the
brief pointed at was 21.3 s on that tree, which is MORE than 16 s.
**`[LJ-1.185]`'s lead "THE 16 SECONDS DOES NOT EXIST" is true only of the
DECOMPOSITION.** The report says so itself at `:238-242`, so this is a headline
issue and not an error.

### 1.2 The account of the residue and the 0.25 percentage point fit

**The residue SIZE reproduces exactly.** I ran the report's own
`agents/tasks/LJ-1-185/residue.py` over its six tracked runs. It printed
18,133 / 17,688 / 17,696 ms, mean 17,839 ms, spread 2.5 percent. **That matches
`agents/tasks/LJ-1-185/lj-1.185-report.md:211-215` to the millisecond.**

#### 1.2.1 THE FOUR COLUMNS OF SECTION 2.7 ARE TWO. MEASURED

Name the four columns of `lj-1.185-report.md:249-253`:

```
A = (Total - Miscellaneous) / Total            (definitions run)
B = (CheckLHS + CheckRHS) / Total              (internal run)
C = residue / Total                            (the subtraction)
D = (TypeSig + OccursCheck + bare Typing) / Total   (internal run)
```

`C = p - q` and `A = 1 - p`, so `A + C = 1 - q`. `B + D` is the whole of
`Typing` over the internal total, which is also `1 - q`. **So `A + C = B + D`
by construction.** I confirmed it on all three pairs: 61.25 against 61.25,
61.59 against 61.59, 61.15 against 61.15.

**MEASURED: "Every row agrees to 0.25 percentage points" counts each pair
twice.** The row `A ~ B` and the row `C ~ D` are one statement, mirrored. The
evidence is three checks, not six.

#### 1.2.2 THE COLUMN LABEL IS WRONG. MEASURED, and it does not change the fit

The column that `lj-1.185-report.md:249` labels "definition sum / total" is
`(Total - Miscellaneous) / Total`. **The printed definition rows sum to 45.57 /
46.28 / 45.95 percent**, which misses column B by 1.5 to 2.0 percentage points.
The 2,151 / 2,217 / 2,336 ms difference is the rows Agda drops below its print
threshold. **The method is right and the report states it at `:74-77`. Only the
label is wrong**, and a later reader who takes the label at face value will not
reproduce the fit.

#### 1.2.3 SIX MORE COUNTER-EXAMPLES, not one. MEASURED

The brief asked me to find more counter-examples or to confirm there are none.
**I found six, and two of them are at this master.** I applied the same test to
every profile pair that the tree tracks:

The `miss` column is `(C - D)` on the internal run's clock. It is the part of
the residue that the identification does not explain.

| site | `A - B`, percentage points | run gap | miss, ms |
|---|---:|---:|---:|
| `[LJ-1.185]` pair 1, 2026-08-14 | **-0.25** | 6.49 pc | +336 |
| `[LJ-1.185]` pair 2 | **+0.22** | 4.99 pc | -285 |
| `[LJ-1.185]` pair 3 | **+0.24** | 0.86 pc | -315 |
| **`L/Condensation` at `[LJ-1.145]`, 2026-08-13** | **-3.21** | 1.08 pc | **+3,927** |
| **`L/Condensation` at `[LJ-1.155]`, 2026-08-13** | **-3.82** | 1.20 pc | **+4,628** |
| `TwelveAgree` at `[LJ-1.155]` | **+13.89** | 0.75 pc | -4,110 |
| `LowerAgree` at `[LJ-1.155]` | **+4.23** | 0.50 pc | -838 |
| `UpperAgree` at `[LJ-1.155]` | **+7.40** | 1.31 pc | -881 |
| **`ProbeLJ1185B`, its own probe, four repeats** | **-1.33 to -2.00** | 0.08 to 4.00 pc | +25 to +32 |
| `ProbeLJ1185C`, four repeats | -5.08 to -18.42 | small | degenerate |

Sources: `agents/tasks/LJ-1-145/lj-1.145-report.md:40-79`;
`agents/tasks/LJ-1-155/runs/src_L_Condensation{,_TwelveAgree,_LowerAgree,_UpperAgree}.{defs1,int1}.txt`;
`agents/tasks/LJ-1-185/runs/agents_tasks_LJ-1-185_ProbeLJ1185{B,C}.agda.{defs,int}{1,2,3,4}.txt`.

**`ProbeLJ1185C` is degenerate and I discount it.** Its total is 90 to 118 ms,
and Agda prints NO definition row at all, so `A` reads 0.00. The report already
warns about that file at `:293`.

**The two rows that matter are the first two `L/Condensation` rows.** They are
the SAME MASTER, one day earlier, with the SAME method, and their run gaps are
1.08 and 1.20 percent, which is TIGHTER than pairs 1 and 2 of the fit itself.
**So the mismatch is not a run-gap artefact. MEASURED.** The fit missed by
3,927 ms and 4,628 ms there, which is 18 to 21 percent of the residue it was
explaining.

**MEASURED CONCLUSION: the billing law holds at one master on one morning and
fails at six other sites in the tree's own tracked files.** The proposed law at
`lj-1.185-report.md:557-573` says `TypeSig` and `OccursCheck` "sit outside it
wherever they occur". **That word "wherever" is MEASURED FALSE.**

#### 1.2.4 SECTION 2.6 AND SECTION 2.7 CONTRADICT EACH OTHER. MEASURED

`lj-1.185-report.md:225-231` says "THE TERM HAS BEEN MEASURED THREE TIMES AND IT
IS FALLING ON ITS OWN", from 22.2 s to 22.7 s to 17.8 s. `:257-266` says the
term IS `TypeSig` plus `OccursCheck` plus bare `Typing`.

**Read the identified content off the internal profiles directly. It ROSE.**

| when | `TypeSig` + `OccursCheck`, ms | source |
|---|---:|---|
| `[LJ-1.145]`, 2026-08-13 | 16,240 | `lj-1.145-report.md:75-77` |
| `[LJ-1.155]`, 2026-08-13 | 16,143 | `runs/src_L_Condensation.int1.txt:15-16` |
| `[LJ-1.185]`, 2026-08-14, mean of three | **17,082** | `runs/src_L_Condensation.int{1,2,3}.txt` |

**MEASURED: the identified content rose 5.8 percent while the residue estimator
fell 18 percent, from 21,858 ms to 17,839 ms.** Both cannot be right. The
estimator is a difference of two fractions from two different runs, and section
1.2.3 measures its error at 3.9 to 4.6 s at this master. **The stable reading
is the phase account, and the
"falling on its own" sentence is an artefact of the noisier estimator.
INFERRED for the cause, MEASURED for the three phase sums.**

**One small transcription error, immaterial.** `lj-1.185-report.md:212` and
`:252` give pair 2's share as 13.62 percent. Its own tool gives 13.57 percent.
The residue in milliseconds, 17,688, is correct.

### 1.3 Instantiation at 0.9 percent. UPHELD, MEASURED

**The probe D minus probe C delta reproduces exactly.** I took the mean of
repeats 2, 3 and 4, which are the report's three kept pairs:

| phase | my delta, ms | report, `:307-312` |
|---|---:|---:|
| `DeadCode` | 986 | 986 |
| `Serialization` | 785 | 785 |
| `InterfaceInstantiateFull` | 166 | 166 |
| `Typing`, all sub-phases | 152 | 152 |
| `Parsing` + `Scoping` + `Deserialization` | 60 | 59 |
| **total** | **2,151** | **2,151** |

**And the sub-phase split strengthens the report beyond what it wrote.** The
152 ms of `Typing` is `+150` of BARE `Typing` and `+12` of `OccursCheck`, with
`TypeSig` and `CheckRHS` flat. **So a module application bills to the one row
the report marked as its uncertain 7 percent.** 136 applications carry 150 ms
against the master's 1,202 ms of bare `Typing`, which is 12 percent of that
row. That is internally consistent.

**The census reproduces.** I counted the in-fence lines of
`src/L/Condensation.lagda.md` myself: **136 module applications, 54 distinct
aliases, 99 other module headers.** That matches `lj-1.185-report.md:154` and
`[LJ-1.177]`'s 99 headers.

**One weakness in the transfer, and it does not change the verdict.**
`lj-1.185-report.md:324-331` argues the probe OVERSTATES the master, because
`Body` has 24 signatures while `EnvSet` has 17 and the others fewer. **That
compares COUNTS and not TYPE SIZE.** `agents/tasks/LJ-1-185/gen_probe.py:101-112`
builds each `Body` type from 24 parameter names and one ladder name, which is a
small term. The master's applied modules carry real formulas and stages in
their types. **So the direction of the transfer is INFERRED, not MEASURED, and
the report states it as an upper bound rather than a price.** The verdict
survives anyway: at ten times the probe's price, instantiation is 1,520 ms,
which is 8.5 percent of the residue and still not "the 16 s".

**The telescope half also reproduces.**
`agents/tasks/LJ-1-155/runs/agents_tasks_LJ-1-155_ProbeLJ1155B1.agda.int1.txt:12-14`
gives `DeadCode` 2,822 ms against all of `Typing` at 1,091 ms, for a
36-hypothesis telescope. **MEASURED: a telescope's price is `DeadCode`, which
the residue excludes.**

## 2. QUESTION 2: IS THE MEASUREMENT SOUND?

### 2.1 The protocol, the run count and the load. SOUND

**I checked every raw header.** All 34 files under
`agents/tasks/LJ-1-185/runs/` carry `GHCRTS -A64m -I0 -M8g`, exit 0, wall
seconds, and the load before and after. The cap is never raised. The three
master pairs ran at load 3.04 to 3.60. The probe series ran at load 2.90 to
3.67. **The report's account of the machine at `:545-556` matches the file
headers.** The report also declares its own contamination at `:442-462` instead
of hiding it, and it chose the pessimistic figure for the headline.

**The wing figures reproduce.** `runs/wing-ratio.txt` gives 192.41 s over
11,926 lines. The four Condensation masters read 6,676 + 494 + 305 + 306 =
7,781 lines and 138.63 + 8.59 + 5.64 + 5.39 = 158.25 s. The other eight read
4,145 lines and 34.16 s, which is 0.0082 s per line and UNDER the 0.010514 bar.
**Section 5.3 is correct to the last digit. MEASURED.**

### 2.2 THE INSTRUMENT ARGUMENT IS WRONG. OVERTURNED, MEASURED

**This is the load-bearing leg of the whole negative and it does not hold.**

`scripts/check-ratio.py:72-98` states what the constant is:

> MEASURED 2026-08-13 by [LJ-1.148] ... it is the BETWEEN-SERIES figure rather
> than the within-series one. ... WITHIN any one of those series the spread was
> 0.5 to 4.0 percent, so a series cannot see its own displacement and reports a
> false confidence. A verdict is ONE series on ONE occasion, so the
> between-series figure is the one that governs it.

**The band answers the question "is this wing 1.76x?". It does not answer the
question "did this cure work?".** A cure is a DIFFERENCE, and a difference has
three possible designs:

| design | what carries the error |
|---|---|
| one series before, one series after | the between-series band, `+-12.8` percent |
| both spellings alternated INSIDE one series | the within-series spread, 0.5 to 4.0 percent |
| the phase account read off `--profile=internal` | the phase's own repeatability |

**`lj-1.185-report.md:353-396` assumes the first design and then says "THERE IS
NO CURE THAT THIS PROJECT'S INSTRUMENT COULD SHOW TO HAVE WORKED". MEASURED
FALSE for the instrument, TRUE only for that design.**

**And the report used the second design itself, four sections earlier.**
`:283-322` measures a 2,151 ms delta as probe D minus probe C, three kept
repeats, inside one window, and marks it MEASURED. `[LJ-1.159]:262` measured
100.64 s against 11.92 s the same way. `[LJ-1.145]:207-223` measured 10 ms
against 23 ms inside ONE run. **The report accepted the design in section 2.9
and denied it in section 3.3.**

**Here is the arithmetic, from the report's own raw files.**

| quantity | three runs | spread |
|---|---|---:|
| master total, internal | 134,223 / 133,718 / 132,444 ms | **1.33 pc** |
| master wall, definitions | 128.55 / 129.25 / 133.48 s | **3.8 pc** |
| **`Typing.OccursCheck`** | **11,904 / 11,925 / 11,750 ms** | **1.48 pc** |
| `Typing.TypeSig` | 5,241 / 5,290 / 5,135 ms | 2.97 pc |

**A cure that took HALF of `OccursCheck` is 5,875 ms.** Against the master's
own within-series total spread of 1,779 ms that is 3.3 times. Against
`OccursCheck`'s own spread of 175 ms that is 34 times. **MEASURED: such a cure
is resolvable, and the report's own runs measure it.**

**A CAUTION AGAINST MY OWN OVERTURN, and I state it rather than hide it.** A
cure of `OccursCheck` can move other phases. I-5 writes branch types, which
creates signatures, which adds `Typing.TypeSig`. **So `OccursCheck` alone is not
the net.** The answer is that all phases sum to the total in the same profile,
so one run shows the trade and the net together, and the within-series total
spread is 1.33 percent. **The design still resolves the cure. It must read the
whole account and not one row.**

**A second check, across three days and three trees.** `OccursCheck` as a share
of the master's check reads 9.176 / 9.064 / 8.869 / 8.918 / 8.872 percent at
`[LJ-1.145]`, `[LJ-1.155]` and `[LJ-1.185]`'s three runs. **The total spread is
3.4 percent, or 0.31 percentage points, and it is a BETWEEN-SERIES and
BETWEEN-TREE figure.** A cure of 4.4 percentage points is fourteen times that
drift.

### 2.3 The band was also applied to the wrong denominator. MEASURED

`lj-1.185-report.md:384` multiplies `+-12.8` percent by the WING's 192.41 s to
get `+-24.6` s. **`check-ratio.py:88-95` says why that is the wrong direction:**

> ... both are the spread of a SUM over many masters, and independent per-module
> noise averages DOWN as you sum. A sum's spread is a LOWER BOUND on one
> module's ...

**The constant is a ONE-MODULE figure, and a twelve-master sum spreads LESS,
not more.** The report's own `runs/wing-ratio.txt` prints "the aggregate rests
on 2 runs and spreads 1.9%". **So the 24.6 s band overstates the wing's
uncertainty, and `dev/PLAN.md:78-80` now carries that overstatement into the
live status screen.**

**And DD24's own judgment is a RATIO taken inside one run.**
`runs/wing-ratio.txt` prints "1.76x the AC side at the SAME caliber", which
compares the wing and the AC baseline measured by the same tool in the same
series. **A displacement of the series moves both sides together. So the
quantity DD24 judges is already a within-series comparison**, and the
between-series band governs the absolute seconds rather than the ratio. **I
mark the last step INFERRED**, because a displacement is not proved to be
uniform across masters.

## 3. QUESTION 3: DID THE BRIEF CAUSE THE OUTCOME?

**YES, TWICE. This is the orchestrator's defect and it is a seventh false
premise plus a fixed instrument.**

**Premise one, and the return caught it.** `agents/tasks/LJ-1-185/LJ-1.185.md:8-11`
states "the GCH wing's ONLY remaining lever is about 16 seconds ... which it
identifies as module-application instantiation". **MEASURED FALSE, and the
return refuted it.** That is the dispatch working as DD25 intends.

**Premise two, and the return did NOT catch it.**
`agents/tasks/LJ-1-185/LJ-1.185.md:23-27` writes:

> **a cure under about 21 s cannot be shown to have worked by one pair of runs**
> ... **That last row is your design constraint, not a caution.**

and `:85-88` adds "A delta inside the band is not a small measurement, it is no
measurement."

**The brief fixed the measurement design at "one pair of runs" and named it a
CONSTRAINT.** The agent obeyed it. Section 3.3 of the return is that constraint
applied to a 17.8 s term, and section 8.2 declines the probe for the same
reason:

> Section 3.3 measures that the whole term is smaller than the wing's noise
> band, **so the probe would price a lever that cannot be shown to have worked
> even at one hundred percent.**
> (`lj-1.185-report.md:604-607`)

**MEASURED: the brief supplied the argument that produced the STOP.** The agent
ran a three-pair protocol of its own and still did not question the one-pair
framing, because the brief said it was not a caution. **That is C-39 and C-40's
class exactly, and it is the fourth item of the return's own recommendation
list turned against the return.**

## 4. QUESTION 4: IS THERE A CURE THE RETURN MISSED?

**YES, and the evidence is in the return's own raw files.**

### 4.1 `Deserialization` gained 8.3 s at this master in one day. MEASURED

| when | `Deserialization`, cumulative ms | source |
|---|---:|---|
| `[LJ-1.145]`, 2026-08-13 | 1,535 | `lj-1.145-report.md:79` |
| `[LJ-1.155]`, 2026-08-13 | **1,689** | `runs/src_L_Condensation.int1.txt:28` |
| `[LJ-1.185]`, 2026-08-14 | **9,955 / 9,954 / 10,230** | `runs/src_L_Condensation.int{1,2,3}.txt` |

**MEASURED: a non-`Typing` phase at this master went from about 1.6 s to about
10.0 s, and it is stable over three consecutive runs with a 2.8 percent
spread.** The whole master's internal total rose **12.3 s** over the same
period, from 121,115 ms to a three-run mean of 133,462 ms, and
`Deserialization` is **68 percent** of that rise. The master gained 122
in-fence lines in the same period, which at its own 0.0208 s per line accounts
for 2.5 s.

**I ruled out the page cache. MEASURED.** If the dependency interfaces were
cold on disk, run 1 would be slow and runs 2 and 3 fast. They read 9,955,
9,954 and 10,230 ms. The harness moves aside the TARGET's interface only, so
the dependencies stay warm after run 1.

**I ruled out contention. MEASURED.** The 1,689 ms reading was taken at load
5.51 to 8.44 (`runs/src_L_Condensation.int1.txt:5`). The 10,000 ms readings
were taken at load 3.38 to 3.65. **The LOADED day was the FASTER one, so
contention does not explain the rise.**

**The cause is INFERRED and I did not bisect it.** `[LJ-1.173]` and
`[LJ-1.176]` edited this master between the two dates. A new import that drags
a large dependency interface is the obvious candidate. **I did not verify it,
and I did not run Agda.**

**Why this matters.** 8.3 s is larger than the 5.2 s `DeadCode` ceiling that
`[LJ-1.177]` and the brief both call the wing's remaining lever. It is NOT in
the residue, because the residue excludes every non-`Typing` phase by
construction. **It is a wing-local term of about 8 s that no report owns, and
its size is read straight off a phase account rather than from a cross-run
subtraction.**

### 4.2 The probe the return designed and did not build

`lj-1.185-report.md:591-608` writes the probe in full: restate one `back`
definition twice at the master's own generality, once with the truncation
branches left to inference and once with every branch carrying a written type
(I-5), and read `Typing.OccursCheck` off `--profile=internal` in both. **It
costs about ten seconds a run and it needs no master edit.**

**Section 2.2 removes the only reason the report gave for not building it.**
`OccursCheck` reads to 1.48 percent over three runs, so this probe measures its
own answer.

### 4.3 What I do NOT claim

**I do not claim a cure exists.** `lj-1.185-report.md:364-374` is right that
P-l forbids carrying `[LJ-1.145]`'s `midOpen`-to-`midSealed` factor onto
`OccursCheck`, because that factor is a `Typing.CheckRHS` coercion. **Nothing
in this repository has measured a lever at an `OccursCheck` site. That is
correct and I confirm it.** The difference is the WORD: the term is UNPRICED,
and the report calls it unmeasurable.

## 5. C-42 IN BOTH DIRECTIONS

### 5.1 Does the negative reach FURTHER than it claims? YES, in three places

1. **The proposed law at `:557-573`** says `TypeSig` and `OccursCheck` sit
   outside every definition "wherever they occur", and that a residue is "never"
   priced by naming a construct in the source. **MEASURED FALSE at six sites,
   section 1.2.3.** Do not admit the law as written. Its measurement supports
   one master on one morning.
2. **Section 6 at `:506-509`** says the billing law "holds for the J tower's
   masters on the day they exist, and it means nobody has to run this diagnosis
   twice". **Same over-reach.** The law is site-dependent, so the J side must
   re-measure it.
3. **Section 3.3 at `:353`** generalises one measurement design to "this
   project's instrument". **OVERTURNED, section 2.2.**

### 5.2 Does the negative reach LESS far than it claims? YES, in two places

1. **It is about ONE CHAPTER, not the wing.** The report's own section 5.3
   measures that eight of twelve wing masters sit UNDER the bar together at
   0.0082 s per line, and that the Condensation family carries 82 percent of
   the seconds on 65 percent of the lines. **The report says this. The PLAN
   sentence at `dev/PLAN.md:70-83` keeps it. Read the verdict as "the
   Condensation family has no priced lever", not "the wing has none".**
2. **The instantiation refutation prices a probe, not the master.** Section
   1.3 gives the reason. The conclusion survives a tenfold error, so the
   shortfall changes nothing here. **It would matter if a later report reused
   the 15.8 ms per application as a price at a different site (P-l).**

## 6. THE RAISED GAP, 44 s to 56 or 67 s

**UPHELD as arithmetic. The deflation is INFERRED and the report says so.**

`runs/wing-ratio.txt` gives 192.41 s over 11,926 lines, n=2, aggregate spread
1.9 percent. On-bar seconds are `11,926 x 0.010514 = 125.39`, so the gap is
**67.02 s**. That reproduces exactly.

**The 6.3 percent deflation carries one unpriced difference.** The report
compares its own three quiet runs at 128.55 / 129.25 / 133.48 s, which used
`--profile=definitions`, against `check-ratio.py`'s 138.63 s, which used no
profile flag. **Those are two different commands.** If profiling costs
anything, the contention is LARGER than 6.3 percent and the deflated 181.0 s is
too generous. The report writes "I can price the contamination"
(`:449`), which reads as MEASURED. **Mark it INFERRED.**

**A finding the report did not draw from its own gap.** The wing went from
164.60 s at `[LJ-1.173]` to 192.41 s, which is +27.8 s for +101 lines. Deflated
it is +16.4 s. **At 10 to 17 percent of 164.60 s that sits at the edge of the
band, so it is not established by these two figures.** But section 4.1
identifies 8.3 s of it at one master in one phase, and that reading is stable
over three runs. **The wing's growth has a partly identified cause and nobody
has claimed it.**

## 7. DD4

**The probe series is genuinely generic and I checked it.**
`agents/tasks/LJ-1-185/gen_probe.py` builds its carrier as a private unary `N`
inside the generated file. `ProbeLJ1185A/B/C/D.agda` import only
`Cubical.Foundations.Prelude`. `residue.py` reads any pair of Agda profile
files. **No tower name appears in any of them. The series re-instantiates for
the J side unchanged.** `[LJ-1.185]` did not use its stop-line as a reason to
write fixed.

**One DD4 question the report did not ask, and it runs the other way.** The
residue's dominant term is `Typing.OccursCheck`, which is metavariable solving.
**Generic code creates more metavariables than fixed code, so DD4's own
direction feeds the term the report declares unfixable.** `[LJ-1.159]:262`
measured generic at 8.4 times cheaper in SECONDS at a neighbouring site, so the
direction is not settled either way. **This is a question for a brief, not a
refutation, and I raise it rather than answer it.**

**The DD4 test the brief set does NOT bite here.** `[LJ-1.185]` did not price a
fixed shape and refuse it. It measured a property of Agda 2.8.0's elaborator,
which has no fixed and no generic spelling.

## 8. WHAT THIS UNBLOCKS OR CONFIRMS

**CONFIRMED, and the campaign may rely on these.**

1. **The double subtraction.** `[LJ-1.177]`'s 16 s decomposition is dead.
2. **Instantiation is not the residue.** 136 applications cost 2,151 ms, of
   which 152 ms is `Typing`.
3. **A telescope's price is `DeadCode`.** The residue excludes it.
4. **The wing gap is 67 s undeflated, and eight of twelve masters are under
   the bar.**

**UNBLOCKED, and each needs a decision.**

1. **Do NOT rule the residue term SPENT.** `[LJ-1.185]`'s recommendation 1 at
   `:689-692` rests on section 3.3, which section 2.2 overturns. **The term is
   UNPRICED.**
2. **Build the section 8.2 probe.** It costs about ten seconds a run and no
   master edit. It is the only thing that prices the `OccursCheck` lever.
3. **Correct `dev/PLAN.md:78-80`.** The sentence "The whole term is smaller
   than the wing's own noise band of 24.6 s, so a 100 percent cure could not be
   shown to have worked" applies a one-module between-series band to a
   twelve-master aggregate and to a within-series question.
4. **Open the `Deserialization` question.** 8.3 s appeared at this master in
   one day. Its size is MEASURED and its cause is INFERRED.
5. **Do not admit the proposed law at `:557-573` as written.** Six
   counter-examples, two at the master itself. **If the orchestrator still
   wants a law, the admissible statement is narrower: at
   `src/L/Condensation.lagda.md` on 2026-08-14 the residue matched `TypeSig`
   plus `OccursCheck` plus bare `Typing` to 0.25 percentage points in three
   pairs, and the same test fails by 3.2 to 13.9 percentage points at six other
   sites.**
6. **A brief must stop shipping the instrument with the task.** The band
   belongs in a brief as a fact. `LJ-1.185.md:25` made it a design constraint,
   and the agent could not then choose a design.

## 9. WHAT I CHECKED, and how

| check | method |
|---|---|
| the double subtraction | I summed the 12 non-`Typing` phases of `src_L_Condensation.int1.txt` by hand and reached 41,326 ms |
| the residue, three pairs | I ran `agents/tasks/LJ-1-185/residue.py` over its own six tracked runs |
| the four-column fit | I recomputed A, B, C and D from the raw files for all three pairs |
| the counter-examples | I applied the same test to 4 masters and 12 probe repeats across three tasks |
| the D minus C delta | I averaged repeats 2, 3 and 4 of both probes, phase by phase |
| the census | I counted module applications in the master's in-fence lines myself |
| the wing split | I re-added `runs/wing-ratio.txt`'s rows |
| the band's provenance | I read `scripts/check-ratio.py:72-98` |
| **Agda** | **NOT RUN.** Two siblings hold both slots. This review is a reading of the record |

## 10. EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| the 16 s decomposition is a double subtraction | **MEASURED TRUE.** Re-derived, section 1.1 |
| the residue is 17.8 s today | **MEASURED for the run.** Its 2.5 percent spread is within-series and understates the estimator's error, which is 3.8 to 4.5 s at this master on other days |
| the four columns of section 2.7 are independent | **MEASURED FALSE.** `A + C = B + D` by construction |
| the fit has ONE counter-example | **MEASURED FALSE.** Six more, two at the master |
| the billing law holds "wherever they occur" | **MEASURED FALSE** |
| the term "is falling on its own" | **MEASURED FALSE** on the report's own identification. `TypeSig` plus `OccursCheck` ROSE 5.8 percent |
| instantiation is 0.9 percent of the residue | **MEASURED TRUE**, and it survives a tenfold transfer error. The transfer's direction is INFERRED |
| a telescope's price is `DeadCode` | **MEASURED TRUE** |
| no cure could be shown to have worked | **MEASURED FALSE for the instrument.** True only for a before-and-after series design. `OccursCheck` reads to 1.48 percent over three runs |
| the wing band is 24.6 s | **MEASURED FALSE as applied.** The constant is a one-module figure and a sum spreads less |
| a lever on `OccursCheck` is measured anywhere in this repository | **MEASURED FALSE.** I confirm the report. Nothing measures one |
| the brief caused the STOP | **MEASURED.** `LJ-1.185.md:23-27` fixed the design and called it a constraint |
| `Deserialization` gained about 8.3 s at this master in one day | **MEASURED.** The cause is **INFERRED** |
| I edited a master, a brief or a report | **MEASURED FALSE**, none of the three |
| I ran Agda, `make check`, a commit or a push | **MEASURED FALSE**, none of the four |
| I ran `git checkout`, `stash`, `reset --hard` or `clean` | **MEASURED FALSE**, none of the four |

## 11. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-185/`, in full.** **TOOK:** `lj-1.185-report.md` read
  whole; `LJ-1.185.md:8-11` and `:23-27`, the two premises of section 3;
  `gen_probe.py:93-112`, the shape of `Body`'s types, which is the transfer
  weakness in section 1.3; `residue.py:48-79`, the estimator, which I ran
  rather than re-implemented (C-26); `runs/src_L_Condensation.{defs,int}{1,2,3}.txt`,
  the six runs behind every figure; `runs/agents_tasks_LJ-1-185_ProbeLJ1185{B,C,D}.agda.*`,
  24 probe runs; `runs/wing-ratio.txt`, the wing aggregate.
  **I read the probes and the raw runs, not the report's account of them.**
- **`agents/tasks/LJ-1-155/`.** **TOOK:** `lj-1.155-report.md:120-137`, the
  derivation of 21,268 ms, which I re-added;
  `runs/src_L_Condensation.{defs1,int1}.txt`, the two accounts;
  `runs/src_L_Condensation_{TwelveAgree,LowerAgree,UpperAgree}.{defs1,int1}.txt`,
  which are three of the six counter-examples;
  `runs/agents_tasks_LJ-1-155_ProbeLJ1155B1.agda.int1.txt:12-14`, the telescope
  price.
- **`agents/tasks/LJ-1-177/lj-1.177-report.md:259-265`**, the target sentence;
  `:239-257`, the 5.2 s `DeadCode` ceiling; `:281-285`, the WING-LOCAL cone;
  `:308-312`, the 21 s resolution test that the brief then hardened into a
  design constraint.
- **`agents/tasks/LJ-1-145/lj-1.145-report.md:40-79`**, the third
  `L/Condensation` profile pair, which gives the sixth counter-example;
  `:86-100`, the "about 22,000 ms", which uses the PRINTED definition sum and
  so carries the dropped rows; `:189-223`, the P-w refutation.
- **`agents/tasks/LJ-1-159/lj-1.159-report.md:255-266`**, the 8.4 times figure
  the brief cites, and a second example of a within-series paired measurement.
- **`scripts/check-ratio.py:72-98`**, the band, its provenance and the two
  sentences that decide section 2.2 and section 2.3.
- **`dev/PLAN.md:70-83`**, what the campaign now builds on this verdict, and
  `:756-758`, the two task-index rows.
- **`archive/dev/TASKS-archived.md`, `archive/dev/STATUS-archived.md` and
  `archive/src/2026-08-09-rud-route/`: SURVEYED, NOT USED, and I say so rather
  than pad this section.** `[LJ-1.185]:655-661` already searched them for
  `--profile`, `Miscellaneous`, `module application` and `instantiat` and
  reported four hits, all about re-instantiating a proof at a new carrier.
  **My question is narrower than its question**: I needed a second
  `--profile=definitions` and `--profile=internal` PAIR of one module to test
  the billing law. The retired route holds single-account profiles only
  (`archive/dev/measurements/l3.32-t242-profile.txt`), so no pair transfers.
  **No SHAPE from the archive bears on this review.**
- `dev/LESSONS.md`, at each entry: **C-42** (section 5, both directions),
  **C-22** (this file existed before the first check), **P-l** (section 1.3
  refuses to move the probe's per-application price to the master; section 4.3
  keeps the report's own refusal), **C-39 and C-40** (section 3), **D-1** (the
  abort criterion was in the brief and section 0 answers it), **D-10** (section
  1.2 prices the truth of the recorded residue before pricing a cure for it),
  **I-5** (section 4.2).

## 12. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md` and `dev/literature/devlin-errata.md` do not
bear on this review.** I searched both for `profile`, `elaborat`, `cost` and
`Agda`. Every hit is the ordinary English word "second". **The literature
settles nothing that this negative says is unsettled, because every term in
this review is a property of Agda 2.8.0's elaborator and its benchmark
accounts.**
