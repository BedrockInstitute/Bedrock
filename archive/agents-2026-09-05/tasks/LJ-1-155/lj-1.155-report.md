# LJ-1.155 report: there IS a second term, it is in the `*Agree` masters, and its cure is WING-LOCAL

tier: opus (version `override`). Written incrementally (C-22). Every negative
is marked **MEASURED** or **INFERRED**.

**STATUS: COMPLETE. DIAGNOSIS ONLY. No master was edited.** Fourteen probes
are written under `agents/tasks/LJ-1-155/`, all tracked. Nothing was committed
and nothing was pushed.

## 0. THE ANSWER, in one sentence and then five lines

**WE ARE IN BOTH WORLDS AT ONCE, and the split is per master: the three
`*Agree` masters DO have a second term of their own, worth about 21 s, whose
cure is WING-LOCAL and moves the AC baseline by nothing; the 6,554-line
`L/Condensation`, which carries 56 percent of the wing's seconds, does NOT,
and its cost is spread over 335 definitions whose largest is 3.04 percent.**

**AND THE BRIEF'S GAP IS HALF THE REAL ONE. MEASURED: the wing is 209.52 s
over 11,635 lines, 1.97x, and the bar is 0.010514 rather than the brief's
0.0136, which belongs to a baseline `[LJ-1.128]` replaced. The gap is 87 s,
not 44. So a 21 s cure closes 24 percent of it, not half.** Section 7.2.

1. **THE SECOND TERM IS `DeadCode.DeadCodeReachable`, and it is
   `*Agree`-local. MEASURED.** It is **24,469 ms, 39.7 percent** of the three
   `*Agree` masters' 61,633 ms, and the largest phase in all three. In
   `L/Condensation` the same phase is **4.4 percent**.
2. **ITS CAUSE IS THE MODULE TELESCOPE, and the cost transplants. MEASURED.**
   Probe B1 restates `UpperAgree`'s 36 telescope hypotheses verbatim, adds
   eight definitions that do NO work, and costs **5,291 ms with 2,652 ms of
   `DeadCode`** against the master's 11,936 ms with 3,675 ms. **72 percent of
   `UpperAgree`'s `DeadCode` is reproduced with zero mathematics in the file.**
3. **THE CURE IS MEASURED AND IT IS A FACTOR OF 106.** State 35 of the 36 as
   ONE record and `DeadCode` goes **2,652 ms to 25 ms**, the whole file
   **5,291 ms to 2,521 ms, minus 52.4 percent**. Two runs each side, warm-up
   discarded, load 2.9 to 3.1.
4. **ONE NAME WALLS AND ITS FIELD MUST STAY IN THE TELESCOPE: `sucV`, inside
   `sucK`.** As a record field it exhausts an 8 GB heap in 108 s; **remove
   that one token and the same field costs 2.02 s; keep only that token and it
   walls again.** MEASURED from both sides, and the 36-field record walls the
   same way three times over.
5. **THE CURE IS WING-LOCAL. It touches no shared machinery, so it moves the
   AC baseline by ZERO and the ratio can only improve.** That is the column
   `[LJ-1.147]` could not give.

**This fires the brief's first abort criterion: a second term worth double
figures of seconds, with its cure and its price. I stop here.**

## 0.1 Machine load and run count, beside every figure

**I ran ONE agda process at a time throughout, at `GHCRTS="-A64m -I0 -M8g"`,
and never raised the cap.** The harness `agents/tasks/LJ-1-155/measure.py`
REFUSES to start beside another agda binary (`pgrep -x agda`) and it waited
four times for a sibling. **Every raw run is in
`agents/tasks/LJ-1-155/runs/`, with its load before and after in the file
header.**

**A sibling ran Agda during this dispatch and I name it.** `[LJ-1.156]`'s
`ProbeLJ1156D.agda` was PID 30711 at 22:56, seen with `ps -eo pid,command`.
`[LJ-1.154]`'s directory appeared in `git status` at the head of the task.

**The machine was NOT quiet and no measurement can hide it.** At the head of
the task `corespotlightd` held a whole core at 100.7 percent and the 15-minute
load average was 11.29. It fell through the dispatch: load 1m was 5.5 for the
`*Agree` profiles, 4.3 to 5.8 for the master, and **2.8 to 3.1 for the
controlled pair**, which is the only figure a decision rests on.

| run | instrument | load 1m before to after | result |
|---|---|---|---|
| three `*Agree`, `--profile=definitions` | harness | 5.46 to 5.46 | 30.43 / 20.52 / 11.97 s |
| three `*Agree`, `--profile=internal` | harness | 4.92 to 5.73 | 30.63 / 20.26 / 12.15 s |
| `L/Condensation`, `--profile=definitions` | harness | 4.26 to 5.51 | 122.80 s |
| `L/Condensation`, `--profile=internal` | harness | 5.51 to 5.83 | 122.21 s |
| probes A1, A2 | harness | 5.64 to 5.27 | 1.75 / 1.90 s |
| probes B2, B3, B4, B6, B8 | harness | 5.4 down to 2.3 | **HEAP WALL, five times** |
| probes B5, B7, B9, B11 | harness | 4.15 to 4.52 | 2.25 / 1.94 / 2.68 / 2.02 s |
| probe B12 | harness | 3.97 to 4.16 | **HEAP WALL, 106.68 s** |
| **the controlled pair, B1 against B10, three rounds** | harness | **2.77 to 3.05** | **section 4** |

**Every load-bearing figure below is a RATIO INSIDE ONE RUN or a pair taken
back to back on a load that moved by 0.2.** A factor of 106 does not turn on
that.

## 1. THE MASTER, `src/L/Condensation.lagda.md`, re-measured after `[LJ-1.153]`

**The brief said `[LJ-1.153]` added 55 lines. MEASURED: it added 103.**
`scripts/ledger.py` `count` reads **6,554** in-fence lines at HEAD against the
brief's 6,451. **`TwelveAgree` moved further: 309 to 399, plus 90.**
`LowerAgree` 265 to 267 and `UpperAgree` 268 to 270.

### 1.1 The definition profile. MEASURED, cold, one run, 122.80 s wall

`agda --profile=definitions`, own interface moved aside and restored, exit 0,
total **119,663 ms**. Raw: `runs/src_L_Condensation.defs1.txt`.

| bucket | ms | share |
|---|---:|---:|
| **`Miscellaneous`** | **62,594** | **52.3 pc** |
| 335 named definitions | 56,903 | 47.6 pc |
| **largest single definition, `SatGraphAgree.back`** | **3,632** | **3.04 pc** |
| top ten definitions | 18,779 | 15.7 pc |
| top fifty definitions | 43,006 | 35.9 pc |
| the `out`/`back` family, 79 definitions | 29,505 | 24.7 pc |

**MEASURED NEGATIVE: there is NO dominant definition in the master, and the
distribution got FLATTER, not sharper.** `[LJ-1.145]` measured the largest at
7.6 percent before the seal and `[LJ-1.147]` left it at 3.4 s. **Today the
largest is 3,632 ms, 3.04 percent.** Half the check is billed to no name at
all.

**This is the second world, stated exactly.** Cutting the single worst
definition to zero buys 3.6 s of an 87 s gap. Cutting the top TEN to zero buys
18.8 s and there is no cure that does that.

### 1.2 The phase profile. MEASURED, cold, one run, 122.21 s wall

`agda --profile=internal`, exit 0, total **121,115 ms**. Raw:
`runs/src_L_Condensation.int1.txt`.

| phase | ms | share |
|---|---:|---:|
| **`Typing`, all sub-phases** | **79,751** | **65.8 pc** |
| `Typing.CheckRHS` | 33,204 | 27.4 pc |
| `Typing.CheckLHS` | 29,181 | 24.1 pc |
| `Typing.OccursCheck` | 10,978 | 9.1 pc |
| `Typing.TypeSig` | 5,165 | 4.3 pc |
| **`Serialization`** | **18,525** | **15.3 pc** |
| `DeadCode` | 5,297 | **4.4 pc** |
| `Positivity` | 5,021 | 4.1 pc |
| `InterfaceInstantiateFull` | 3,435 | 2.8 pc |
| `Coverage` | 3,332 | 2.8 pc |
| `Parsing` | 2,632 | 2.2 pc |
| `Deserialization` | 1,689 | 1.4 pc |

**The two accounts agree, and the arithmetic locates `Miscellaneous`.** Every
phase that is not `Typing` sums to **41,326 ms**. Against `Miscellaneous` at
62,594 ms that leaves **about 21,268 ms of type-checking outside every
definition**: module telescopes and module-application instantiation.
`[LJ-1.145]` measured "about 22,000 ms" for the same quantity before the seal,
so **the seal did not touch it and it is still there**.

**MEASURED: interface production is 28,946 ms, 23.9 percent** (`Serialization`
18,525 + `DeadCode` 5,297 + `InterfaceInstantiateFull` 3,435 +
`Deserialization` 1,689). `[LJ-1.145]` refused to propose a cure for it and I
refuse too: the interface is **5,426,146 bytes over 6,554 in-fence lines, 828
bytes per line**, against the tree's 1,229 average that `[LJ-1.145]` measured.
**The master is below the tree's mean. This is a floor the repository pays.**

## 2. THE THREE `*Agree` MASTERS, profiled for the first time

### 2.1 The definition profile. MEASURED, cold, one run each

Raw: `runs/src_L_Condensation_*Agree.defs1.txt`. Load 5.46 to 6.79.

| master | lines | total ms | `Miscellaneous` | share | largest named definition |
|---|---:|---:|---:|---:|---|
| `TwelveAgree` | 399 | 29,372 | 22,547 | **76.8 pc** | `twelve-back` 820 ms |
| `LowerAgree` | 267 | 20,202 | 17,409 | **86.2 pc** | `out` 1,003 ms |
| `UpperAgree` | 270 | 11,780 | 9,885 | **83.9 pc** | `out` 520 ms |
| together | 936 | 61,354 | 49,841 | **81.2 pc** | |

**MEASURED NEGATIVE: no `*Agree` master holds an expensive definition.** The
largest across all three is 1,003 ms, 1.6 percent of their seconds. **Four
fifths of their cost is billed to no name.**

### 2.2 The phase profile, and here is the term. MEASURED, cold, one run each

Raw: `runs/src_L_Condensation_*Agree.int1.txt`. Load 4.92 to 6.23.

| phase | `TwelveAgree` | `LowerAgree` | `UpperAgree` | together | share |
|---|---:|---:|---:|---:|---:|
| **`DeadCode.DeadCodeReachable`** | **13,976** | **6,818** | **3,675** | **24,469** | **39.7 pc** |
| `Typing`, all sub-phases | 8,191 | 3,836 | 3,385 | 15,412 | 25.0 pc |
| `InterfaceInstantiateFull` | 972 | 5,500 | 1,253 | 7,725 | 12.5 pc |
| `Deserialization` | 1,735 | 1,718 | 1,704 | 5,157 | 8.4 pc |
| `Coverage` | 3,512 | 667 | 707 | 4,886 | 7.9 pc |
| `Serialization` | 782 | 1,376 | 963 | 3,121 | 5.1 pc |
| `Positivity` | 193 | 52 | 84 | 329 | 0.5 pc |
| total | 29,595 | 20,102 | 11,936 | 61,633 | |

**`DeadCode` is the largest phase in all three, and it is not
type-checking.** Real elaboration, `Typing`, is a quarter of their seconds.
**`DeadCode` plus interface production is 65.7 percent, and none of it is
mathematics.**

**The contrast with the master is the whole finding.** `DeadCode` is 4.4
percent of `L/Condensation` and 39.7 percent of the three `*Agree` masters.
**Same family, same content, one phase, a factor of nine in share.**

## 3. WHAT DRIVES `DeadCode`: the module telescope. MEASURED by transplant

### 3.1 The census

| master | main module | telescope lines | hypotheses | chars | `DeadCode` ms |
|---|---|---:|---:|---:|---:|
| `TwelveAgree` | `AbstractFrame`, `:114` | 175 | 62 | 13,035 | 13,976 |
| `LowerAgree` | `LowerAgree`, `:76` | 113 | 39 | 8,153 | 6,818 |
| `UpperAgree` | `UpperAgree`, `:77` | 103 | 38 | 7,833 | 3,675 |

**The telescope is 38 to 44 percent of each master's in-fence lines**, and it
is prepended to the stored type of EVERY definition inside the module.
`DeadCode.DeadCodeReachable` walks those stored types.

### 3.2 The transplant. MEASURED

**Probe A1** (`ProbeLJ1155A1.agda`), a module with no `L.Condensation` import
and one trivial definition: **774 ms, `DeadCode` absent.**

**Probe A2** (`ProbeLJ1155A2.agda`), `UpperAgree`'s import list at `:21-40`
VERBATIM and the same one trivial definition: **1,778 ms, `DeadCode` still
absent.**

**MEASURED NEGATIVE: `DeadCode` is NOT an import tax.** Importing the
6,554-line master costs 1,004 ms of `Deserialization` and **zero
`DeadCode`**.

**Probe B1** (`ProbeLJ1155B1.agda`), the same imports PLUS `UpperAgree`'s 36
telescope hypotheses, machine-extracted verbatim from `:80-178`, plus eight
definitions that do NO work:

| | probe B1 | `UpperAgree` the master | ratio |
|---|---:|---:|---:|
| total | **5,291 ms** | 11,936 ms | 0.44 |
| **`DeadCode.DeadCodeReachable`** | **2,652 ms** | **3,675 ms** | **0.72** |
| `Typing` | 1,008 ms | 3,385 ms | 0.30 |

**72 percent of `UpperAgree`'s `DeadCode` and 44 percent of its whole check
are reproduced by its TELESCOPE ALONE, in a file that proves nothing.**
The telescope over the A2 floor is **5,291 minus 1,778 = 3,513 ms, 29 percent
of the master's entire check**, for zero mathematics.

**This is P-t at a new site.** An average over 270 lines hides it: the
telescope is 103 of those lines and it carries a third of the seconds.

## 4. THE CURE, MEASURED as a controlled pair

### 4.1 What it is

**State the block ONCE as a record parameter instead of 36 telescope
hypotheses.** This is not my invention: `src/L/Condensation.lagda.md:5996`
already declares `record KFacts` with 27 fields, and the comment above it at
`:5990-5994` states the reason in the repository's own words, "one record, so
a transfer module states the block as ONE parameter and re-elaborates it once
per module instead of once per instantiation site". That is `[LJ-1.62]`.

**The three `*Agree` masters never got it. MEASURED by `grep -c KFacts`:**
`L/Condensation` 26, `LowerAgree` **0**, `TwelveAgree` **0**, `UpperAgree`
**1**, and that one hit is a comment at `:51` saying `sucK` is deliberately
NOT a `KFacts` field.

### 4.2 The controlled pair. MEASURED, two runs each side, warm-up discarded

**`ProbeLJ1155B1.agda`** states the 36 as a telescope.
**`ProbeLJ1155B10.agda`** states 35 of the 36 as ONE record, keeps `sucK` in
the telescope for the reason section 5 measures, and carries **the same eight
definitions byte for byte**. The 36 hypotheses in both files are
machine-extracted from the master by
`agents/tasks/LJ-1-155/gen_record_probe.py`; nothing was retyped.

**Three rounds back to back, the first discarded as the warm-up
(`[LJ-1.148]`). Load 1m 2.77 to 3.05 across all six runs.**

| phase | B1 run 1 | B1 run 2 | B10 run 1 | B10 run 2 | delta of means |
|---|---:|---:|---:|---:|---:|
| **Total** | 5,337 | 5,245 | **2,525** | **2,518** | **-2,770, minus 52.4 pc** |
| **`DeadCode.DeadCodeReachable`** | 2,636 | 2,668 | **25** | **25** | **-2,627, a factor of 106** |
| `Typing`, all | 1,029 | 986 | 639 | 644 | -366 |
| `Coverage` | 504 | 487 | 0 | 0 | -496 |
| `Serialization` | 167 | 172 | 372 | 358 | **+196** |
| `Positivity` | 47 | 47 | 479 | 485 | **+435** |
| `InterfaceInstantiateFull` | 49 | 49 | 136 | 139 | +89 |
| wall seconds | 5.43 | 5.34 | 2.62 | 2.62 | |

**The two runs on each side agree to 1.7 percent and 0.3 percent.** The
instrument is not the source of a factor of 106.

**The record has its OWN fixed cost and I state it rather than net it away:
`Positivity` plus `Serialization` plus `InterfaceInstantiateFull` rise by
720 ms.** That is one record declaration, paid once per master.

### 4.3 The price in seconds. DD8: ONE figure, and here is its basis

**About 21 seconds off the three `*Agree` masters.** Section 7.3 carries the
4.6 percent correction for the profiler's own cost; the arithmetic below is
the profiled figure, 22.1 s, and 20.97 s after that correction.

1. **MEASURED.** `DeadCode` in the three masters is **24,469 ms**
   (section 2.2), three cold runs, one each.
2. **MEASURED.** The controlled pair collapses `DeadCode` by **99.1 percent**,
   2,652 ms to 25 ms, on the same 36 hypotheses (section 4.2).
3. **MEASURED.** The record's own fixed cost is **720 ms per master**, so
   about **2,160 ms** for three.
4. **INFERRED.** 24,469 times 0.991, minus 2,160, is **22.1 s**.

**What step 4 assumes, and it is the analogy P-l forbids as a price:** that
`TwelveAgree`'s 62-hypothesis telescope collapses at the same RATE as
`UpperAgree`'s 36, and `TwelveAgree` carries 13,976 ms of the 24,469. **I
measured the collapse at ONE of the three telescopes.** Section 8 says what
closes it.

**Two upsides I measured but do NOT price**, because the probe's eight
definitions do no work and cannot carry them: `Coverage` fell to zero in the
pair and is 3,512 ms in `TwelveAgree`; `Typing` fell 36 percent in the pair
and is 15,412 ms across the three. **If either transfers the cure is bigger
than 21 s. I claim neither.**

### 4.4 The price in lines. It ADDS lines, and it deletes none

**About 40 in-fence lines added, none deleted. INFERRED from the probe's own
shape.** A record declaration restates the block once, so the three masters
each trade a telescope for a record of the same length plus a `record ... :
Type (ℓ-suc ℓ) where` header and a `field` line, and every use site inside the
module gains a projection.

**P-q and DD24 both hold: nothing is deleted to improve a ratio.** The ratio
improves because the DENOMINATOR grows a little and the NUMERATOR falls 21 s.

## 5. THE WALL, and it is one field. MEASURED five times

**The obvious form of the cure, all 36 as a record, DOES NOT COMPILE. It
exhausts an 8 GB heap.** I hit this wall five times and never raised the cap
(C-12).

| probe | what it declares | verdict |
|---|---|---|
| `ProbeLJ1155B2.agda` | the 36 as a record, plus the `Big` module | **HEAP WALL, 8 GB, 115.17 s** |
| `ProbeLJ1155B3.agda` | B2 plus `no-eta-equality`, ONE line changed | **HEAP WALL, 8 GB, 106.88 s** |
| `ProbeLJ1155B4.agda` | the record declaration ALONE, no consumer | **HEAP WALL, 8 GB, 117.14 s** |
| `ProbeLJ1155B5.agda` | fields 0 to 22, the `KFacts`-shaped block | **GREEN, 2.25 s** |
| `ProbeLJ1155B6.agda` | fields 23 to 35, the satisfaction block | **HEAP WALL, 8 GB, 104.47 s** |
| `ProbeLJ1155B7.agda` | `envK-neg` ALONE, a satisfaction hypothesis | **GREEN, 1.94 s** |
| `ProbeLJ1155B8.agda` | **`sucK` ALONE** | **HEAP WALL, 8 GB, 107.92 s** |
| `ProbeLJ1155B9.agda` | all 36 EXCEPT `sucK` | **GREEN, 2.68 s** |
| `ProbeLJ1155B11.agda` | **`sucK` with `sucV` REMOVED, one token** | **GREEN, 2.02 s** |
| `ProbeLJ1155B12.agda` | **`sucV` alone, every other part removed** | **HEAP WALL, 8 GB, 106.68 s** |

**THE FIELD, stated exactly.** `src/L/Condensation/UpperAgree.lagda.md:152-153`:

```
sucK : (a : S) → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
     → ⟨ sucV (fst a) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
```

**As a module telescope hypothesis it is free. As a record field, alone, it
exhausts 8 GB.**

**MEASURED NEGATIVE: eta is NOT the cause.** B3 changes exactly one line,
`no-eta-equality`, and walls at the same size within 8 percent of the time.

**MEASURED NEGATIVE: the satisfaction hypotheses are NOT the cause.** `envK-neg`
names `envSetAt` and `⊨` and passes in 1.94 s, and all twelve of its
neighbours pass together in B9.

### 5.1 THE TERM IS `sucV`, and it is MEASURED from both sides

**The term is ONE NAME: `sucV`, the cumulative hierarchy's successor
(`Cubical.HITs.CumulativeHierarchy.Constructions.InfinitySet`).** It occurs
exactly once in the 36 hypotheses, inside `sucK`, and `grep -c sucV` proves
it: 1 in probe B1's telescope, and in probe B9's 35 green fields the only hit
is the `open` line.

**Probe B11 is probe B8 with ONE TOKEN CHANGED.** The field's conclusion reads
`⟨ fst a ∈ ... ⟩` where B8 reads `⟨ sucV (fst a) ∈ ... ⟩`. Nothing else
differs.

**Probe B12 removes everything BUT `sucV`**: one field, `(a : S) → ⟨ sucV
(fst a) ∈ fst (lookup (suc⁶ K) γ) ⟩`, no hypothesis at all.

| probe | the field | verdict |
|---|---|---|
| `ProbeLJ1155B8.agda` | `sucK`, as the master writes it | **HEAP WALL, 8 GB, 107.92 s** |
| **`ProbeLJ1155B11.agda`** | **the same, `sucV` removed** | **GREEN, 2.02 s** |
| **`ProbeLJ1155B12.agda`** | **`sucV` and nothing else** | **HEAP WALL, 8 GB, 106.68 s** |

**MEASURED, and no longer inferred: `sucV` in a record field type exhausts an
8 GB heap. Remove that one name and the same field costs 2.02 s. Remove
everything else and keep that one name and it walls again.** Load 3.97 to 4.52
across the three runs.

**Why, and THIS part is INFERRED.** `sucV` is TRANSPARENT where `numeralL`
beside it is `opaque` (`src/L/Axioms/Numerals.lagda.md:97`, measured by
`[LJ-1.145]` section 2.3). **This is P-l's and P-x's class exactly: naming a
transparent construction in a TYPE is what costs**, and a record field type is
elaborated for the record, for its constructor and for its projection, so it
is paid three times over where a telescope pays once.

**The master's own comment already ruled this, and it had no measurement.**
`src/L/Condensation/UpperAgree.lagda.md:49-51`: "sucK is the successor
closure, a telescope fact of the frame, never a KFacts record field (P-x)."
**That sentence is now MEASURED rather than inherited, and this report
supplies the number it never had: 2.02 s against an 8 GB wall.**

**I did NOT revisit P-x.** P-x asks what a DELIVERED record field costs and
`[LJ-1.145]` answered 833 ms at 0.7 percent. This measures what a PROPOSED
record field costs, which is a different question with a different answer, and
it does not disturb that refutation.

## 6. SHARED OR WING-LOCAL, which is the column the owner cannot rule without

| cure | shared or wing-local | what it does to the AC baseline |
|---|---|---|
| **the record on the three `*Agree` telescopes**, about 21 s | **WING-LOCAL** | **NOTHING. Zero.** |
| `[LJ-1.147]`'s seal, for comparison | SHARED | cut it, and made the ratio WORSE |

**MEASURED, and this is why the distinction holds.** The baseline is the
import CLOSURE of `src/Landmarks.lagda.md`, minus the catalogs
(`scripts/check-ratio.py:312-315`). **I computed that closure with the
repository's own function rather than reasoning about it:** 74 masters, and
`grep`-free.

| master | in the AC baseline cone? |
|---|---|
| `src/L/Coding/Graph.lagda.md`, which `[LJ-1.147]` sealed | **YES** |
| `src/L/Choice/Adequate.lagda.md` | **YES** |
| `src/L/Condensation.lagda.md` | **no** |
| `src/L/Condensation/TwelveAgree.lagda.md` | **no** |
| `src/L/Condensation/LowerAgree.lagda.md` | **no** |
| `src/L/Condensation/UpperAgree.lagda.md` | **no** |

**That is the whole difference between this cure and `[LJ-1.147]`'s, in one
table.** The seal landed on a master INSIDE the cone, so it cut the
denominator. This cure lands on three masters OUTSIDE it, so it cannot.

**And nothing outside the three imports them.**
`grep -rn "Condensation.UpperAgree\|Condensation.LowerAgree\|Condensation.TwelveAgree" src/`
returns eight hits: their own three module headers, two imports INSIDE the
group (`src/L/Condensation/TwelveAgree.lagda.md:32` and `:34` import
`LowerAgree` and `UpperAgree`), and three lines of `src/Everything.lagda.md`,
which the catalog ruling of 2026-08-10 excludes from every size figure.

**So this cure changes exactly three files, all three inside the wing, and the
AC baseline cone of `src/Landmarks.lagda.md` contains none of them.** The
denominator of DD24's bar cannot move. **The ratio improves by the full 21 s,
and `[LJ-1.147]`'s sting cannot fire.**

**One consequence to price, and it is inside the wing.** `TwelveAgree`
instantiates the other two, so changing `LowerAgree`'s and `UpperAgree`'s
telescope into a record changes `TwelveAgree`'s instantiation sites as well.
**That is three files, not two, and section 4.4's 40 lines already counts
three.**

**That is the DD4 answer and it is uncomfortable, so I state it plainly.**
`[LJ-1.147]` proved that a SHARED cure serves both trophies and makes the
JUDGED ratio worse. This cure is the opposite on both counts: it serves ONE
trophy, it shares nothing, and it improves the ratio by its whole size.
**DD4 says maximize what the two proofs share. DD24 rewards the cure that
shares nothing.** The owner is not being asked to choose here, because the
telescope-to-record change is a presentation of the wing's own hypothesis
block and there is no AC-side consumer to share it WITH. **But the report
would be dishonest if it did not say that the two rules point in opposite
directions at this site.**

## 7. THE GAP, and what the cure leaves

**Line counts, MEASURED at HEAD by `scripts/ledger.py`, and they moved more
than the brief says.**

| master | brief | HEAD | delta |
|---|---:|---:|---:|
| `L/Condensation` | 6,451 | **6,554** | +103 |
| `L/Cond/TwelveAgree` | 309 | **399** | +90 |
| `L/Cond/LowerAgree` | 265 | **267** | +2 |
| `L/Cond/UpperAgree` | 268 | **270** | +2 |

### 7.1 The wing today. MEASURED, `check-ratio.py --runs 2`, warm-up discarded

Load 3.52 at the head, no other agda process, exit 0, aggregate spread
**0.2 percent**. Raw: `runs/wing-ratio.txt`.

| master | s/line | lines | seconds | 2-run spread |
|---|---:|---:|---:|---:|
| `L/Condensation` | 0.0179 | 6,554 | **117.61** | 0.2 pc |
| `L/Cond/LowerAgree` | 0.0721 | 267 | 19.24 | 1.2 pc |
| `L/Cond/TwelveAgree` | 0.0701 | 399 | 27.96 | 0.1 pc |
| `L/Cond/UpperAgree` | 0.0429 | 270 | 11.58 | 0.0 pc |
| the eight others | | 4,145 | 33.13 | |
| **WING AGGREGATE** | **0.0180** | **11,635** | **209.52** | **0.2 pc** |

**The three `*Agree` masters are 58.78 s, 28.1 percent of the wing**, over 8.0
percent of its lines. **The brief's 28 percent is confirmed on today's tree.**

### 7.2 THE BRIEF'S BAR IS STALE, and the gap is TWICE what it says

**MEASURED, from the tool's own first line.** `check-ratio.py` prints "AC
baseline 0.0091 s/line | tolerance 1.15x | **bar 0.0105 s/line**".

**The brief gives baseline 0.009143 and bar 0.0136. Those two numbers do not
belong to each other.** 0.0136 divided by 1.15 is **0.011826**, which is the
baseline `[LJ-1.147]` recorded and `[LJ-1.128]` replaced. The live pair is
0.009143 and **0.010514**.

| | the brief | MEASURED today |
|---|---:|---:|
| baseline | 0.009143 | 0.009143 |
| bar at 1.15x | 0.0136 | **0.010514** |
| wing seconds | 199.50 | **209.52** |
| wing lines | 11,438 | **11,635** |
| on-bar seconds | 155.6 | **122.34** |
| **the gap** | **44 s** | **87.18 s** |
| the ratio | 1.91x | **1.97x** |

**So the wing is 87 s over, not 44.** The brief's 1.91x was right, because it
divided by the BASELINE; its 44 s was wrong, because it multiplied by the OLD
bar. **A ratio and a gap computed from two different baselines cannot both be
true, and the owner must not fund against the smaller one.**

### 7.3 What the cure does, and what it does NOT do

**About 21 s, and it closes 24 percent of the gap. Not half.**

The 22 s of section 4.3 is measured under `--profile=internal`, which costs
about 4.6 percent: the three masters read 61,633 ms profiled and 58,780 ms
unprofiled. Scaling the `DeadCode` term by 0.954 and keeping the record's own
720 ms per master gives **20.97 s**.

| | seconds | lines | s/line | against the bar |
|---|---:|---:|---:|---:|
| today | 209.52 | 11,635 | 0.0180 | **1.97x** |
| after the cure, INFERRED | 188.55 | 11,675 | 0.01615 | **1.77x** |

**The wing still misses the bar by 66 s. The cure is craft and it is real, and
it does not decide the DD24 question.**

**The other 66 s is `L/Condensation`, and section 1 measured that it has no
term left to name:** 335 definitions, largest 3.04 percent, half the check
billed to no name at all. **On that master we are in the second world and the
ruling stays unavoidable.**

## 8. THE WIDEST UNMEASURED TERM, which DD8 requires me to name

**Whether `TwelveAgree`'s 62-hypothesis telescope collapses at `UpperAgree`'s
rate.** It carries **13,976 ms of the 24,469**, 57 percent of the whole
saving, and I measured the collapse on `UpperAgree`'s 36. **Its telescope is
72 percent longer and its `DeadCode` is 3.8 times larger, which is
super-linear**, so the rate may be better or worse and I will not guess.

**How to close it cheaply:** run `gen_record_probe.py` against
`TwelveAgree`'s telescope instead of `UpperAgree`'s, then B1 against B10 once
more. **Two probe runs, under a minute of Agda, and the whole 21 s becomes
MEASURED.** The generator already takes a field range and an exclusion list.

**Second unmeasured term:** whether any of the other 61 `TwelveAgree`
hypotheses walls as a record field the way `sucK` does. **I bisected
`UpperAgree`'s 36 and found exactly one. `TwelveAgree`'s telescope contains
`sucK` too**, and 26 hypotheses `UpperAgree` does not have. Each wall costs
about 110 s to find.

## 8.5 THE LAW THIS MEASURES, for the orchestrator to number or refuse

**Proposed law. A long module telescope is paid once per definition, and the
bill arrives in `DeadCode`, not in `Typing`.**

Agda prepends a parameterised module's whole telescope to the stored type of
every definition inside it. `DeadCode.DeadCodeReachable` then walks those
stored types. **So a module with T hypotheses and D definitions pays about
T times D, and the profiler bills none of it to a definition name**: it shows
up as `Miscellaneous` in `--profile=definitions` and as `DeadCode` in
`--profile=internal`. **A rate over the file's lines cannot see it, because
the telescope is 38 to 44 percent of those lines and carries a third of the
seconds.**

**The action.** State the block ONCE as a record parameter. **The cure is
measured at a factor of 106 on the phase and 52 percent on the file**
(section 4.2).

**The exception, and it has its own measurement.** **A record field type may
not name a transparent construction of the ambient set theory.** `sucV` in a
field type exhausts an 8 GB heap; the same hypothesis in a telescope is free
(section 5.1, three probes, both directions). **So the block splits: the facts
go in the record and the closure operators stay in the telescope.**

**Why this is a law and not a note.** It says WHERE to look when a master's
seconds are billed to no definition, it names the phase that proves it
(`DeadCode`, not `Typing`), it gives the cure, and it gives the cure's own
failure mode with the token that triggers it. **P-t is the parent**: P-t says
the formula decides the content class, and this says the TELESCOPE decides how
many times that formula is elaborated.

**The measurement, 2026-08-13, `[LJ-1.155]`, on the delivered tree:**

| | telescope | record |
|---|---:|---:|
| `DeadCode.DeadCodeReachable`, 36 hypotheses, 8 definitions | 2,652 ms | **25 ms** |
| the whole probe file | 5,291 ms | **2,521 ms** |
| `sucK` as a field, with `sucV` | n/a | **8 GB WALL** |
| `sucK` as a field, `sucV` removed | n/a | **2.02 s** |

## 9. LITERATURE (DD18)

**Nothing in the literature governs elaboration cost.** The term measured here
is a property of Agda 2.8.0's dead-code pass and its conversion checker.

## 10. ARCHIVE USED

- **`agents/tasks/LJ-1-145/lj-1.145-report.md`, read WHOLE.** **TOOK:** the
  method at `:40-41`, `--profile=definitions` cold with the interface moved
  aside, which is what `measure.py` calls; the transplant law at `:229-247`,
  which is probe B1; the two refutations at `:102-153` and `:189-228`, which I
  did NOT revisit; `:371-374`, "there is no single dominant definition", which
  section 1.1 re-measures on today's tree and finds FLATTER; `:376-381`, the
  interface-production floor and the 1,229 bytes-per-line tree average, which
  is why section 1.2 proposes no cure for `Serialization`; `:139-141`, that
  `numeralL` is `opaque`, which is the contrast that makes `sucV` the suspect
  in section 5.
- **`agents/tasks/LJ-1-147/lj-1.147-report.md`, read WHOLE.** **TOOK:** the
  ratio finding at `:407-434`, that a shared cure helps the baseline more per
  line than the wing, which is the whole of section 6; the AFTER phase account
  at `:384-390`, "the largest remaining term is still not a definition", which
  section 1 confirms; `:396-406`, the three candidates it priced NONE of, of
  which candidate 3 is `TwelveAgree` and is where this task found the term;
  `:552-555`, that the seal did not change the three `*Agree` masters, which
  is why their seconds are the wing's untouched territory; `:156-158`, the
  measured line deltas, which is the caliber for section 4.4.
- `agents/tasks/LJ-1-153/lj-1.153-report.md:1-80`. **TOOK:** the repair of 20
  rule-1 flags across the four masters, and that its edits shift
  `L/Condensation` down by 43 lines from `:2731`. **Its line figure is what
  section 7 re-measures: 103 lines to `L/Condensation` and 90 to
  `TwelveAgree`, not 55.**
- **`dev/LESSONS.md`, read whole at each entry.** P-t at `:2619`, **TOOK** the
  rule that an average hides the term, which is section 3.1: the telescope is
  38 to 44 percent of the lines and a third of the seconds. P-q at `:2651`,
  **TOOK** the refusal to delete lines for a ratio, which is why section 4.4
  adds 40 and removes none. P-l at `:2323`, **TOOK** two things: that a
  measured cure does not transfer by analogy, which is why section 8 names
  `TwelveAgree` as unmeasured, and that naming a transparent construction in a
  TYPE is what costs, which is section 5's inferred mechanism. P-s at `:2587`,
  **TOOK** the refusal to divide a slice rate, which is why section 4.3's step
  4 is marked INFERRED. P-m at `:2478`, the content classes. P-w at `:3112`
  and P-x at `:3582`, read so I would not revisit them, and I did not. C-12 at
  `:2093`, one process at the cap, and the wall reported as a wall. C-22 at
  `:2255`, the incremental deliverable. D-1 at `:1038`, the probe doctrine and
  its abort criterion fixed in advance. R-40 at `:929`, **TOOK** that a deep successor
  chain normalizes super-linearly, which is the first thing I looked for in
  `sucK` and is NOT what section 5 measured, because the other fields carry
  chains fourteen deep and pass.
- **`dev/PLAN.md` DD24, read whole.** **TOOK:** the bar is a ratio so the
  content must be the same KIND of content, which is why nothing is deleted;
  and that the baseline belongs to ONE tree, which is section 6.
- `dev/ledger.toml:2730`, `ac_baseline_module_rate = 0.009143`; `:2992`,
  `tolerance = 1.15`; `:3037-3060`, the twelve-master `gch_wing` list;
  `:2632`, the caliber `-A64m -I0 -M8g`. **TOOK:** all four, and section 6
  uses the wing list to prove the three masters are leaves.
- `scripts/check-timing.py:217-276`, `time_module`. **TOOK:** the cold
  protocol, which `measure.py` calls rather than copies (C-26).
- `scripts/ledger.py:126-143`, `count`. **TOOK:** the in-fence caliber, which
  is section 7's line table.
- `src/L/Condensation.lagda.md:5990-6032`, the `KFacts` record and the comment
  above it. **TOOK:** the repository's own statement of why a record beats a
  telescope, which is `[LJ-1.62]` and is section 4.1.
- `src/L/Condensation/UpperAgree.lagda.md:49-51`. **TOOK:** the comment ruling
  `sucK` out of `KFacts`, which section 5 now measures rather than inherits.
- `scripts/check-probes.py:1-40`. **TOOK:** the probe's home, tracked and
  never deleted.

## 11. THE PROBES

Fourteen files, tracked, beside this report, under `agents/tasks/LJ-1-155/`.
Two generators, `measure.py` and `gen_record_probe.py`, both tracked.

| file | question | verdict |
|---|---|---|
| `ProbeLJ1155A1.agda` | what does a module with no `L.Condensation` cost? | 774 ms, no `DeadCode` |
| `ProbeLJ1155A2.agda` | is `DeadCode` an import tax? | **NO. 1,778 ms, no `DeadCode`** |
| `ProbeLJ1155B1.agda` | does the TELESCOPE drive `DeadCode`? | **YES. 2,652 ms of 5,291** |
| `ProbeLJ1155B2.agda` | does the record cure it? | **HEAP WALL** |
| `ProbeLJ1155B3.agda` | is eta the wall? | **NO. Walls with `no-eta-equality`** |
| `ProbeLJ1155B4.agda` | is the wall the record DECLARATION? | **YES** |
| `ProbeLJ1155B5.agda` | do the 23 `KFacts`-shaped fields wall? | **NO. 2.25 s** |
| `ProbeLJ1155B6.agda` | do the 13 site fields wall? | **YES** |
| `ProbeLJ1155B7.agda` | does a satisfaction field wall? | **NO. 1.94 s** |
| `ProbeLJ1155B8.agda` | does `sucK` ALONE wall? | **YES. 8 GB, 107.92 s** |
| `ProbeLJ1155B9.agda` | do the other 35 pass? | **YES. 2.68 s** |
| `ProbeLJ1155B10.agda` | **the cure, against B1, controlled** | **`DeadCode` 2,652 to 25** |
| `ProbeLJ1155B11.agda` | is `sucV` the wall? one token removed | **YES. GREEN, 2.02 s** |
| `ProbeLJ1155B12.agda` | is `sucV` ALONE enough to wall? | **YES. 8 GB, 106.68 s** |

## 12. NEGATIVES, classified as the brief asks

- **A second dominant DEFINITION anywhere in the family: DOES NOT EXIST.
  MEASURED.** 335 definitions in the master, largest 3.04 percent, top ten
  15.7 percent. Three `*Agree` masters, largest 1,003 ms of 61,633.
  **I profiled every definition in all four masters, cold, at the ledger
  caliber. That is how deep I went.**
- **A second dominant TERM: IT EXISTS, and it is a PHASE rather than a place.
  MEASURED.** `DeadCode.DeadCodeReachable`, 24,469 ms, 39.7 percent of the
  three `*Agree` masters.
- **`DeadCode` as an import tax: REFUTED. MEASURED.** Probe A2 imports the
  6,554-line master and pays zero.
- **The record cure in its obvious form: WALLS. MEASURED, five times, at 8 GB
  and 104 to 117 s each.**
- **Eta as the cause of the wall: REFUTED. MEASURED.** Probe B3, one line
  changed.
- **The satisfaction hypotheses as the cause of the wall: REFUTED. MEASURED.**
  Probe B7 green, probe B9 green over 35 fields.
- **`sucV` as the WALL: MEASURED, from both sides.** Probe B11 removes that
  one token and the field costs 2.02 s; probe B12 keeps only that token and
  walls at 8 GB. **Why `sucV` costs, as opposed to that it costs: INFERRED.**
  It is transparent where `numeralL` beside it is `opaque`.
- **The 21 s price at `TwelveAgree` and `LowerAgree`: INFERRED.** Measured at
  `UpperAgree`'s telescope only. Section 8.
- **`Coverage` and `Typing` savings: UNMEASURED and NOT priced.** The probe's
  eight definitions do no work.
- **Interface production as a curable term: REFUTED again. MEASURED.** 828
  interface bytes per in-fence line against the tree's 1,229 mean.
- **P-x and P-w: NOT REVISITED.** Section 5 measures a PROPOSED record field,
  which is a different question.

## 13. WHAT I DID NOT DO

- **I did not edit any master.** `git status` shows only
  `agents/tasks/LJ-1-155/` and the sibling's `agents/tasks/LJ-1-154/`.
- **I did not commit and did not push.**
- **I did not run `make check`.** The brief reserves it.
- **I did not build the cure in the masters.** This is a diagnosis and the
  cure lives in a probe, as the brief requires.
