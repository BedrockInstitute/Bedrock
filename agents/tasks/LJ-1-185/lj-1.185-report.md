# LJ-1.185 report: the 16 seconds billed outside every definition

tier: opus (version `override`). Written incrementally (C-22). Every negative
is marked **MEASURED** or **INFERRED**.

**STATUS: COMPLETE. A REFUTATION AND A STOP.** No master was edited. Nothing
was committed and nothing was pushed. I did not run `make check`. Four probes,
all GREEN, all under `agents/tasks/LJ-1-185/`.

## 0. LEAD

**THE 16 SECONDS DOES NOT EXIST, AND THE TERM THAT DOES EXIST IS NOT WHAT
`[LJ-1.177]` SAYS IT IS. Both are MEASURED, and the second one is the finding.**

### 0.1 The accounting, in five lines

| | |
|---|---|
| **the 16 s** | **MEASURED FALSE.** It is `21,268 - 5,297` where the 5,297 ms of `DeadCode` was ALREADY subtracted to reach the 21,268. **A double subtraction.** Section 1.3 |
| **what the residue really is, in size** | **17.8 s** today, three kept cold pairs, spread 2.5 percent, load 3.0 to 3.9. Section 2.6 |
| **what the residue really is, in kind** | **`Typing.OccursCheck` 11.75 s and `Typing.TypeSig` 5.14 s: 95 percent of it.** Metavariable solving and signature elaboration. Section 2.7 |
| **module-application instantiation** | **REFUTED, MEASURED. It is 0.9 percent of the residue.** Probe D prices 136 applications at 2,151 ms, and **93 percent of that is billed to `DeadCode` and `Serialization`**, which the residue excludes by construction. Section 2.9 |
| **module telescope elaboration** | **REFUTED, MEASURED**, by `[LJ-1.155]`'s own tracked raw files: a 36-hypothesis telescope bills 2,822 ms of `DeadCode` against 1,091 ms of all `Typing`. Section 2.4 |

### 0.2 The verdict against the brief's own abort criteria

**IDENTIFIED AND NOT CURABLE. Section 3.3 is the whole argument and it is
arithmetic, not opinion.**

**The entire residue is 17.8 s. The wing measures 192.41 s today, so its noise
band is about 24.6 s.** A cure that removed one hundred percent of this term
could not be shown to have worked by one pair of runs, and no partial cure can
be either. **`[LJ-1.177]` set that test itself; this term fails it.**

**AND THE GAP IS LARGER THAN ANYONE THOUGHT.** The wing sits **56 to 67 s**
above DD24's bar today, n=2, against `[LJ-1.177]`'s 44 s. **So the residue is
27 to 32 percent of the gap even if it were free.** Section 5.

**AND THE TWO CANDIDATES `[LJ-1.177]` KEPT APART ARE ONE.** It capped the
`DeadCode` lever at about 5.2 s and named the residue as a SEPARATE, larger
candidate. **The module machinery it named as the residue's cause is billed to
`DeadCode` and `Serialization`. It sits inside the 5.2 s ceiling that report
already measured, not beside it.** So the wing does not have two remaining
levers of 5 s and 16 s. **It has one measured ceiling of about 5 s, and a 17.8 s
term whose cause is ordinary elaboration with no measured lever at all.**

### 0.3 What I would tell the orchestrator in one sentence

**The GCH wing is intrinsically this expensive, the instrument cannot resolve
any cure this wing still has available, and the brief's premise that a
measurable lever remained is MEASURED FALSE.**

## 1. THE ACCOUNTING, from `[LJ-1.155]`'s own tracked raw files

**MEASURED, and it needs no Agda.** `[LJ-1.155]` left both raw profiles in the
tree. I re-read them and re-did the arithmetic.

| file | what it holds |
|---|---|
| `agents/tasks/LJ-1-155/runs/src_L_Condensation.defs1.txt` | `--profile=definitions`, cold, total **119,663 ms**, `Miscellaneous` **62,594 ms** |
| `agents/tasks/LJ-1-155/runs/src_L_Condensation.int1.txt` | `--profile=internal`, cold, total **121,115 ms**, `Typing` **79,751 ms** |

### 1.1 The two accounts are COMPLETE, so the subtraction is legitimate

- The internal account prints `Miscellaneous` at **45 ms**. Every other
  millisecond carries a phase name.
- The definitions account prints 335 named rows summing to **56,903 ms**.
  With `Miscellaneous` at 62,594 that is 119,497 of the 119,663 total. **The
  166 ms difference is the rows Agda drops below its print threshold.**

**So `Miscellaneous` in the definitions account is a REAL measurement of the
time that no definition owns**, and it is not an artefact of dropped rows.

**Today's runs drop more: 2,151 ms of 125,512, which is 1.7 percent.** That
does not touch the residue, because the residue is computed from
`Miscellaneous`, which is an account Agda prints, and never from the sum of the
printed definition rows.

### 1.2 The residue is TYPING, and `DeadCode` is NOT in it

Non-`Typing` phases are `121,115 - 79,751 = 41,364 ms`. The two runs differ by
1,452 ms, 1.2 percent, so the quantity is taken as a DIFFERENCE OF TWO
FRACTIONS, each inside its own run. A uniform slowdown of one run then cancels:

```
p = Miscellaneous(defs) / Total(defs)   = 62,594 / 119,663 = 52.31 pc
q = (Total - Typing)(int) / Total(int)  = 41,364 / 121,115 = 34.15 pc
Typing billed outside every definition  = p - q = 18.16 pc = 21,726 ms
```

**I state one caution against my own arithmetic. `p - q` is ONE derivation, not
two.** Writing it as `Typing - definition sum` gives the same number by
algebra, so the agreement between the two spellings is not independent
evidence. **What the two spellings do check is that both accounts are
complete**, and section 1.1 measures that they are.

### 1.3 THE 16 SECONDS IS A DOUBLE SUBTRACTION. MEASURED FALSE

`[LJ-1.177]:259-265` reads:

> about **21,268 ms** of this master's type-checking is billed outside every
> definition, and `DeadCode` is only 5,297 ms of it. **The other 16 s is
> module telescope elaboration and module-application INSTANTIATION.**

**`DeadCode` is not 5,297 ms OF the 21,268 ms. It was already taken OUT of it.**
`[LJ-1.155]:134-137` builds the 21,268 by subtracting **every phase that is not
`Typing`** from `Miscellaneous`, and `DeadCode` is one of those phases
(`src_L_Condensation.int1.txt:20-21`). Subtracting it a second time removes it
twice.

| statement | class |
|---|---|
| the residue is about 21.3 s | **MEASURED TRUE** |
| `DeadCode` is 5,297 ms **of** that residue | **MEASURED FALSE.** `DeadCode` is in the 41,364 ms of non-`Typing` phases that were subtracted to REACH the residue |
| **there is a separate 16 s term** | **MEASURED FALSE. The 16 s does not exist.** It is `21,268 - 5,297` with the 5,297 already gone |

**So on `[LJ-1.155]`'s tree the quantity was 21.7 s, and no separate 16 s term
was ever there.** Section 2.6 re-measures it on today's tree at 17.8 s.

## 2. WHAT THE TIME IS

### 2.1 The instrument refuses the joint account. MEASURED

**Agda 2.8.0 will not take two profile kinds in one run.**

```
$ agda --profile=internal --profile=definitions <file>
Error: Cannot use profiling option 'definitions' with 'internal'
$ agda --profile=internal --profile=modules <file>
Error: Cannot use profiling option 'modules' with 'internal'
```

Raw: `agents/tasks/LJ-1-185/ProbeLJ1185A.agda` and section 8. **So the
cross-run subtraction is the ONLY method the tool allows, and every residue
figure in this family carries the run-to-run difference as its floor.**

### 2.2 `--profile=modules` does not locate an inner module. MEASURED

`agents/tasks/LJ-1-185/runs/src_L_Condensation_UpperAgree.mod1.txt`, cold,
exit 0, 6.57 s wall, load 4.64 to 4.43:

```
Total                     5,574ms
Miscellaneous             1,752ms
L.Condensation.UpperAgree 3,822ms
```

**`--profile=modules` bills per FILE, not per inner module.** `UpperAgree` holds
three inner module headers and eight module applications and none of them gets a
row. **MEASURED: the third account cannot locate the residue either.**

### 2.3 Module-application copies are billed to NO definition. MEASURED

The master holds **136 module applications** under 54 distinct aliases
(`agents/tasks/LJ-1-185/` census, in-fence lines only). **No row in the 335-row
definitions profile passes through any of those aliases.** So `applySection`'s
work is billed to no definition at all. **That makes instantiation ELIGIBLE for
the residue. Whether it REACHES the residue turns on which PHASE it is billed
to, and section 2.9 measures that.**

### 2.4 The same residue at the three `*Agree` masters. MEASURED

Same arithmetic, same tracked raw files, `[LJ-1.155]` runs:

| master | check ms | Typing outside definitions | share | telescope then | module applications |
|---|---:|---:|---:|---:|---:|
| `L/Condensation` | 119,663 | **21,726** | **18.2 pc** | 588 hypotheses over 99 headers | **136** |
| `TwelveAgree` | 29,372 | 1,304 | 4.4 pc | **62** in one header | 3 |
| `LowerAgree` | 20,202 | 1,062 | 5.3 pc | 39 in one header | 8 |
| `UpperAgree` | 11,780 | 1,446 | 12.3 pc | 38 in one header | 8 |

**MEASURED NEGATIVE: a wide telescope does NOT produce a large
Typing-outside-definitions term.** `TwelveAgree` carried the widest telescope in
the whole wing, 62 hypotheses over 175 lines, and its residue is 1.3 s.

**And `[LJ-1.155]`'s own transplant says why.** Probe B1 restates 36 telescope
hypotheses with eight definitions that do no work
(`runs/agents_tasks_LJ-1-155_ProbeLJ1155B1.agda.int1.txt`): **`DeadCode` 2,822 ms
and `Typing` 1,091 ms in total.** **A telescope's price is `DeadCode`, which is
NOT in the residue.**

### 2.5 The module-application half was already refuted at this master

`[LJ-1.145]:207-223`, a controlled pair inside one probe run:

| spelling | ms |
|---|---:|
| through `module SG = SatGraphAgree ...` | **10** |
| the same definition applied directly, NO module application | **23** |

**C-42 applies and I state it rather than hide it: that refutation measured ONE
site with ONE application.** It does not price 136 of them. Section 2.9 measures
the aggregate.

### 2.6 THE RESIDUE RE-MEASURED TODAY, three cold pairs. MEASURED

Six cold runs of `src/L/Condensation.lagda.md` at 6,676 in-fence lines, under
`GHCRTS="-A64m -I0 -M8g"`, one agda process, cap never raised. **The pairs are
INTERLEAVED**, so machine drift moves both accounts together. Raw:
`agents/tasks/LJ-1-185/runs/src_L_Condensation.{defs,int}{1,2,3}.txt`.

**A fourth pair was planned and I stopped it, and section 8 says why.** A
sibling held the machine from 09:29, my harness waited rather than contended,
and I kept three pairs rather than queue a fourth behind it. **All three pairs
ran on a quiet machine and each run is cold by construction, because the
harness moves the interface aside every time. So none of the three is a
warm-up and I discard none of them.**

| pair | defs total | int total | wall s | load 1m | Misc(defs) | Typing | **residue** | share |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 125,512 | 134,223 | 128.6 / 135.1 | 3.04 to 3.54 | 66,160 | 82,212 | **18,133** | 13.96 pc |
| 2 | 127,051 | 133,718 | 129.3 / 134.6 | 3.54 to 3.19 | 66,038 | 82,355 | **17,688** | 13.62 pc |
| 3 | 131,311 | 132,444 | 133.5 / 133.3 | 3.19 to 3.45 | 68,634 | 80,990 | **17,696** | 13.42 pc |

**Mean 17,839 ms, spread 2.5 percent over three pairs.** Pair 3's two runs agree
to 0.86 percent, and there the unscaled and the scaled subtraction give 17,180
and 17,620, so the scaling is not carrying the result.

**MEASURED: the residue is 17.5 to 18.1 s today, not 21.3 s and not 16 s.**
The share fell from `[LJ-1.155]`'s 18.2 percent to 13.6 percent because today's
non-`Typing` block is larger: `Deserialization` reads **9,955 ms** against
1,689 ms in `[LJ-1.155]`'s run, on a tree whose dependencies have since been
rebuilt.

**THE TERM HAS BEEN MEASURED THREE TIMES AND IT IS FALLING ON ITS OWN.**

| when | Typing outside every definition | master lines |
|---|---:|---:|
| `[LJ-1.145]`, 2026-08-13 | **22.2 s** (its own words: "about 22,000 ms") | 6,451 |
| `[LJ-1.155]`, 2026-08-13 | **22.7 s** | 6,554 |
| **this report, 2026-08-14** | **17.8 s** | **6,676** |

**The drop of about 5 s is outside the instrument's band on a 22 s quantity,
which is +-2.8 s. Nobody targeted it.** `[LJ-1.173]` and `[LJ-1.176]` edited
this master between the second row and the third. **I mark the CAUSE INFERRED,
because I did not bisect it. The three figures themselves are MEASURED.**

**One fairness note against my own refutation.** `[LJ-1.177]`'s derivation of
the 16 s is arithmetically wrong, and its MAGNITUDE is still within 10 percent
of today's measured 17.8 s. **The number was nearly right by accident. The
reasoning behind it was not, and section 2.7 shows the reasoning is what led
the identification astray.**

### 2.7 WHAT THE RESIDUE IS. MEASURED, and it is NOT module machinery

**The definitions account and the internal account line up phase by phase, and
they do it three times.**

| pair | definition sum / total | `CheckLHS`+`CheckRHS` / total | residue / total | `TypeSig`+`OccursCheck`+bare `Typing` / total |
|---:|---:|---:|---:|---:|
| 1 | **47.29 pc** | **47.54 pc** | **13.96 pc** | **13.71 pc** |
| 2 | **48.02 pc** | **47.81 pc** | **13.62 pc** | **13.78 pc** |
| 3 | **47.73 pc** | **47.49 pc** | **13.42 pc** | **13.66 pc** |

**Every row agrees to 0.25 percentage points, in three independent pairs.**

**MEASURED CONCLUSION: `--profile=definitions` bills `Typing.CheckLHS` and
`Typing.CheckRHS` to definitions, and bills `Typing.TypeSig` and
`Typing.OccursCheck` to NO definition.** So the residue has a name:

| phase | pair 3 ms | share of the residue |
|---|---:|---:|
| **`Typing.OccursCheck`** | **11,750** | **66 pc** |
| **`Typing.TypeSig`** | **5,135** | **29 pc** |
| bare `Typing`, no sub-phase | 1,202 | 7 pc, **and see the caution below** |
| sum | **18,087** | against a measured residue of 17,696 |

**`Typing.OccursCheck` is two thirds of the term.** That is metavariable
solving. **It is not module telescope elaboration and it is not
module-application instantiation.**

**A CAUTION AGAINST MY OWN FIT, and I found the counter-example rather than
stopping at the three that agreed.** The same test on `TwelveAgree`'s tracked
pair does NOT fit: its definition sum is **23.2 percent** of its check while
its `CheckLHS`+`CheckRHS` is **9.3 percent**, and its bare `Typing` alone is
**16.8 percent**. **So bare `Typing` CAN be billed inside a definition, and my
seven-percent row is the uncertain one.**

**The finding survives the caution, because the two large rows do not depend on
it.** `TypeSig` and `OccursCheck` are outside every definition at all three
sites tested. **They are 16,885 ms of a 17,696 ms residue: 95 percent.**

### 2.8 THE CONTROLLED PROBE SERIES. MEASURED, three kept pairs each

**Three spellings of the same file, generated by
`agents/tasks/LJ-1-185/gen_probe.py`, each read twice and repeated four times.
Repeat 1 is discarded. All GREEN, exit 0, one agda process, load 2.90 to 3.42.**

| probe | shape | total ms | residue ms | residue share |
|---|---|---:|---:|---:|
| **B** | definitions at file level. **NO module header, NO module application** | 1,222 | **35** | **2.9 pc** |
| **C** | the same content under a **24-hypothesis telescope**, 0 applications | 91 | 69 | 66 pc, on a 91 ms file |
| **D** | C plus **136 module applications**, the master's own count | 2,248 | **216** | 9.6 pc |

**PROBE B SETS THE INSTRUMENT'S FLOOR AND CONFIRMS THE BILLING LAW.** Its
definition sum is **1,170 ms** and its `Typing.CheckRHS` is **1,164 ms**. **The
`Definition` account and `CheckLHS`+`CheckRHS` are the same quantity here too,
at a third site.** Its residue is 2.9 percent, because it has no measurable
`TypeSig` and no measurable `OccursCheck`.

### 2.9 WHAT 136 MODULE APPLICATIONS ACTUALLY COST. MEASURED

Probe D minus probe C, mean of three kept pairs, `--profile=internal`:

| phase | delta ms | per application | share of the delta |
|---|---:|---:|---:|
| **`DeadCode.DeadCodeReachable`** | **+986** | 7.25 | **46 pc** |
| **`Serialization`** | **+785** | 5.77 | **36 pc** |
| `InterfaceInstantiateFull` | +166 | 1.22 | 8 pc |
| **`Typing`, ALL sub-phases** | **+152** | **1.12** | **7 pc** |
| `Parsing`, `Scoping`, `Deserialization` | +59 | 0.43 | 3 pc |
| **total** | **+2,151** | **15.81** | |

**MEASURED: module-application instantiation is real and it costs about 15.8 ms
per application, and 93 percent of that price is billed OUTSIDE `Typing`.** It
goes to `DeadCode`, to `Serialization` and to `InterfaceInstantiateFull`.

**THE RESIDUE EXCLUDES ALL THREE BY CONSTRUCTION**, because the residue is
`Miscellaneous(defs)` minus every non-`Typing` phase.

**So at the master's 136 applications, instantiation puts about 152 ms into a
17,800 ms residue. That is 0.9 percent.**

**THE TRANSFER IS CONSERVATIVE, and P-l says to state the basis rather than
assume it.** Probe D's `Body` carries **24 parameters and 24 definitions**, so
every application copies 24 types that each name all 24 parameters. **The
master's applied modules are SMALLER**: `EnvSet` has 17 signatures over 134
lines, `BinFormAgree` 18, `UnFormAgree` 15, `BinFrameAgree` 11, `TmAgree` 8,
`RowTransfer` 6 and `BinFullDecode` 4. **So the probe overstates the master's
per-application price, and the 0.9 percent is an upper bound rather than a
central estimate.**

### 2.10 THE VERDICT ON `[LJ-1.177]`'s IDENTIFICATION

| `[LJ-1.177]` said | class |
|---|---|
| there is a residue billed outside every definition | **MEASURED TRUE.** 17.8 s today, three kept pairs |
| it is **16 s** | **MEASURED FALSE as arithmetic**, a double subtraction. **The magnitude is within 10 percent of the truth by accident** |
| `DeadCode` is 5,297 ms **of** it | **MEASURED FALSE.** `DeadCode` was already subtracted out |
| it is **module telescope elaboration** | **MEASURED FALSE.** `[LJ-1.155]`'s probe B1 puts a 36-hypothesis telescope's price in `DeadCode`, 2,822 ms against 1,091 ms of `Typing` |
| it is **module-application INSTANTIATION** | **MEASURED FALSE.** Probe D prices 136 applications at 2,151 ms, of which 152 ms is `Typing`. **0.9 percent of the residue** |
| **what it actually is** | **`Typing.OccursCheck` 66 pc, `Typing.TypeSig` 29 pc, bare `Typing` 7 pc. MEASURED, three pairs, agreeing to 0.25 percentage points** |

**AND THE TWO HALVES JOIN UP.** `[LJ-1.177]` capped the `DeadCode` lever at
about 5.2 s and marked the residue as a SEPARATE and larger candidate. **They
are not separate. The module machinery it named is billed to `DeadCode` and
`Serialization`, so it sits INSIDE the 5.2 s ceiling that report already
measured, not beside it.** The residue is a different term with a different
cause.

## 3. THE CURE AND ITS PRICE

**THERE IS NO CURE THAT THIS PROJECT'S INSTRUMENT COULD SHOW TO HAVE WORKED.
That is the finding, and section 3.3 is the arithmetic that forces it.**

### 3.1 What the term is made of, and what each part could give

| part | ms | what it is | is there a lever? |
|---|---:|---|---|
| **`Typing.OccursCheck`** | **11,750** | the occurs check that runs on every metavariable assignment | **I-5**, write branch types so fewer metas are created; **P-t / P-l**, seal so an assigned term is an atom rather than a tree. **NEITHER IS MEASURED AT AN `OccursCheck` SITE ANYWHERE IN THIS REPOSITORY** |
| **`Typing.TypeSig`** | **5,135** | elaborating the type signatures. A regular expression counts **about 1,240** candidate in-fence signatures, so **about 4.1 ms each**. **That count is a text count and I mark it INFERRED** | **NONE that is admissible.** The only way down is fewer or smaller signatures, and **P-q measured 315 lines removed buying 11.8 s**, so deleting to improve a ratio is refused |
| bare `Typing` | 1,202 | module sections and everything `checkDecl` bills to no sub-phase | **NONE priced.** Probe D puts 136 applications at 152 ms of this |

### 3.2 Why I price no cure, and say so rather than guess one

**P-l forbids it and I have no site to re-measure at.** The one measured seal
factor in this family is `[LJ-1.145]:299-314`, `midOpen` 2,459 ms to
`midSealed` below 1 ms. **That is a `Typing.CheckRHS` coercion, not an
`OccursCheck`.** `[LJ-1.147]` then applied it and the wing's largest definition
fell from 9,267 ms to 3,632 ms, **which is CheckRHS moving, exactly as the
probe predicted, and it did not touch this term.**

**A price built by carrying that factor onto `OccursCheck` would be a
hypothesis, not a price (DD8, P-l).** So I give none.

### 3.3 THE SIZE TEST, and it is decisive on its own

**MEASURED, from `scripts/check-ratio.py:76-101`: the instrument's band is
+-12.8 percent.**

| quantity | value | the band on it |
|---|---:|---:|
| `src/L/Condensation.lagda.md`, cold, three quiet runs | **130.4 s** | **+-16.7 s** |
| the GCH wing, 12 masters, 11,926 lines, n=2 | **192.41 s**, section 5 | **+-24.6 s** |
| **THE WHOLE RESIDUE** | **17.8 s** | |

**So a cure that removed ONE HUNDRED PERCENT of this term would move the master
by about its own noise band, and the wing by well UNDER its noise band.**

**`[LJ-1.177]:308-312` set exactly this test and this term fails it.** A cure
that took half of `OccursCheck`, which nothing measured suggests is reachable,
would be 5.9 s: **a third of the master's band and a quarter of the wing's.**

**THIS FIRES THE BRIEF'S SECOND ABORT CRITERION: IDENTIFIED AND NOT CURABLE.**
I state it in the brief's own words. **The wing is intrinsically this
expensive, and the last lever the wing was thought to hold is not a lever.**

## 4. SHARED OR WING-LOCAL

**WING-LOCAL, and I re-measured the cone rather than quoting `[LJ-1.177]`.**

I ran `scripts/ledger.py`'s own `closure` over `import_graph(tracked_masters())`
from `ratio.ac_baseline_root`, which is `src/Landmarks.lagda.md`. **The AC
baseline cone holds 74 masters. `src/L/Condensation.lagda.md` and all three
`*Agree` masters are NOT among them.** MEASURED, with the tool's own function
rather than by reading a list.

**So a cure applied inside `src/L/Condensation.lagda.md` cannot move DD24's
denominator, and `[LJ-1.147]`'s sting cannot fire.**

**BUT THE CURE CLASS IS THE OTHER QUESTION, and it is the one that decides.**
The only lever with a measured factor at an `OccursCheck`-adjacent site is the
`opaque` seal, and **`[LJ-1.147]` applied that class to SHARED upstream
machinery and measured every master faster and the ratio WORSE.** A seal placed
inside `L/Condensation` is WING-LOCAL; a seal placed on the machinery the
master reads is SHARED. **The two are not the same cure and the report that
funds one must say which.**

| candidate | site | SHARED or WING-LOCAL |
|---|---|---|
| write branch types to remove metas (I-5) | inside `L/Condensation` | **WING-LOCAL** |
| seal a formula the master itself builds | inside `L/Condensation` | **WING-LOCAL** |
| seal the machinery the master reads | `src/L/Coding/*` | **SHARED. REFUTED as a route by `[LJ-1.147]`** |

## 5. THE WING'S GAP, RE-MEASURED. n=2, and I say so

**Instrument: `scripts/check-ratio.py --runs 2`, cold, warm dependencies,
`GHCRTS="-A64m -I0 -M8g"`, warm-up discarded by the tool.** Raw:
`agents/tasks/LJ-1-185/runs/wing-ratio.txt`. Bar `0.010514` s per line, which is
`0.009143` at the 1.15 tolerance.

**MEASURED: the wing is 192.41 s over 11,926 lines. Ratio 0.0161, which is
1.76x the AC side at the same caliber. The aggregate rests on 2 runs and
spreads 1.9 percent.**

```
on-bar seconds = 11,926 x 0.010514 =  125.39 s
wing seconds                       =  192.41 s
GAP TO THE BAR                     =   67.02 s
```

### 5.1 The load beside the figure, and what it costs the figure

**A sibling ran Agda beside this series and the number is an UPPER BOUND.**
`check-ratio.py` refuses to START beside another agda and it did not refuse, so
the machine was clean at 09:39. **`[LJ-1.184]` then started again during the
series.** Load 3.5 to 4.4.

**I can price the contamination, because I measured the dominant master myself
on a quiet machine three times.**

| `src/L/Condensation.lagda.md` | seconds | when |
|---|---:|---|
| my three cold `--profile=definitions` runs, quiet | **128.55 / 129.25 / 133.48**, mean **130.4** | 09:07 to 09:28 |
| `check-ratio.py`, n=2, sibling live | **138.63** | 09:39 to 09:45 |

**That is 6.3 percent, and it is in the direction contention predicts.**
Deflating the whole wing by the same 6.3 percent gives **181.0 s and a gap of
55.6 s**.

**SO THE WING'S GAP TODAY IS 56 TO 67 s. MEASURED, n=2, with the contention
stated.** `[LJ-1.177]` measured about 44 s on `[LJ-1.173]`'s tree.

### 5.2 What the gap says about the residue

**Even a cure that removed the ENTIRE 17.8 s residue leaves the wing 38 to 49 s
above the bar.** The residue is **27 to 32 percent** of the gap, and section 3.3
measures that no part of it can be shown to have moved.

### 5.3 Where the wing's seconds actually are, MEASURED today

| group | lines | seconds | s per line | against the 0.010514 bar |
|---|---:|---:|---:|---|
| **the four Condensation masters** | **7,781** | **158.25** | **0.0203** | **1.93x OVER** |
| the other eight wing masters | 4,145 | 34.16 | **0.0082** | **UNDER** |

**MEASURED: eight of the twelve wing masters are already under the bar
together. 65 percent of the wing's lines carry 82 percent of its seconds, and
they are the Condensation family.** **The wing does not have a broad cost
problem. It has one chapter.**

**UNDER DD24 AS THE OWNER RULED IT ON 2026-08-14 THIS IS A DISTANCE, NOT AN
ARREARS.** Intermediate debt is allowed and only the whole GCH side is judged
at the end. **I report the distance and I do not turn it into a schedule.**

## 6. DD4

**Maximize the code the two proofs share, and write it generic. Here is what
re-instantiates for the J tower, and it is nearly all of it.**

| file | names a tower? | re-instantiates |
|---|---|---|
| `gen_probe.py` | **NO.** The carrier is a private unary `N` declared inside the generated file | **WHOLE.** It generates a J-side probe series by running it |
| `ProbeLJ1185A/B/C/D.agda` | **NO.** No stage, no formula, no `𝒮ʟ`, no `𝒮ⱼ`. The only import is `Cubical.Foundations.Prelude` | **WHOLE, unchanged** |
| `residue.py` | **NO.** It reads any pair of Agda profile files for any module | **WHOLE** |
| `run_probes.sh` | **NO.** It takes its file list from the argument line | **WHOLE** |
| `agents/tasks/LJ-1-177/census_telescopes.py` | **NO** | **REUSED rather than rewritten** |
| `agents/tasks/LJ-1-155/measure.py` | **NO** | **CALLED rather than copied** (C-26) |

**619 probe lines and 0 tower names. `[LJ-1.178]` wrote 301 lines naming the
tower eleven times with every one in a TYPE; this series names it zero
times, because the question is about Agda's elaborator and not about either
tower.**

**AND THE FINDING ITSELF IS TOWER-FREE, which is the part that matters.** The
billing law in section 2.7, that `--profile=definitions` bills `CheckLHS` and
`CheckRHS` and leaves `TypeSig`, `OccursCheck` and bare `Typing` outside every
definition, **is a property of Agda 2.8.0. It holds for the J tower's masters
on the day they exist, and it means nobody has to run this diagnosis twice.**

**A stop-line is not a reason to write fixed and I did not use it as one.** The
probe series is generic even though its verdict is a stop.

## 7. EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| **there is a separate 16 s term** | **MEASURED FALSE. It does not exist.** It is `21,268 - 5,297` with the 5,297 already subtracted. Section 1.3 |
| **`DeadCode` is part of the residue** | **MEASURED FALSE.** It is one of the non-`Typing` phases subtracted to reach it |
| **the residue is module telescope elaboration** | **MEASURED FALSE.** `[LJ-1.155]`'s probe B1 bills a 36-hypothesis telescope to `DeadCode` at 2,822 ms against 1,091 ms of all `Typing` |
| **the residue is module-application instantiation** | **MEASURED FALSE.** Probe D prices 136 applications at 2,151 ms with 152 ms of `Typing`, so instantiation is **0.9 percent** of the residue. Section 2.9 |
| **module applications are free** | **MEASURED FALSE, and I say it against my own refutation.** They cost 15.8 ms each. The price is real; it is billed to `DeadCode` and `Serialization`, which the residue excludes |
| **`[LJ-1.145]`'s P-w refutation settles the aggregate** | **FALSE by C-42.** It measured ONE site. Probe D measures 136 and reaches the same verdict for a different reason |
| **a dominant definition exists** | **MEASURED FALSE, re-measured today.** Largest is `LeafAgree.back` at 6,940 ms, 5.5 percent |
| **the residue is an instrument artefact with no content** | **MEASURED FALSE.** Probe B, with no module header and no application, has a residue of **2.9 percent**; the master has 13.6 percent |
| **the residue is 21.3 s today** | **MEASURED FALSE.** 17.8 s, three kept pairs, spread 2.5 percent. `[LJ-1.155]`'s 21.3 s was its own tree and its own run |
| **a cure of this term can be shown to have worked** | **MEASURED FALSE.** The whole term is 17.8 s against a wing band of about 21 s |
| **I priced a cure** | **NO, AND DELIBERATELY.** P-l forbids carrying `[LJ-1.145]`'s CheckRHS seal factor onto `OccursCheck`, and I have no site to re-measure it at |
| **the machine was quiet throughout** | **MEASURED FALSE.** A sibling, `[LJ-1.184]`, ran Agda from 09:29; at 09:32 it ran TWO agda processes at once, RSS 6.9 GB and 3.9 GB. Section 8 |
| **I raised the heap cap** | **MEASURED FALSE.** `GHCRTS="-A64m -I0 -M8g"` throughout, never raised |
| **I edited a master, committed, pushed, or ran `make check`** | **MEASURED FALSE**, none of the four |
| **I ran `git checkout`, `stash`, `reset --hard` or `clean`** | **MEASURED FALSE**, none of the four |
| **I killed a process that was not mine** | **MEASURED FALSE.** I stopped my OWN waiting batch loop, PIDs 28783, 28786 and 34135, and no sibling process |

## 8. CHECKERS AND THE MACHINE

| checker | result |
|---|---|
| `scripts/lint-agda.py --check` | **exit 0** |
| `scripts/lint-prose.py --check` | **exit 0** |
| `scripts/check-probes.py` | **clean**, 1,833 tracked files, no probe outside `agents/tasks/` |
| `agda` | **ONE process at a time**, `GHCRTS="-A64m -I0 -M8g"`, cap never raised, **no heap wall** |
| `make check` | **NOT RUN.** The brief reserves it |

**THE MACHINE WAS NOT QUIET AND EVERY FIGURE CARRIES ITS LOAD.**

| when | what |
|---|---|
| 09:05 to 09:29 | quiet. Load 3.0 to 3.9. **The three master pairs and their loads are in section 2.6** |
| **09:29** | **`[LJ-1.184]` started `agda agents/tasks/LJ-1-184/ProbeLJ1184C.agda`, PID 34069, RSS 3.9 GB** |
| **09:32** | **TWO sibling agda processes at once, PIDs 35046 and 35431, RSS 6.9 GB and 3.9 GB** |
| 09:29 to 09:36 | **my batch WAITED rather than contending.** `measure.py` refuses to start beside another agda binary, and it printed `another agda is live` seven times |
| 09:33 | **I stopped my own 4th master pair** rather than let it queue behind the sibling, and kept three pairs. **I killed only my own processes** |
| 09:36 to 09:39 | quiet again. **The probe series ran here**, load 2.90 to 3.42 |
| **09:39 onward** | **`[LJ-1.184]` again, PID 43957, RSS 7.3 GB, BESIDE my wing run.** Section 5 states what that costs the wing figure |

## 8.1 A PROPOSED LAW, with its measurement (the orchestrator assigns the ID)

**A residue computed by subtracting `--profile=internal` from
`--profile=definitions` is `TypeSig` and `OccursCheck`. It is never module
machinery.**

**Rule.** Agda 2.8.0 refuses `--profile=internal` together with
`--profile=definitions` or `--profile=modules`, so "the seconds billed outside
every definition" can only be reached by subtracting one cold run from another.
**That residue is not a hiding place for structure. The `Definition` account
covers `Typing.CheckLHS` and `Typing.CheckRHS`; `Typing.TypeSig` and
`Typing.OccursCheck` sit outside it wherever they occur.** Module telescopes
and module applications are billed to `DeadCode`, `Serialization` and
`InterfaceInstantiateFull`, and the subtraction removes all three before the
residue is formed. **So a residue is priced by reading `TypeSig` and
`OccursCheck` off the internal profile, and never by naming a construct in the
source.**

**Measurement.** `src/L/Condensation.lagda.md`, three kept cold pairs on
2026-08-14: definition sum 47.29 / 48.02 / 47.73 percent against
`CheckLHS`+`CheckRHS` 47.54 / 47.81 / 47.49 percent, agreeing to 0.25
percentage points. `agents/tasks/LJ-1-185/ProbeLJ1185B.agda`, three kept pairs:
definition sum 1,170 ms against `CheckRHS` 1,164 ms, and a residue of 2.9
percent with no module header in the file.
`agents/tasks/LJ-1-185/ProbeLJ1185D.agda` minus `ProbeLJ1185C.agda`, three kept
pairs: 136 module applications cost 2,151 ms, of which `DeadCode` 986,
`Serialization` 785, `InterfaceInstantiateFull` 166 and all of `Typing` 152.

**What it would have saved.** `[LJ-1.145]` named this residue "module telescopes
and module-application instantiation" on 2026-08-13 and marked it INFERRED.
`[LJ-1.155]` repeated the sentence. `[LJ-1.177]` repeated it again and made it
the wing's last lever. **Three reports carried one unmeasured phrase for two
days, and it cost this dispatch.** That is C-39 and C-40's class exactly.

## 8.2 C-36: THE TERM I COULD NOT WRITE

**I could not price a cure for `Typing.OccursCheck`, and the reason is that
nothing in this repository has ever measured one.**

**The probe I would build, named so the next dispatch can price it.** Take one
of the master's `back` definitions, restate it twice at the master's own
generality, once with every truncation branch left to inference and once with
every branch carrying a written type (I-5), and read `Typing.OccursCheck` off
`--profile=internal` in both. **That measures the meta count lever at the real
site. It needs no master edit and it costs about ten seconds a run.**

**I did NOT build it, and I say why rather than leave it implied.** Section 3.3
measures that the whole term is smaller than the wing's noise band, **so the
probe would price a lever that cannot be shown to have worked even at one
hundred percent.** Building it would be spending a dispatch on a quantity the
instrument cannot read. **If the owner wants the number anyway, the probe above
is the cheapest way to get it.**

## 9. LITERATURE (DD18)

**Nothing in the literature governs elaboration cost.** Every term named here
is a property of Agda 2.8.0's elaborator and its benchmark accounts.

## 10. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-177/lj-1.177-report.md`, read WHOLE.** **TOOK:** the
  target at `:259-265`, which section 1.3 refutes; the 5.2 s `DeadCode` ceiling
  at `:239-257`; the census method at `:83-98`, which I re-ran on
  `L/Condensation` unchanged; the WING-LOCAL cone finding at `:281-285`, which
  section 4 keeps; the instrument's 21 s resolution at `:308-312`.
- **`agents/tasks/LJ-1-155/lj-1.155-report.md`, read WHOLE, and its RAW FILES,
  which matter more than its prose.** **TOOK:** `runs/src_L_Condensation.defs1.txt`
  and `runs/src_L_Condensation.int1.txt`, which are the two accounts section 1
  re-adds; `:134-139`, the derivation of the 21,268 ms, whose arithmetic I
  reproduce and whose double subtraction I refute;
  `runs/agents_tasks_LJ-1-155_ProbeLJ1155B1.agda.int1.txt` and `...B10...`,
  which measure that a 36-hypothesis telescope costs `DeadCode` and not
  `Typing`; `:127`, the 4.4 percent; `:397-433`, the AC cone.
- **`agents/tasks/LJ-1-145/lj-1.145-report.md`, read WHOLE, and its four
  probes.** **TOOK:** `:189-223`, the P-w refutation, which is one half of
  `[LJ-1.177]`'s identification already measured FALSE at this master;
  `:86-100`, the first derivation of the same residue at "about 22,000 ms",
  which shows the quantity is stable across three months of the master's
  growth; `:229-247`, the transplant method, which is the method this report
  uses for its probe series. **REFUSED:** its 21 s cure price, because
  `[LJ-1.147]` already spent that lever and measured the ratio WORSE.
- **`agents/tasks/LJ-1-158/lj-1.158-report.md:100-106` and `:243-252`**, through
  `[LJ-1.177]`'s quotation. **TOOK:** the telescope-to-record cure and its
  42.72 s, which is why the telescope lever is SPENT and not re-opened here.
- **`archive/dev/measurements/l3.32-t242-profile.txt` and
  `archive/dev/measurements/t132-check.log`.** **TOOK the SHAPE, not a claim:**
  two `--profile=definitions` runs from the RETIRED rud route bill
  `Miscellaneous` at **8.3 percent** and **8.7 percent** of the check.
  **`L/Condensation` bills it at 52.7 percent.** So a file CAN put nine tenths
  of its seconds inside named definitions, and 52.7 percent is not the
  instrument's floor. **WHAT DOES NOT TRANSFER:** both are single-module probes
  of the retired route with no module application at all, and their content
  class is P-n instantiation content. **Their 8 percent is not a target for a
  6,676-line master with 136 module applications**, and I use it only to bound
  the "instrument artefact" explanation.
- **`archive/dev/measurements/README.md`.** **TOOK:** the rule that a cold
  profile is evidence and not exhaust, which is why this report keeps every raw
  run under `agents/tasks/LJ-1-185/runs/`.
- **`archive/dev/TASKS-archived.md` and `STATUS-archived.md`: SURVEYED, NOT
  USED, and I say so rather than pad this section.** I searched both for
  `--profile`, `Miscellaneous`, `module application` and `instantiat`. **The
  four hits are all about re-instantiating a PROOF at a new carrier, not about
  Agda's module application.** The retired route never profiled a master this
  way. **`archive/src/2026-08-09-rud-route/` holds no master with a comparable
  module-application density**, so no shape transfers from it.
- `dev/LESSONS.md`, at each entry: **P-l** (section 6 refuses to move a measured
  figure by analogy), **P-t** (section 2.4 counts rather than averages),
  **P-q** (nothing was deleted), **C-42** (section 2.5 states the extent of
  `[LJ-1.145]`'s refutation instead of borrowing it), **C-12** (one agda
  process, cap never raised), **C-22** (this file existed before the first
  run), **D-1** (the abort criterion was in the brief and section 0 answers
  it), **P-m** and **I-5** (section 3).
- `scripts/check-ratio.py:76-101`, the `+-12.8` percent band and its
  provenance.

## 11. THE PROBES AND THE FILES

All under `agents/tasks/LJ-1-185/`, all tracked, none anywhere near `src/`.

| file | what it is |
|---|---|
| `ProbeLJ1185A.agda` | the format probe: it asks whether Agda takes two profile accounts in one run. It does not |
| `gen_probe.py` | the generator for the controlled series. **It names no tower, no stage and no formula, so it re-instantiates for the J side unchanged** |
| `ProbeLJ1185B.agda` | `base`: the definitions at file level, NO module header, NO module application |
| `ProbeLJ1185C.agda` | `tele`: the same shape under a 24-hypothesis telescope |
| `ProbeLJ1185D.agda` | `apps`: `tele` plus 136 module applications, the master's own count |
| `residue.py` | the subtraction, written once. It reads any pair of Agda profile files for any module in either tower |
| `run_probes.sh` | the run loop. It calls `agents/tasks/LJ-1-155/measure.py` rather than copying it (C-26) |
| `runs/` | **34 files.** Every raw run, with its load before and after, its wall seconds and its exit code. Six master profiles, 24 probe profiles, one `--profile=modules` run, two batch logs and `wing-ratio.txt` |

## 12. WHAT I RECOMMEND, offered and not taken

1. **Rule the residue term SPENT, and record why in one line.** It is
   `Typing.OccursCheck` and `Typing.TypeSig`, it is 17.8 s, and the instrument
   cannot resolve any cure of it. **The wing has no measurable lever left.**
2. **Correct `[LJ-1.177]`'s two levers into one.** The module machinery it named
   as the residue's cause is `DeadCode` and `Serialization` work, so it sits
   inside that report's own 5.2 s ceiling. **The wing's remaining measured
   ceiling is about 5 s, not 5 s plus 16 s.**
3. **Re-measure the wing on a quiet machine before any decision rests on 67 s.**
   My series ran beside a sibling and section 5.1 prices the contamination at
   6.3 percent. **The 56 s deflated figure is the safer one.**
4. **Take the proposed law in section 8.1 or refuse it, but do not let the
   phrase survive unmeasured a fourth time.** Three reports carried "module
   telescopes and module-application instantiation" from `[LJ-1.145]` to
   `[LJ-1.177]` without anyone measuring it.
5. **If the owner still wants a seconds lever on this wing, it is not in this
   term.** Section 5.3 measures that eight of the twelve wing masters are
   already under the bar together, and the Condensation family carries 82
   percent of the wing's seconds on 65 percent of its lines. **The question
   worth funding is what that chapter would cost written fresh today (DD13),
   not what can be shaved off it.**
