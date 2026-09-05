# LJ-1.158 report: the `*Agree` telescopes collapse into records

tier: opus (version `override`). Written incrementally (C-22). Every negative
is marked **MEASURED** or **INFERRED**.

**STATUS: COMPLETE. THE CURE IS LANDED AND GREEN.** Three masters edited, four
probes written under `agents/tasks/LJ-1-158/`, all tracked. **Nothing was
committed and nothing was pushed. I did not run `make check`; the brief
reserves it.**

## 0. THE ANSWER, in one line and then five

**THE WING GOES 2.06x TO 1.60x, and this is the first cure measured on it that
improves the DD24 verdict instead of eroding it.**

1. **MEASURED, two runs each side, one session, one agda process.** The wing
   was **219.14 s over 11,635 lines, 0.0188 s/line, 2.06x**; it is now
   **172.17 s over 11,743 lines, 0.0147 s/line, 1.60x**. Aggregate spreads 2.4
   and 2.7 percent. Load 4.72 to 4.38 before and 3.98 to 3.51 after.
2. **The cure's own share is 42.72 s, not 46.97.** The nine untouched wing
   masters moved by -4.25 s between the two series and nothing in them changed,
   so that part is the machine. **On the cure's own 42.72 s the wing reads
   1.64x, and that is the figure to quote.**
3. **`TwelveAgree` behaved like `UpperAgree` and slightly better. MEASURED.**
   Probes T1 and T2: `DeadCode.DeadCodeReachable` **13,018 ms to 95 ms**, a
   factor of 138, and the probe file minus 69.4 percent. **P-l did not fire,
   and I measured it before I edited anything.**
4. **NOTHING WALLED and the 8 GB cap was never raised.** Probe T2 states 59 of
   `TwelveAgree`'s 60 hypotheses as record fields, including all 24 that
   `UpperAgree` does not have. **`sucK` stays a telescope hypothesis in
   `UpperAgree` and `TwelveAgree`, and it is the only known waller.**
5. **Every consumer is GREEN and no theorem statement changed.**
   `TwelveAgree`, the only `src/` consumer of the other two, is exit 0 at 7.84
   s. Every signature is byte-identical to HEAD `0e4ddcd`, verified by diff.

**THE VERDICT IS STILL OVER THE BAR. The bar is 0.0105 s/line, the wing needs
123.5 s and spends 172.2, so the gap is 48.7 s against 96.8 before.** The cure
closes half of it. **The other half is `L/Condensation`, which this cure barely
touches**, and section 6.2 names the probe that prices it.

**This fires the brief's first abort criterion: the three masters collapsed and
the wing improved. I report and stop.**

**EVERY `HEAD` CITATION IN THIS REPORT MEANS `0e4ddcd`**, the commit this task
started on. The orchestrator committed `[LJ-1.159]` as `a68ed20` while I
worked. **MEASURED: `git diff 0e4ddcd a68ed20 -- src/` is EMPTY**, so the
before-and-after line counts and the statement diffs read the same tree under
either name.

## 1. MACHINE LOAD, RUN COUNT AND THE SIBLING

**ONE agda process at a time, `GHCRTS="-A64m -I0 -M8g"`, cap never raised.**
`agents/tasks/LJ-1-158/run158.py` REFUSES to start beside another agda binary
(`pgrep -x agda`) and waits instead.

**A sibling ran Agda through most of this dispatch and I name it.**
`[LJ-1.159]`, PID 50631, `agda --profile=definitions
agents/tasks/LJ-1-159/ProbeLJ1159A.agda`, seen with `ps -eo
pid,etime,rss,command` at 23:31. **It blocked my first attempt at the BEFORE
wing measurement**, which `scripts/check-ratio.py` refused outright with
"another Agda process is live (C-12)". **It then held the machine for 270
seconds before the consumer check**, PIDs 58162, 59057 and 59883, which
`run158.py` waited out rather than measured through.

**THE MACHINE WAS NOT QUIET AND NO FIGURE HERE HIDES IT.** The 15-minute load
average sat at 3.98 to 4.30 throughout. **Every load-bearing figure is a pair
taken on the same instrument**: the two probe pairs are back-to-back runs
minutes apart, and the two wing series are 20 minutes apart in one session at
loads that differ by 0.7.

**ONE HONESTY NOTE ON THE AFTER SERIES.** At 23:56, while that series was
running, I replaced a three-line comment in `LowerAgree.lagda.md` with a
seven-line one, because the generated comment named `sucK`, which that master
does not have. **`check-ratio.py` reads a module's line count immediately
before timing it** (`scripts/check-ratio.py:259`), and `LowerAgree` is the
LAST of the twelve. **Its AFTER row reads 291 lines, which is the post-edit
count, so its lines and its seconds are the same tree.** The nine untouched
masters were unaffected either way.

## 2. THE TELESCOPE CENSUS, and it corrects `[LJ-1.155]`

**MEASURED, by machine extraction from the masters at HEAD `0e4ddcd`**
(`agents/tasks/LJ-1-158/gen_probe.py`, which splits the telescope into
parenthesised groups and prints their names):

| master | module | hypotheses | `[LJ-1.155]` census |
|---|---|---:|---:|
| `UpperAgree` | `UpperAgree`, `:77` | **36** | 38 |
| `LowerAgree` | `LowerAgree`, `:76` | **37** | 39 |
| `TwelveAgree` | `AbstractFrame`, `:114` | **60** | 62 |

**Each row is exactly 2 lower than `[LJ-1.155]` section 3.1**, and the reason
is arithmetic: that census counted the `Fin (5 + n)` block and the `γ` line as
hypotheses. `[LJ-1.155]`'s own cure text says 36 for `UpperAgree`, so its table
and its text disagree by the same 2. **The seconds figures it measured are not
affected.**

## 3. THE PROBES: the two unmeasured telescopes, MEASURED

**`[LJ-1.155]` measured the collapse at `UpperAgree`'s 36 hypotheses only and
named the rest as its own unmeasured term.** P-l forbids a transplant by
analogy, so I measured the other two before I edited anything.

`agents/tasks/LJ-1-158/gen_probe.py` extends `[LJ-1.155]`'s generator to any of
the three masters and to both sides of the pair. Each probe carries the
master's import block VERBATIM, its telescope VERBATIM, and **the same eight
definitions that do no work**, so the two sides of a pair differ in the
statement of the block and in nothing else.

**Four probes, two controlled pairs, two runs each side, warm-up discarded,
`--profile=internal`, cold every run (the probe's own `.agdai` deleted before
each), load 1m 4.03 to 6.04.**

| phase | L1 telescope | L2 record | delta | T1 telescope | T2 record | delta |
|---|---:|---:|---:|---:|---:|---:|
| **Total** | 7,243 | **3,726** | **-48.6 pc** | 20,958 | **6,421** | **-69.4 pc** |
| **`DeadCode.DeadCodeReachable`** | 2,689 | **26** | **factor 105** | 13,018 | **95** | **factor 138** |
| `Typing`, all | 1,484 | 728 | -756 | 3,192 | 1,753 | -1,439 |
| `Coverage` | 906 | **0** | -906 | 1,978 | **0** | -1,978 |
| `Positivity` | 34 | 464 | **+430** | 73 | 986 | **+913** |
| `Serialization` | 187 | 425 | **+238** | 406 | 1,067 | **+661** |
| `InterfaceInstantiateFull` | 50 | 172 | **+122** | 136 | 422 | **+286** |
| `Deserialization` | 1,107 | 1,138 | +31 | 1,153 | 1,179 | +26 |

Every cell is the mean of two runs. **The two runs on each side agree to 3.4
percent or better** (L1 7,120 and 7,365; L2 3,724 and 3,727; T1 20,868 and
21,048; T2 6,433 and 6,408). Raw: `agents/tasks/LJ-1-158/runs/{L1,L2,T1,T2}.run{1,2}.txt`.

**NOTHING WALLED. MEASURED.** `L2` states all 37 of `LowerAgree`'s hypotheses
as fields, and `LowerAgree` has no `sucV` anywhere (`grep -c sucV`, and its
`open InfinitySet` at `:40` takes `#_` only). `T2` states 59 of
`TwelveAgree`'s 60 and keeps `sucK` in the telescope. **No probe exhausted the
8 GB cap and the cap was never raised.**

**THE RECORD'S OWN FIXED COST, stated rather than netted away.** `Positivity`
plus `Serialization` plus `InterfaceInstantiateFull` rise by **790 ms** at
`LowerAgree`'s 37 fields and **1,860 ms** at `TwelveAgree`'s 59.
`[LJ-1.155]` measured 720 ms at `UpperAgree`'s 35. **The fixed cost grows with
the field count and the saving grows faster.**

### 3.1 The transplant fraction, and it is NOT uniform

| master | its `DeadCode` (`[LJ-1.155]` 2.2) | the telescope probe alone | share |
|---|---:|---:|---:|
| `UpperAgree` | 3,675 ms | 2,652 ms | 72 pc |
| `LowerAgree` | 6,818 ms | 2,689 ms | **39 pc** |
| `TwelveAgree` | 13,976 ms | 13,018 ms | **93 pc** |

**MEASURED: `TwelveAgree`'s telescope reproduces 93 percent of its master's
`DeadCode` in a file that proves nothing.** `LowerAgree`'s reproduces 39
percent, so a larger part of its `DeadCode` is billed to the six row module
applications inside it rather than to the telescope. **That is the one place
where the three masters differ, and it caps what the cure can return at
`LowerAgree`.**

## 4. THE EDIT, and nothing in it is retyped

**Three masters, three records, `sucK` a telescope hypothesis in two of them.**
`agents/tasks/LJ-1-158/apply_collapse.py` performs the move: a field's TEXT is
the telescope hypothesis's text, shifted one column and with its outer
parentheses removed. **Nothing was retyped, so the collapse cannot change what
a theorem says.**

| master | record | fields | kept in the telescope |
|---|---|---:|---|
| `UpperAgree.lagda.md:90` | `UFacts` | **35** | `sucK` |
| `LowerAgree.lagda.md:89` | `LFacts` | **37** | none; it has no `sucV` |
| `TwelveAgree.lagda.md:128` | `TFacts` | **59** | `sucK` |

Each module body opens its record as its first line (`open UFacts uf`,
`UpperAgree.lagda.md:200`), so every use site inside the module is unchanged.

### 4.1 What `TwelveAgree` had to do as well

`TwelveAgree` supplies `LowerAgree` and `UpperAgree`, so its six call sites
listed 37 and 35 arguments by name. **They now pass ONE record each**, built
once at `:369` and `:399` from `TFacts`'s own fields:

```
  lf : LFacts {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'
  lf = record
    { tagEq0 = tagEq0
    ...
```

**That is the archived `asRecursion`'s move exactly**
(`archive/src/2026-08-09-rud-route/L/Recursion.lagda.md:320`), and
`KFactsCons` at `src/L/Condensation.lagda.md:6039` is the same move inside the
live tree.

**`arityK` is DERIVED in `TwelveAgree` from `transK` and is a HYPOTHESIS of
`UpperAgree`**, so `uf .arityK` is the derivation. That is what the positional
call sites passed before, and it discharges nothing (C-38).

**MEASURED: Agda 2.8.0 resolves a record expression's field names against the
EXPECTED type.** `TwelveAgree` imports `LFacts` and `UFacts` with a `using`
clause that binds neither record's field names, and `record { tagEq0 = tagEq0
; ... }` still elaborates. **So no `open LFacts` was needed and the name
collision that would have forced one never arose.**

### 4.2 What did NOT change, MEASURED

**Every theorem statement is byte-identical to HEAD `0e4ddcd`.** I diffed the
signature lines of `out`, `back`, `sixB`, `sixAt`, `twelveB`, `p0b`, `p1b`,
`twelve-out`, `twelve-back`, `arityK` and the five tied key facts across all
three masters against `git show HEAD:`, with their continuation lines.
**IDENTICAL in all three.**

**No hypothesis was added and none was removed.** 36 becomes 35 fields plus
`sucK`; 37 becomes 37 fields; 60 becomes 59 fields plus `sucK`.

**Nothing was deleted to improve a ratio (P-q, DD24).** The line count RISES.

| master | HEAD | now | delta |
|---|---:|---:|---:|
| `UpperAgree` | 270 | **290** | **+20** |
| `LowerAgree` | 267 | **291** | **+24** |
| `TwelveAgree` | 399 | **463** | **+64** |
| the wing | 11,635 | **11,743** | **+108** |

**`TwelveAgree` gains most because it pays twice**: its own record, and the two
records it builds for the partials. `scripts/ledger.py` `count` is the caliber.

**`scripts/lint-agda.py --check` and `scripts/lint-prose.py --check` are GREEN
on all three**, before and after.

## 5. WING RATIO, BEFORE AND AFTER

**MEASURED, `scripts/check-ratio.py --check --runs 2`, TWO runs per master,
warm-up discarded, cold with warm dependencies, one agda process, both series
in this session and 20 minutes apart.** Raw:
`agents/tasks/LJ-1-158/runs/wing-before.txt` and `runs/wing-after.txt`.

| | BEFORE | AFTER | delta |
|---|---:|---:|---:|
| wing seconds | **219.14** | **172.17** | **-46.97** |
| wing in-fence lines | 11,635 | 11,743 | +108 |
| **s per line** | **0.0188** | **0.0147** | |
| **DD24 ratio** | **2.06x** | **1.60x** | **-0.46** |
| run count | 2 | 2 | |
| aggregate spread | 2.4 pc | 2.7 pc | |
| load 1m, start to end | 4.72 to 4.38 | 3.98 to 3.51 | |
| wall of the series | 442.94 s | **348.65 s** | -94.29 |

**THE VERDICT IS STILL OVER THE BAR, and I say so first.** The bar is 0.0105
s/line at the 1.15x tolerance, so the wing needs 123.5 s and spends 172.2.
**The gap is 48.7 s, down from 96.8 s.** The cure closes half the gap and does
not decide DD24.

**AND IT IS THE FIRST CURE ON THIS WING THAT MOVED THE VERDICT THE RIGHT WAY.**
`[LJ-1.147]`'s seal took every master faster and the ratio from 1.56x to 1.91x,
because it was SHARED and the reference side gained more (P-y). **This one is
wing-local, the baseline cone contains none of the three masters, and the
denominator of the bar could not move.** `[LJ-1.155]` verified that cone
membership with the tool's own function.

### 5.1 THE HONEST DEDUCTION, and it is smaller than 46.97 s

**The untouched masters also moved, and that is the instrument, not the cure.**

| master | BEFORE s | AFTER s | delta |
|---|---:|---:|---:|
| the NINE untouched wing masters | 156.66 | 152.41 | **-4.25** |
| **the three edited masters** | **62.48** | **19.76** | **-42.72** |
| the wing | 219.14 | 172.17 | -46.97 |

**So the cure is worth 42.72 s, and 4.25 s of the 46.97 is the machine.**
`L/Condensation` alone accounts for 2.98 of that 4.25 and nothing in it
changed. **A report that claimed the whole 46.97 for the cure would be
overstating it by 10 percent, and DD24 is not decided by 10 percent.**

**Recomputed on the cure's own 42.72 s: 219.14 minus 42.72 is 176.42 over
11,743 lines, 0.01502 s/line, 1.64x.** That is the conservative figure and it
is the one to quote.

## 6. PER-MASTER DELTA, at the MASTER and not at the probe

**MEASURED, both sides by `check-ratio.py --runs 2`, the same instrument.**

| master | BEFORE s | s/line | AFTER s | s/line | delta | delta pc |
|---|---:|---:|---:|---:|---:|---:|
| `TwelveAgree` | 30.42 | 0.0762 | **9.54** | 0.0206 | **-20.88** | **-68.6 pc** |
| `LowerAgree` | 20.00 | 0.0749 | **4.80** | 0.0165 | **-15.20** | **-76.0 pc** |
| `UpperAgree` | 12.06 | 0.0446 | **5.42** | 0.0187 | **-6.64** | **-55.1 pc** |
| **the three** | **62.48** | | **19.76** | | **-42.72** | **-68.4 pc** |

**All three are still OVER the bar per module**, at 0.0165 to 0.0206 against
0.0105. **The per-module flag is advice; the aggregate is the judgment.**

**ONE ROW CARRIES INSTRUMENT NOISE and I flag it rather than hide it.**
`TwelveAgree`'s AFTER row spreads **32.9 percent** over its two runs, the
largest spread in either series. Its BEFORE row spread 2.1 percent. **So the
9.54 s figure is the weakest number in this report**, and the honest reading of
`TwelveAgree` is "about 20 s off, plus or minus 3". The other five rows spread
1.2 to 6.0 percent.

### 6.1 What the probe PREDICTED against what the master DELIVERED

| master | probe pair, whole file | master, whole file | error |
|---|---:|---:|---:|
| `TwelveAgree` | -69.4 pc | **-68.6 pc** | **0.8 points** |
| `UpperAgree` | -52.4 pc (`[LJ-1.155]`) | **-55.1 pc** | 2.7 points |
| `LowerAgree` | -48.6 pc | **-76.0 pc** | **27.4 points, UNDER** |

**MEASURED: the probe predicted two of the three masters to within three
points and UNDER-predicted `LowerAgree` by 27.** The probe is a good
instrument for this cure and it is not a perfect one.

**Why `LowerAgree` beat its probe is UNMEASURED and I will not guess it.** The
one fact I have is section 3.1's: `LowerAgree`'s telescope reproduces only 39
percent of its master's `DeadCode`, against 93 percent at `TwelveAgree`. **So
`LowerAgree` carries `DeadCode` that the telescope alone does not explain, and
the collapse reached that part too.** P-w, which measures that a module
application COPIES its body, is the first place to look, and it is a
hypothesis until somebody runs it.

### 6.2 DD8: the widest unmeasured term now

**`src/L/Condensation.lagda.md`, and it is 119.24 s of the wing's 172.17, or
69 percent.** `[LJ-1.155]` section 1.2 measured that about **21,268 ms of its
type-checking is billed outside every definition**, which is module telescopes
and module-application instantiation, and that `[LJ-1.145]` measured the same
quantity before `[LJ-1.147]`'s seal. **Its `DeadCode` is only 4.4 percent, so
THIS cure's lever is small there and a different one is needed.**

**The probe that measures it costs about two minutes:** run
`agents/tasks/LJ-1-158/gen_probe.py` against one of `L/Condensation`'s own row
module telescopes, both sides. **The generator already takes a master key and a
line range.** I did not run it, because the brief's scope is the three `*Agree`
masters and its abort criterion says report and stop.

## 7. DID `TwelveAgree` BEHAVE LIKE `UpperAgree`? MEASURED: YES, AND BETTER

**This is the term `[LJ-1.155]` named as its own and refused to price. It is
now measured and P-l did NOT fire.**

| pair | hypotheses | `DeadCode` before | after | factor | whole file |
|---|---:|---:|---:|---:|---:|
| `UpperAgree`, `[LJ-1.155]` B1/B10 | 36 | 2,652 | 25 | **106** | -52.4 pc |
| `LowerAgree`, L1/L2 | 37 | 2,689 | 26 | **105** | -48.6 pc |
| **`TwelveAgree`, T1/T2** | **60** | **13,018** | **95** | **138** | **-69.4 pc** |

**The collapse rate is the same law at all three sites**, and the absolute
saving scales with the telescope. **`TwelveAgree`'s factor is the largest of
the three**, so the 57 percent of the saving that `[LJ-1.155]` could not price
is not merely confirmed, it is slightly better than its own analogy would have
given.

**AND IT CLOSES `[LJ-1.155]`'s SECOND unmeasured term at the same time.** That
report asked whether any of `TwelveAgree`'s other hypotheses walls as a record
field the way `sucK` does; it had bisected `UpperAgree`'s 36 and found exactly
one. **MEASURED: NO. Probe T2 states 59 fields, including every one of the 24
that `UpperAgree` does not have, and it is GREEN at 6.4 s.** `envSetK`, which
names `Generic.envSetGen` and is `TwelveAgree`-only, is among them.
**`sucK` remains the only known waller in this family, and the 8 GB cap was
never raised.**

**One difference between the three, and it is at `LowerAgree`.** Section 3.1
measured that its telescope reproduces only 39 percent of its master's
`DeadCode`, against 72 and 93 percent for the other two. **So `LowerAgree` has
a second source of `DeadCode` that the telescope alone does not carry**, and
its master delta is the one the probe could least predict. Section 6 says what
it actually returned.

## 8. CONSUMER VERDICTS (C-40)

**The consumer set, MEASURED by grep over `src/` after the edit.**
`grep -rn "Condensation.UpperAgree\|Condensation.LowerAgree\|Condensation.TwelveAgree" src/`
returns eight hits: the three module headers, `TwelveAgree.lagda.md:32` and
`:34` importing the two partials, and three `import` lines of
`src/Everything.lagda.md`.

| file | what it is | verdict |
|---|---|---|
| `src/L/Condensation/UpperAgree.lagda.md` | edited | **GREEN, exit 0, 5.24 s** |
| `src/L/Condensation/LowerAgree.lagda.md` | edited | **GREEN, exit 0, 4.77 s** |
| `src/L/Condensation/TwelveAgree.lagda.md` | edited AND the only `src/` consumer of the other two | **GREEN, exit 0, 7.84 s** |
| `src/Everything.lagda.md` | the catalog; three bare `import` lines | **NOT CHECKED. See below.** |

**Module-cold with warm dependencies, the three `.agdai` deleted first, one
series, one agda process, load 3.55 to 3.78.** Raw:
`agents/tasks/LJ-1-158/runs/first-check.txt`.

**`TwelveAgree` is the load-bearing consumer check and it passed FIRST TIME.**
It applies both partials at their new record parameters, so a mismatch in any
of the 72 fields it builds would have been a type error.

**`src/Everything.lagda.md`: NOT CHECKED, and I say why rather than claim it.**
The brief forbids touching it and reserves `make check` for the orchestrator.
It carries three bare `import` lines and no module application, and **the three
module names, their `{ℓ}` and `lem` parameters are unchanged**, so nothing it
does can break. **That last sentence is INFERRED from the file's content, not
MEASURED by a run.** `make check` settles it in one pass.

## 9. DD4, and the honest answer is NO

**`KFacts` does not fit, and I say what I used instead.**
`src/L/Condensation.lagda.md:5996` declares
`record KFacts {n} (A K N0 ... N11 : Fin n) (γ : S ^ n)` with 29 fields.
**MEASURED, by reading its field list against the three telescopes:**

- **It would ADD hypotheses to every one of the three.** `KFacts` carries all
  twelve `tagEq` and all twelve `numK`; `UpperAgree` needs six of each and
  `LowerAgree` needs the other six. It also carries `carrierK`, which needs an
  `A` slot none of the three has, and `innerPairK`, which none of the three
  states.
- **Adding a required hypothesis is a change to what the theorem SAYS**, and
  the brief forbids that. **So `KFacts` is refused, and it is refused on
  content rather than on cost.**

**What I used instead: `KFacts`'s SHAPE and its stated reason**, which is the
repository's own sentence at `:5990-5994`, "one record, so a transfer module
states the block as ONE parameter and re-elaborates it once per module instead
of once per instantiation site". Three records, one per master, each holding
exactly the facts that master already required.

### 9.1 Is the collapsed record TEMPLATE content? MEASURED: NO

**`[LJ-1.153]` measured its 55 lines of repair at 100 percent template. These
records are at zero.** I counted the tower-specific names in the field types:

| name | `UFacts` | `LFacts` | `TFacts` | where it comes from |
|---|---:|---:|---:|---|
| `numeralL` | 16 | 16 | 28 | `L.Axioms.Numerals` |
| `prʟ` | 2 | 2 | 2 | `L.Coding.Model` |
| `envSetAt`, `envOverAt` | 6 | 6 | 9 | `L.Coding.Model` |
| `tmValAt`, `subValAt`, `subValSuccAt`, `consAtL` | 6 | 7 | 13 | `L.Coding.Model` |
| `sucV` | 1 (telescope) | 0 | 1 (telescope) | the hierarchy |

**Every record names the L tower in nearly every field**, and `S` itself is
`hPropStructure 𝒮ʟ`. **The J tower would need its own record and could share
none of these fields.**

**What DOES transfer is the SHAPE, and it transfers whole.** The rule is "state
a frame's fact block as ONE record parameter, and keep any field whose type
names a transparent construction in the telescope". **That is tower-free, it is
measured three times in this report, and it is what a J-side frame would
reuse.** `[LJ-1.155]` section 8.5 already proposed it as a law; this task adds
the second and third measurements it lacked.

**So DD4's answer is: the code shares nothing and the LAW shares everything.**
I state that plainly rather than claim a sharing the grep refuses.

## 10. ARCHIVE USED (DD18)

**I read the three archived files the brief names and I say what I took and
what I refused, at `file:line`.**

- **`archive/src/2026-08-06-four-dead-modules/L/Rud/CodePred.lagda.md:238-246`.**
  **THE RETIRED ROUTE HIT THIS CLASS AND CHOSE THE TELESCOPE.** `module Pred`
  states EIGHT frame facts as telescope hypotheses: `Wtr`, `C∈`, `prIn`,
  `numIn`, `sglIn`, `cupIn`, `∅∈W`, `codeIn`. **TOOK:** the shape, which is the
  same fact class this task collapses, and the census figure that its telescope
  was small. **REFUSED:** its own prose at `:230-235`, which states as a
  standing rule that "writing this chapter on a telescope rather than at a
  stage is what keeps the concrete layer out of every type below, and that is
  the standing rule for a construction this size". **That rule is about WHAT is
  abstracted, never about HOW MANY hypotheses a telescope may carry, and the
  retired route never measured the second question.** At eight hypotheses it
  never had to; at 60 it would have.
- **`archive/src/2026-08-05-realize-cone/L/Rud/Realize.lagda.md:115-160`.**
  `module Basis` carries the longest telescope in the archive: about twenty
  operation-and-specification PAIRS, each spec several lines. **TOOK:** the
  confirmation that the retired route's answer to a long fact block was always
  a longer telescope, never a record. **REFUSED:** every claim about the
  realization cone; `[LJ-1.11]` ruled the retired route's condensation target
  classically FALSE and nothing here rests on its mathematics.
- **`archive/src/2026-08-09-rud-route/L/LevelFormula.lagda.md:94`.** `module
  LevelAt (α : S) (K : ⟪ Lset α ⟫)` is a TWO-parameter telescope and its facts
  are named `Type`s below it (`isLimit` at `:105`, `limitClause` at `:111`,
  `Approx` at `:118`). **TOOK:** the naming move, which is `someEnvDef`'s move
  in `LowerAgree.lagda.md:51` and is why that one hypothesis reads in one line.
  **REFUSED:** the file's mathematics, same reason as above. **This file is NOT
  an instance of the class:** two parameters cost nothing and the archive grep
  that named it for telescope shape over-reaches.
- **`archive/src/2026-08-09-rud-route/L/Recursion.lagda.md:103-107`, `:311-318`
  and `:320-328`.** Found by grep for `record` across `archive/src/`, not named
  in the brief. **TOOK, and it is the shape the edit uses:** `record Recursion`
  and `record Definition` state a fact block as a record whose prose reason at
  `:88` is "a record names them, so an instance is a filled-in form rather than
  a re-run argument"; and `asRecursion` at `:320` BUILDS one record from
  another's fields, `record { dom = D.dom ; graph = D.graph ; ... }`, which is
  exactly what `TwelveAgree` now does to feed `LowerAgree` and `UpperAgree`.
  **So the retired route did know the record form; it applied it to a five-field
  interface and never to a frame's fact block.**
- **`agents/tasks/LJ-1-155/lj-1.155-report.md`, read WHOLE**, and its fourteen
  probes. **TOOK:** the controlled-pair method at `:250-274`; the wall census
  at `:318-334`, which is why `sucK` never becomes a field; the `sucV`
  bisection at `:353-377`, both directions; the cone table at `:397-421`, which
  is why this cure cannot move the baseline; the generator
  `gen_record_probe.py`, which `agents/tasks/LJ-1-158/gen_probe.py` extends
  rather than copies (C-26). **REFUSED, and MEASURED as wrong:** its telescope
  census at `:193-197`, which counts the `Fin` block and the `γ` line as
  hypotheses and is 2 high in every row (section 2 above).
- **`agents/tasks/archive/LJ-1-62/`**, where `KFacts` came from, and the record
  itself at `src/L/Condensation.lagda.md:5996-6032` with its reason at
  `:5990-5994`. **TOOK:** the reason, in the repository's own words, "one
  record, so a transfer module states the block as ONE parameter and
  re-elaborates it once per module instead of once per instantiation site", and
  the `KFactsCons` shape at `:6039` for building a record from a record.
  **REFUSED: `KFacts` itself does not fit and section 9 says why.**
- **`dev/LESSONS.md`, read whole at each entry.** P-x at `:3582`, **TOOK** the
  law and its action, which is why `sucK` stays a telescope fact in all three
  masters; and I did NOT revisit its refutation. P-l at `:2323`, **TOOK** the
  rule that a cure does not transfer by analogy, which is why section 3
  measures `LowerAgree` and `TwelveAgree` before the edit rather than after.
  P-t at `:2619` and P-q at `:2651`, **TOOK** the line-lever and seconds-lever
  split, which is why section 4 adds lines and deletes no content. P-y at
  `:3704`, **TOOK** its warning that a cure in shared code can make the ratio
  worse, which is the contrast this task is funded on. C-40 at `:3620`,
  **TOOK** the consumer rule, which is section 8. C-12 at `:2093`, one process
  at the cap. C-22 at `:2255`, the incremental deliverable. P-p at `:2688`,
  **TOOK** the rule that a stale interface masquerades as a heap wall, which is
  why every probe run deletes its own `.agdai` first. D-1 at `:1038`, the probe
  doctrine and its abort criterion fixed in advance.
- **`scripts/check-probes.py:1-40`.** **TOOK:** that `agents/tasks` is a second
  Agda include root, so a probe is written and RUN in its final home.
- **`bedrock.agda-lib`.** **TOOK:** the same fact from the tool that states it.

## 11. LITERATURE (DD18)

**Nothing in the literature governs a module telescope.** The term measured
here is a property of Agda 2.8.0's dead-code pass.

## 12. NEGATIVES, classified as the brief asks

- **`TwelveAgree` failing to behave like `UpperAgree`: REFUTED. MEASURED.**
  Probes T1 and T2, two runs each, `DeadCode` 13,018 ms to 95 ms. P-l did not
  fire here, and I looked for it before I edited anything.
- **A second walling hypothesis anywhere in the family: DOES NOT EXIST, so far
  as 60 fields can show. MEASURED.** Probe T2 states 59 of `TwelveAgree`'s 60
  as fields, including all 24 that `UpperAgree` lacks, and is GREEN at 6.4 s.
  **This closes `[LJ-1.155]`'s second unmeasured term.**
- **`sucK` as a record field: NOT RETRIED, by instruction, and it stays a
  telescope hypothesis in `UpperAgree` and `TwelveAgree`.** `[LJ-1.155]`
  measured it in both directions and P-x carries the law.
- **`KFacts` as the record for these three: REFUSED. MEASURED against its own
  field list.** It would add `carrierK`, `innerPairK` and six `tagEq` and six
  `numK` to each partial, which changes what the theorem says. Section 9.
- **The collapsed record as TEMPLATE content: REFUTED. MEASURED by name
  census.** Every record names `numeralL`, `prʟ` and the `L.Coding.Model`
  readers. The SHAPE transfers; the record does not. Section 9.1.
- **A record expression needing its field names in scope: REFUTED. MEASURED.**
  `TwelveAgree` builds `LFacts` and `UFacts` under a `using` clause that binds
  neither record's fields, and it is GREEN.
- **`[LJ-1.155]`'s telescope census: WRONG BY 2 IN EVERY ROW. MEASURED.** It
  counted the `Fin` block and the `γ` line as hypotheses. Its seconds are
  unaffected. Section 2.
- **Any change to a theorem statement: REFUTED. MEASURED** by diff against
  `git show HEAD:` for every signature in all three masters. Section 4.2.
- **`src/Everything.lagda.md` as a broken consumer: INFERRED SAFE, NOT
  MEASURED.** Three bare `import` lines, unchanged module names. `make check`
  settles it and the brief reserves it.
- **A heap wall anywhere in this task: NONE. MEASURED.** Nine probe runs at the
  8 GB cap and three master checks, all exit 0. **The cap was never raised.**
- **`LowerAgree` beating its own probe by 27 points: MEASURED, UNEXPLAINED.**
  Section 6.1. I name P-w as the first place to look and price it as a
  hypothesis, not a finding.
- **The wing meeting the DD24 bar: NO. MEASURED.** 1.60x against a 1.15x
  tolerance, and 48.7 s still to find.

## 13. THE PROBES AND TOOLS

Four probes and four tools, tracked, beside this report under
`agents/tasks/LJ-1-158/`. Nothing under `src/`, and `check-probes.py --check`
is clean.

| file | question | verdict |
|---|---|---|
| `ProbeLJ1158L1.agda` | `LowerAgree`'s 37 as a TELESCOPE | 7,243 ms, `DeadCode` 2,689 |
| `ProbeLJ1158L2.agda` | the same 37 as a RECORD | **3,726 ms, `DeadCode` 26** |
| `ProbeLJ1158T1.agda` | `TwelveAgree`'s 60 as a TELESCOPE | 20,958 ms, `DeadCode` 13,018 |
| `ProbeLJ1158T2.agda` | 59 of them as a RECORD, `sucK` kept | **6,421 ms, `DeadCode` 95** |
| `gen_probe.py` | generates any of the four | extends `[LJ-1.155]`'s generator |
| `apply_collapse.py` | performs the master edit, verbatim | the landed cure |
| `run158.py` | refuses to run beside another agda | C-12 |
| `runprobes.sh`, `checkmasters.sh` | the two series | cold every run |

## 14. WHAT I DID NOT DO

- **I did not commit and did not push.**
- **I did not run `make check`.** The brief reserves it, and it is the one
  thing that closes `src/Everything.lagda.md`.
- **I did not touch `src/Everything.lagda.md` or
  `src/L/Coding/Graph.lagda.md`.**
- **I did not try `sucK` as a record field.** Measured twice already.
- **I did not delete a line to improve a ratio.** The wing gained 108 lines.
- **I did not price the `L/Condensation` term.** Section 6.2 names it and its
  probe.
