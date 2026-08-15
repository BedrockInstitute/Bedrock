# [LJ-1.309] report: sweep the WHOLE `src/` tree for R-41's full-chain shape

STATUS: COMPLETE against the abort criterion's THIRD branch, which DID NOT
FIRE, with phase 2 run because a slot was free. Written incrementally (C-22).
Every negative is marked MEASURED or INFERRED, in those words. ASD-STE100
applies.

Machine at start: `ps aux | grep '[a]gda '` returned TWO lines at 21:27, but
only ONE was an agda binary (PID 47220, the sibling `[LJ-1.305]` on
`Untruncated.agda`). The second line was that process's own `/bin/bash -c`
wrapper, whose command string contains `agda `. MEASURED. So ONE C-12 slot was
free at start. Re-checked at 21:32: one agda binary (PID 51469, `[LJ-1.305]` on
`UntA.agda`), load averages 6.61 6.11 7.90. One slot still free.

## LEAD

**THE STRONG READING FINDS THREE FULL-CHAIN SITES IN `src/`. THE DEEPEST
DEPTH IS 2.** All three sit in ONE master, `src/L/Coding/Key.lagda.md`, inside
the tower-neutral module `KeyOver`.

**NO SITE AT DEPTH 3 OR MORE EXISTS IN `src/`. MEASURED.** The brief's third
abort branch, "a site at depth 3 or more exists", DID NOT FIRE. R-41's ladder
charges 9,286 ms at depth 3 and 419,218 ms at depth 4
(`agents/tasks/LJ-1-292/lj-1.292-report.md:39`). **The delivered tree buys none
of that.** The ladder's paying rungs are empty.

**The deepest explicit `sucV` chain anywhere in `src/` is depth 3**, at
`src/L/Coding/EnvSupply.lagda.md:216`, and it is NOT against an iterate. It is
`[LJ-1.289]`'s landed cure, and every conversion in its block is chain against
chain, one spelling. MEASURED: the enclosing `where` block, `:209-226`, holds
no `sucIter` token.

**AND THE CENSUS REFUTES ONE SENTENCE IN THE SIBLING REPORT THIS TASK STARTS
FROM.** `agents/tasks/LJ-1-292/lj-1.292-report.md:23-25` calls its own top
charge, `KeyOver._.pair∈` at `src/L/Coding/Key.lagda.md:118-119`, "a
bounded-formula membership climb with no `sucIter` mismatch in it". **That site
carries the strong shape.** Its type at `:118` reads `T (sucIter 2 σ)`; its
proof calls `T-pr σ`, whose declared type at `:85-86` produces
`T (sucV (sucV σ))`. **A full explicit chain of depth 2 against a numeral
iterate is exactly the shape `[LJ-1.292]` told the project to grep for.** The
sibling measured that definition at **261 ms**, the master's top charge
(`lj-1.292-report.md:93`), and its own ladder prices a depth-2 full chain at
**219 ms** (`:124`). The two numbers agree within 19 percent.

**AND I MEASURED THE SHARE RATHER THAN ASSUME IT (C-50, P-l).** The ladder was
priced on a BARE membership, while all three delivered sites run under an
ABSTRACT stage function `T`. **A generic `T` was a plausible shield. It is
not.** My arm `t2` prices the site's own conversion, in its own setting, at
**219 ms**, against the bare arm `b2` at **221 ms**, one percent apart in one
run (section 4). **So about 219 of `pair∈`'s 261 ms, about 84 percent, is the
mixed spelling. MEASURED.**

**AND THE PRIZE IS STILL SMALL.** `Key.lagda.md`'s whole cold total is 3,974 ms
(`lj-1.292-report.md:84`), and the master is in NEITHER DD4 closure, so its
seconds are paid ZERO times on the AC-against-GCH axis. **The whole cure is
worth 219 ms delivered, plus 0 to 522 ms unresolved, against DD24's 60.0 s
standing gap: 0.4 to 1.2 percent.** Section 8 shows the cure is a vocabulary
change across two masters and that the naive half-cure would move the mismatch
from depth 2 to depth 3, 42 times worse. **I recommend against funding it.**

**The 400-second depth-4 hope the brief funded is not in the tree. MEASURED.**

## 0. PREMISES, VERIFIED OR REFUTED (C-44)

| the brief's premise | verdict |
|---|---|
| the standing tree is 94 masters, 32,488 lines | **VERIFIED.** `.venv/bin/python scripts/measure/ledger.py --brief` prints "standing 32,488 lines over 94 masters, measured from HEAD". `find src -name '*.lagda.md'` returns 96; `scripts/measure/ledger.py:112` excludes `src/Everything.lagda.md` and `src/Landmarks.lagda.md` as indexes. 96 minus 2 is 94 |
| R-41 is at `dev/LESSONS.md:4247` | **VERIFIED.** The heading is at `:4247` and the entry runs to `:4318`. I read it whole |
| the two known sites are `EnvSupply.lagda.md:223-224` and `Key.lagda.md:424-429` | **VERIFIED with a correction on the first.** `[LJ-1.289]`'s cure moved the block: the chain now sits at `src/L/Coding/EnvSupply.lagda.md:214-216` and the site runs `:209-226`. The `Key` site is at `:424-429` as stated |
| `Condensation.lagda.md` is the wing's largest single cost, so sweep it first | **VERIFIED as a cost claim and REFUTED as a sweep order.** I swept it. It holds 12 `sucV` tokens and **ZERO `sucIter` tokens. MEASURED.** It carries no explicit chain of depth 2 or more. It cannot hold the shape, and sweeping it first bought nothing |
| the ladder holds in `Condensation` (P-l) | **MOOT. MEASURED.** No site there, so no hypothesis to test |

## 1. THE SHAPE, AS `[LJ-1.292]` MEASURED IT

**THE STRONG READING**, from `agents/tasks/LJ-1-292/lj-1.292-report.md:245-247`
and its controlled pair at `:160-164`:

- **COSTLY:** a fully explicit `sucV` chain of depth 2 or more on one side of a
  conversion, and a numeral `sucIter` iterate on the other. Arm `w4`,
  419,218 ms.
- **FREE:** ONE `sucV` directly over an iterate, at every depth measured. Arms
  `d2`, `d3`, `d4`, none charged.
- **FREE:** the same spelling on both sides, at every depth. `envSetK` is
  depth 4 in one spelling and costs 11 ms (`dev/LESSONS.md:4268-4269`).

**So the census counts EXPLICIT `sucV` CONSTRUCTORS WRITTEN OUT, and never the
numeral.** `sucV (sucV (sucIter 5 σ))` against `sucIter 7 σ` is a DEPTH-2
instance, not a depth-7 instance: the conversion closes at `sucIter 5 σ`,
which both sides spell the same way.

## 2. THE CENSUS

### 2.1 THE GREP, so a later reader can re-run it

Two greps bound the search, and together they are complete.

```
grep -rn 'sucV *( *sucV' src --include='*.lagda.md'      # explicit chains, depth >= 2
grep -rln 'sucIter' src --include='*.lagda.md'           # every numeral-iterate file
```

- **The first returns SEVEN lines in FIVE files.** MEASURED.
- **The second returns FOUR files.** MEASURED: `src/L/Ordinal/StageArith.lagda.md`,
  `src/L/Coding/Bound.lagda.md`, `src/L/Coding/Key.lagda.md`,
  `src/L/Coding/EnvSupply.lagda.md`. **No other master in `src/` names an
  iterate at all**, so no other master can hold the shape.
- **A line-broken chain would escape the first grep, so I ran a second pass**
  with a whole-file regular expression that crosses newlines
  (`perl -0777` over all 96 masters). **It returns the SAME seven lines.
  MEASURED: no chain in `src/` is split across lines.**
- **An alias can hide a chain**, as `EnvSupply.lagda.md:214-216` does. So I
  also ran `grep -rn '= *sucV\b' src --include='*.lagda.md'`, which returns 53
  lines. **Every one outside `EnvSupply.lagda.md` binds a chain of depth 1**
  (`s k = sucV (rank ...)`, `β = sucV (γp p)`, `g x = sucV (f x)`), **and none
  of their files names an iterate. MEASURED.**
- **Only `sucIter` builds a numeral stage iterate in `src/`.** MEASURED:
  `sucIter : ℕ → S → S` at `src/L/Ordinal/StageArith.lagda.md:34-36` is the
  only ℕ-recursive stage helper. The numeral set `#` is a different object; no
  site writes `sucV (sucV (# k))` against `# (k + 2)`, because the seven chain
  lines are the complete list and none of them does.

**The intersection is therefore three files**, and I read every `sucIter`
occurrence in all four, 51 lines in total.

### 2.2 THE FULL-CHAIN SITES, RANKED BY DEPTH, DESCENDING

**THREE SITES. DEEPEST DEPTH 2.**

| rank | site | depth | the TYPE side | the SUPPLIER side | type or term | DD4 closure |
|---:|---|---:|---|---|---|---|
| 1 | `src/L/Coding/Key.lagda.md:118-120`, `KeyOver.paramEnv∈._.pair∈` | **2** | `T (sucIter 2 σ)` at `:118`, a numeral iterate | `T-pr σ ...` gives `T (sucV (sucV σ))`, declared `:85-86` | **type**, a signature inside a `where` | **NEITHER** |
| 2 | `src/L/Coding/Key.lagda.md:129-131`, `KeyOver.splitKey∈`, outer `T-pr` | **2** | `T (sucIter 7 σ)` at `:129` | `T-pr (sucIter 5 σ) ...` gives `T (sucV (sucV (sucIter 5 σ)))` | **type**, the declared conclusion | **NEITHER** |
| 3 | `src/L/Coding/Key.lagda.md:133`, `KeyOver.splitKey∈`, inner `T-pr` | **2** | `T (sucIter 5 σ)`, the outer `T-pr`'s second argument slot | `T-pr (sucIter 3 σ) ...` gives `T (sucV (sucV (sucIter 3 σ)))` | **term**, an argument position | **NEITHER** |

**No row at depth 3. No row at depth 4. MEASURED.**

### 2.3 THE DEPTH-1 SITES, which the brief asks me to list because the count matters

**ELEVEN depth-1 conversions**, each ONE `sucV` directly over an iterate. This is
`[LJ-1.292]`'s `d`-family and it is FREE at every depth measured
(`lj-1.292-report.md:156-158`).

| site | the pair | numeral or variable |
|---|---|---|
| `src/L/Ordinal/StageArith.lagda.md:69`, `+ω-iter` | `sucV (sucIter n u)` against `sucIter (suc n) u` | variable |
| `src/L/Coding/Key.lagda.md:96`, `fromω` zero | `sucV σ` against `sucIter 1 σ` | numeral |
| `src/L/Coding/Key.lagda.md:98-99`, `fromω` suc | `sucV (sucIter (suc d) σ)` against `sucIter (suc (suc d)) σ` | variable |
| `src/L/Coding/Key.lagda.md:102`, `fromω′` zero | `sucV σ` against `sucIter 1 σ` | numeral |
| `src/L/Coding/Key.lagda.md:103`, `fromω′` suc | `sucV (sucIter (suc e) σ)` against `sucIter (suc (suc e)) σ` | variable |
| `src/L/Coding/Key.lagda.md:113-115`, `paramEnv∈` | `sucV (sucIter 2 σ)` against `sucIter 3 σ` | numeral |
| `src/L/Coding/Key.lagda.md:428`, `σ∈α` outer | `sucV (sucIter 2 σ)` against `sucIter 3 σ` | numeral |
| `src/L/Coding/Key.lagda.md:429`, `σ∈α` middle | `sucV (sucIter 1 σ)` against `sucIter 2 σ` | numeral |
| `src/L/Coding/Key.lagda.md:429`, `σ∈α` inner | `sucV σ` against `sucIter 1 σ` | numeral |
| `src/L/Coding/Key.lagda.md:275,480-481`, `landed` | `sucV (sucIter 3 σ)` against `sucIter 4 σ` | numeral |
| `src/L/Coding/Bound.lagda.md:99`, `suc^∈λ` | `sucV (sucIter k σ)` against `sucIter (suc k) σ` | variable |

**THE SHAPE IS RARE, and the count says so.** Eleven depth-1 conversions and
three depth-2 conversions across 94 masters. **Every one of them lives in the
four masters that name `sucIter`, and 90 masters cannot hold the shape at all.
MEASURED.**

**`src/L/Coding/Key.lagda.md:424-429` is the site `[LJ-1.287]` flagged and
`[LJ-1.292]` cleared. My census agrees with `[LJ-1.292]`: it is depth 1 three
times over, MEASURED, and it is not charged in that task's profile
(`lj-1.292-report.md:104`).**

### 2.4 THE MATCHED-SPELLING SITES, listed so the census is closed

These carry `sucIter` and `sucV` in one file but never in one conversion, so
they are outside both readings.

| site | why it is free |
|---|---|
| `src/L/Ordinal/StageArith.lagda.md:96`, `envCloses` | `+ω-iter 3 δ` gives `sucIter 3 δ` and the type says `sucIter 3 δ`. One spelling |
| `src/L/Coding/EnvSupply.lagda.md:144-145`, `envSetK` | `B.suc^∈λ 4 σ σ∈λ` gives `sucIter 4 σ` and the type says `sucIter 4 σ`. One spelling. **MEASURED at 11 ms** (`dev/LESSONS.md:4268-4269`) |
| `src/L/Coding/Bound.lagda.md:114-115`, `Iter.pow∈λ` | `suc^∈λ k (sucV δ)` gives `sucIter k (sucV δ)` and the type says the same. Variable `k`, so nothing unfolds |
| `src/L/Coding/Bound.lagda.md:77-78`, `climb` | `succλ (sucV σ) (succλ σ σ∈)` gives `sucV (sucV σ)` and the type says `sucV (sucV σ)`. **`Bound.lagda.md` holds ZERO numeral iterates. MEASURED** |
| `src/L/Axioms/Basic.lagda.md:596-599`, `pr∈Lset-suc` | chain against chain. **`Basic.lagda.md` holds no `sucIter`. MEASURED** |
| `src/L/Cardinal.lagda.md:73`, `hSucα` | `ord∈Lset-suc (sucV (fst α))` gives `Lset (sucV (sucV (fst α)))` and the type says the same. **`Cardinal.lagda.md` holds no `sucIter`. MEASURED** |
| `src/L/Coding/EnvSupply.lagda.md:209-226`, `sucK.step` | depth 3 chain, chain against chain throughout. `[LJ-1.289]`'s landed cure. **The block holds no `sucIter`. MEASURED** |

## 3. THE WEAK READING, and how many it would have flagged

**`[LJ-1.287]`'s weak reading is stated at
`agents/tasks/LJ-1-287/lj-1.287-report.md:391-394`:** a `sucIter` at a numeral
depth on one side of a conversion and an explicit `sucV` chain on the other,
searched by `grep -rn "sucIter" src/`, which that report counted at **34
occurrence lines outside `StageArith.lagda.md`**.

**I re-derived that count (C-44), and it reproduces after one correction for a
landed cure.** `grep -rn 'sucIter' src --include='*.lagda.md'` returns **51**
lines today; `StageArith.lagda.md`, the defining master, holds **19**; 51 minus
19 is **32**, not 34. **The gap is `[LJ-1.289]`'s cure. MEASURED:**
`git show 92f558f^:src/L/Coding/EnvSupply.lagda.md | grep -c sucIter` returns
**5** and the same grep at HEAD returns **3**, so that landing removed exactly
two iterate lines. **32 plus 2 is 34, and `[LJ-1.287]`'s figure reproduces on
the bytes it was measured against.**

| reading | what it flags | count |
|---|---|---:|
| **WEAK**, `sucIter` beside `sucV` in one file | four files, and by occurrence line **32** candidate lines outside the defining master today, 34 when `[LJ-1.287]` ran | **32 lines, 3 files** |
| **WEAK as `[LJ-1.287]` actually triaged it** | it cleared 6 lines by variable depth and 1 site by one spelling, and flagged **ONE** site, `Key.lagda.md:424-429` | **1 site flagged** |
| **STRONG**, full explicit chain against numeral iterate | **3 sites, all depth 2, all in `Key.lagda.md`** | **3 sites** |

**WHICH READING THE PROJECT SHOULD KEEP: THE STRONG ONE, AND THE CENSUS SHOWS
WHY IN BOTH DIRECTIONS.**

- **The weak reading has a FALSE POSITIVE that cost a whole dispatch.** It
  flagged `Key.lagda.md:424-429`, and `[LJ-1.292]` spent a task measuring it
  clean. The strong reading clears that site by reading alone, in seconds.
- **The weak reading also has a FALSE NEGATIVE, and this is the new finding.**
  `[LJ-1.287]` triaged the 34 lines and cleared `Key.lagda.md:113,115,118`
  implicitly by not naming them. **`:118` carries the strong shape.** The weak
  reading looked at the wrong three lines in the right file.
- **The strong reading is GREPPABLE, and cheaply.** The brief's fourth abort
  branch, "the strong reading is not greppable", **DID NOT FIRE.** Two greps
  and a 51-line read closed the tree. **A checker is possible**, and section 6
  states its shape and its false-positive cost.

## 4. THE PROFILE, and it settles the P-l question with a number

**THE SLOT.** Before the run I counted the agda binaries, not the `ps` lines.
`ps aux | grep '[a]gda '` returned four lines at 21:36: ONE agda binary (PID
54678, `[LJ-1.305]` on `UntA.agda`), that process's `/bin/bash -c` wrapper, and
my own `grep` command line, which contains the string `agda `. **ONE binary was
live, so one C-12 slot was free. I ran ONE process, `GHCRTS="-A64m -I0 -M8g"`,
cap never raised.**

**WHY I DID NOT RE-PROFILE THE TOP-RANKED MASTER.** The top-ranked master is
`src/L/Coding/Key.lagda.md`, and `[LJ-1.292]` already profiled it cold at
3,974 ms. **I verified the bytes are the same. MEASURED:**
`git log -1 -- src/L/Coding/Key.lagda.md` returns `0abbcaa`, the commit
`[LJ-1.292]` names at its `:19-21`, and `git diff HEAD` on that path is empty.
**So the sibling's profile describes today's delivered bytes and a second run
would buy the project a number it already owns.** The measurement nobody owns
is the one below, and it is what the census made necessary.

**THE ARM, and it is P-l made concrete.** `[LJ-1.292]` priced the depth-2 full
chain on a BARE membership with a variable base. **All three delivered sites
run under an ABSTRACT stage function `T`**, a module parameter at
`src/L/Coding/Key.lagda.md:83`. **Whether the ladder transfers to that setting
was a hypothesis, not a price.** `Chain2.lagda.md`, 5 definitions, 20 non-blank
in-fence lines, `--profile=definitions`, ONE run, cold in the module and warm
in its dependencies.

**Wall 1.69 s, exit 0, load 7.04 6.63 7.64 flat across the run, agda Total
1,540 ms** (`agents/tasks/LJ-1-309/runs/c1.out`).

| arm | what it isolates | ms |
|---|---|---:|
| `t7` | census ranks 2 and 3: depth-2 chain over an ITERATE base, against `sucIter 7 σ`, abstract `T` | **261** |
| `b2` | `[LJ-1.292]`'s `w2` re-measured: depth-2 chain against `sucIter 2 σ`, BARE membership | **221** |
| `t2` | **census rank 1, the site's own setting**: depth-2 chain against `sucIter 2 σ`, abstract `T` | **219** |
| `m2` | the matched-spelling control, abstract `T` | **not charged** |
| `d2` | the free spelling, one `sucV` over the iterate | **not charged** |
| Miscellaneous | | 838 |

**THREE THINGS ARE NOW MEASURED AND EACH ONE MATTERS.**

- **THE ANCHOR HOLDS.** `b2` returns **221 ms** against `[LJ-1.292]`'s `w2` at
  **219 ms** (`lj-1.292-report.md:124`), **within 1 percent under a different
  load**. My harness sees the disease, so the negatives below are not
  instrument blindness.
- **THE ABSTRACT STAGE FUNCTION DOES NOT PROTECT THE SITE. MEASURED, and this
  is the P-l answer.** `t2` costs **219 ms** and `b2` costs **221 ms**, one
  percent apart in one run. **The ladder transfers to the delivered sites'
  setting.** A generic `T` was a plausible shield, because the payload could
  stay stuck under a variable head. **It is not a shield.**
- **THE ITERATE BASE COSTS SLIGHTLY MORE, NOT EXPONENTIALLY MORE.** `t7` costs
  **261 ms** against `t2`'s 219 ms, 19 percent apart. **A depth-2 chain over an
  iterate base is still a DEPTH-2 instance.** The census's reading of
  `sucV (sucV (sucIter 5 σ))` as depth 2 rather than depth 7 is confirmed:
  depth 7 would be far above the ladder's 419,218 ms at depth 4.
- **THE MATCHED SPELLING AND THE ONE-DEEP SPELLING ARE BOTH FREE UNDER AN
  ABSTRACT `T`. MEASURED.** `m2` and `d2` do not appear in the profile, in the
  same run that charges three arms beside them. **So the cure direction is
  intact: respelling removes the cost, at depth 2 as at depth 4.**

### 4.1 THE ATTRIBUTION, and it corrects the sibling report with a number

`[LJ-1.292]` measured `KeyOver._.pair∈` at **261 ms** in the delivered master
(`lj-1.292-report.md:93`). **My `t2` prices that definition's level conversion,
in isolation and in its own setting, at 219 ms.**

**So about 219 of `pair∈`'s 261 ms, about 84 percent, is the mixed spelling.
MEASURED by two runs on the same shape, one in the master and one isolated.**
The sibling's sentence that `pair∈` carries "no `sucIter` mismatch in it" is
REFUTED, and the master's top charge has a mechanism.

### 4.2 ONE THING I DID NOT RESOLVE, and I mark it INFERRED

**`splitKey∈` does not appear in `[LJ-1.292]`'s profile at all**, so its
delivered cost is below that profiler's reporting threshold. MEASURED by
absence, in a table that reports down to 12 ms (`lj-1.292-report.md:103`).
**Yet its shape, isolated as `t7`, costs 261 ms.** The two measurements do not
reconcile and I did not resolve them. **INFERRED**, and offered as a
hypothesis only: the conversion at `splitKey∈` may be discharged while Agda
solves the implicit level arguments, and the profiler may then charge it to
`Miscellaneous`, which is 2,417 ms and 60.8 percent of that run. **I did not
read Agda's conversion checker and I do not claim this.**

**So the honest bound on census ranks 2 and 3 is a RANGE, not a price:**
between "below the profiler's threshold in the delivered master, MEASURED" and
"261 ms each in isolation, MEASURED". **Only rank 1 has a delivered price.**

## 5. DD4, WITH ITS AXIS

**AXIS NAMED (C-46): AC-against-GCH**, computed by `scripts/measure/ledger.py`
from `ac_root` and `gch_root`. A respelling changes SECONDS and not lines, and
it changes them in whichever wing the site sits in.

**ALL THREE SITES SIT IN `src/L/Coding/Key.lagda.md`, WHICH IS IN NEITHER
CLOSURE.** I re-derived the closure figures rather than quoting them (C-44):
`.venv/bin/python scripts/measure/ledger.py --reuse` prints AC closure 73
masters and 17,197 lines, GCH closure 51 masters and 9,967 lines, SHARED 44
masters and 7,632 lines, 39.1 percent of 19,532. `Key.lagda.md` appears in
none of the three, which reproduces `[LJ-1.292]`'s own import walk
(`lj-1.292-report.md:208-217`).

**THE DD4 READING OF THIS SWEEP.** A site in BOTH closures is worth more than a
site in one. **Not one of the three sites is in either.** So the seconds this
census found are paid ZERO times on the DD4 axis today, and a cure would move
the axis by nothing.

**BUT THE SITES ARE WRITTEN GENERIC, AND THAT IS THE DD4 WIN ALREADY BANKED.**
All three sit inside `module KeyOver (T : S → S) ...` at
`src/L/Coding/Key.lagda.md:82-91`, which takes the stage function and five
facts as parameters and names no tower. The master's own comment says so at
`:78-81`. **The conversions are checked ONCE in the generic module and not once
per tower**, so when a closure grows to include this master, the cost is paid
once. **The generic writing is what keeps the shape's price flat in the number
of towers. That is DD4 doing its job before any cure.**

## 6. THE ABORT CRITERION, ANSWERED BRANCH BY BRANCH

| branch fixed before the run (D-1) | verdict |
|---|---|
| **the tree holds no further full-chain site** | **DID NOT FIRE. MEASURED.** Three sites exist and section 2.2 names them. The count of files searched is **96 masters**, of which 94 are counted by the ledger; the greps are printed at section 2.1 so a later reader can re-run them |
| **the tree holds sites at depth 1 only** | **DID NOT FIRE, and it came close. MEASURED.** Eleven depth-1 conversions and three depth-2 conversions. R-41 is NOT delivered-tree-clean, but the ladder's paying rungs are empty |
| **a site at depth 3 or more exists, and that is the hit** | **DID NOT FIRE. MEASURED. This is the report's main negative.** The deepest full-chain site in `src/` is depth 2. The deepest explicit chain of any kind is depth 3, at `src/L/Coding/EnvSupply.lagda.md:216`, and it is matched on both sides. **The 400-second depth-4 prize the brief funded is not in the delivered tree** |
| **the strong reading is not greppable** | **DID NOT FIRE. MEASURED.** Two greps plus a 51-line read closed the whole tree in phase 1, with no Agda. Section 7 states what a checker would cost |
| a wall | **DID NOT FIRE. MEASURED.** One agda run, wall 1.69 s, exit 0. No heap exhaustion, cap never raised |

## 7. A CHECKER IS POSSIBLE, and here is its price in false positives

The brief's fourth branch asked what a mechanical proxy would cost. **It is
cheap, because the shape has a two-token signature.**

**THE RULE:** flag a file only if it contains BOTH a token matching
`sucV *( *sucV` and a token matching `sucIter`. **On today's tree that is
THREE files** (`Bound`, `Key`, `EnvSupply`), and within them a reader checks
14 conversions.

**THE FALSE-POSITIVE COST, MEASURED on today's tree:** of those three files,
**`Bound.lagda.md` is a false positive**, because it holds zero numeral
iterates; its indices are all variables and nothing unfolds. **So the file-level
proxy is 1 false positive in 3, about 33 percent.**

**A TIGHTER PROXY CUTS THAT TO ZERO TODAY:** require `sucIter *[0-9]`, a
numeral iterate, instead of bare `sucIter`. **That returns `StageArith` (2
lines), `Key` (17) and `EnvSupply` (2), and drops `Bound` correctly. MEASURED.**

**WHAT NO PROXY CAN DO. INFERRED.** The proxy names a FILE, never a
conversion. Deciding which of `Key.lagda.md`'s 19 iterate conversions is
depth 2 rather than depth 1 needs the supplier's declared type, which needs
name resolution across modules. **A checker can therefore gate "read this
file", and it cannot gate "this line is costly".** That is still worth having:
it turns a tree-wide sweep into a three-file read.

## 8. THE RESPELLING, AS A DIFF I DID NOT APPLY, AND WHY I RECOMMEND AGAINST IT

**The brief asks for a respelling for any site at DEPTH 3 OR MORE. No such site
exists, so the trigger did not fire.** I give the rank-1 respelling anyway,
because the census found it and the project should see why it is not funded.

**THE NAIVE RESPELLING MOVES THE COST AND DOES NOT REMOVE IT.** R-41 says to
state the index in the spelling its proof produces. At
`src/L/Coding/Key.lagda.md:118` that reads:

```
-    pair∈ : (i : Fin k) → ⟨ pr (# (toℕ i)) (h i) ∈ˢ T (sucIter 2 σ) ⟩
+    pair∈ : (i : Fin k) → ⟨ pr (# (toℕ i)) (h i) ∈ˢ T (sucV (sucV σ)) ⟩
```

**That is wrong on its own, and the ladder says by how much.** `T-fin` at
`:115` would then produce `T (sucV (sucV (sucV σ)))` against the conclusion's
`T (sucIter 3 σ)` at `:113`. **The mismatch moves from depth 2 to depth 3, from
219 ms to the ladder's 9,286 ms, about 42 times worse.** This is R-41's own
warning restated: a seal, and equally a half-respelling, MOVES a cost.

**THE CURE THAT REMOVES IT IS A VOCABULARY CHANGE ACROSS TWO MASTERS.** The
conclusion at `:113` must be respelled too, and then every consumer:
`splitKey∈` at `:129-135`, `memberIn` at `:199`, `setSub` at `:211-214`,
`deliveredSplit∈` at `:159`, `Land.α` at `:424`, `landed` at `:480`,
`envSetNumeral∈` at `:488`, and `src/L/Coding/EnvSupply.lagda.md:144-145`.
**That is not five lines. It is `Key.lagda.md`'s whole iterate vocabulary.**

**THE PRICE AGAINST THE PRIZE, and the prize loses.**

| term | figure | basis |
|---|---:|---|
| rank 1, delivered and attributable | **219 ms** | MEASURED, `t2` against `[LJ-1.292]`'s 261 ms for `pair∈` |
| ranks 2 and 3, delivered | **0 ms to 522 ms** | MEASURED as a RANGE only, section 4.2 |
| the whole master's cold total | 3,974 ms | `lj-1.292-report.md:84` |
| DD24's standing GCH gap | **60.0 s** | `dev/ledger.toml:303-304`, `[LJ-1.218]` kept by `[LJ-1.222]`. **The brief's "about 63 s" is corrected to 60.0 s (C-44)** |
| the cure's share of that gap | **0.4 to 1.2 percent** | arithmetic on the two rows above |
| DD4 value | **ZERO** | the master is in NEITHER closure, section 5 |

**RECOMMENDATION: DO NOT FUND THE CURE. C-50 applied honestly.** I profiled
before proposing, and the seconds do not justify a vocabulary change that risks
moving a depth-2 mismatch to depth 3. **The value of this sweep is the census
and the negative, not a cure.**

**WHAT I WOULD FUND INSTEAD, and it costs nothing:** record the census in R-41
so the next agent does not re-sweep, and add the tighter grep of section 7 to
the build-brief checklist. **A shape that is rare, shallow and outside both
closures is a shape the project can stop hunting.**

## ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-292/lj-1.292-report.md`, read WHOLE as the brief
  requires.** ONE line: `:245-247`, "The costly shape is now measured
  precisely: a full explicit `sucV` chain against a numeral iterate, with or
  without `Lset`, super-linear from depth 2." **TAKEN:** the strong reading,
  which is this census's whole filter, and the ladder at `:39` as a
  comparable. **NOT TAKEN:** its `:23-25` reading of `pair∈` as carrying no
  mismatch. **My census REFUTES that sentence and section 4.1 prices the
  refutation.**
- **`agents/tasks/LJ-1-287/lj-1.287-report.md`.** ONE line: `:402`,
  "`src/L/Coding/Key.lagda.md:424-429` CARRIES THE SHAPE. UNMEASURED."
  **TAKEN AS THE SHAPE OF AN ERROR, as the brief asked:** the weak reading
  looked at the right file and the wrong three lines. **NOT TAKEN:** its 34
  count as a live figure; I re-derived it at 32 today and section 3 shows the
  two-line difference is `[LJ-1.289]`'s landing.
- **`agents/tasks/LJ-1-289/lj-1.289-report.md`.** ONE line: `:92`, "Only the
  declared level changes, from `sucIter 4 δ` to `sucV δ₃`." **TAKEN:** what a
  respelling looks like in a master, which is the template section 8 prices.
  **NOT TAKEN:** its 488.59 s saving as a comparable. **P-l forbids it:** that
  saving was a depth-4 site and every site in this census is depth 2.
- **`archive/dev/TASKS-archived.md`, SHAPE ONLY and never a claim.** ONE line:
  `:223`, `[L3.32-T219]`, "The seconds doctrine: what makes a master expensive
  here. Five diseases; the 21-60x gap is a CONTENT CLASS, not a defect."
  **TAKEN AS SHAPE:** a tree's seconds usually sit in a content class and not
  in one curable spelling, which is what this census found. **WHAT WOULD NOT
  TRANSFER:** every number in the retired route's seconds crisis. Those price a
  different tree under a different head, at depths this tree does not reach. I
  carried none, and I re-measured my one comparable (`b2`) rather than quote it.

## LITERATURE USED (DD18)

**No mathematical literature bears on a typechecker's cost model for a
spelling.** The question is Agda's conversion checker, not set theory. I used
none.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Everything I wrote is in `agents/tasks/LJ-1-309/`:

- `LJ-1.309.md`, the pinned brief, written by the orchestrator before me.
- `lj-1.309-report.md`, this file. **TRACKED and MODIFIED, not untracked**, and
  the reason is not mine: I created it as a skeleton at 21:27, and the sibling
  `[LJ-1.308]`'s commit `a97f650` swept that skeleton into the tree while I
  worked. **I did not commit it and I have committed nothing. MEASURED:**
  `git log -- agents/tasks/LJ-1-309/lj-1.309-report.md` names `a97f650` alone,
  whose subject is `[LJ-1.308] SPLIT: the zero holds`. The orchestrator should
  know that a sibling's commit is picking up other agents' in-progress files.
- `Chain2.lagda.md`, the five-arm bisect. GREEN, exit 0, 1.69 s. Untracked.
- `runs/c1.out`, the profile. Untracked.

**No master edited. No `src/` path written. No `dev/` path written.** I did not
touch `src/Everything.lagda.md`, another task directory, or `AGENTS.md`. **No
commit, no push, no `git checkout .`, no stash, no reset, no clean. I did not
run `make check`.** I ran ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap never
raised, with one C-12 slot verified free before it started.

**A NOTE ON THE SLOT COUNT, because the obvious command over-counts.**
`ps aux | grep -c '[a]gda '` returns 2 to 4 on this machine while only ONE agda
binary runs. The extra lines are the `/bin/bash -c` wrapper that launched it and
the counting command itself, both of which carry `agda ` in their command
strings. **Count lines matching `libexec.*bin/agda`, not lines matching
`agda `.** MEASURED at 21:27, 21:32 and 21:36.
