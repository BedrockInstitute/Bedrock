# LJ-1.274 Report: the DD25 adversarial review of `[LJ-1.273]`'s 1,760

tier: opus (in-harness-subagent-mode). No Agda ran. No slot held. Written
incrementally (C-22). Every negative is MEASURED or INFERRED, in those words.

## 0. ONE WORD ON THE 1,760

**WRONG.**

It is not a bad price of the PROOF. It is the wrong answer to the question the
brief asked. Read the four findings apart.

1. **`gch_root` does not need a proof. It needs a committed module.** MEASURED
   at `scripts/ledger.py:404-446`. The distance to a working DD4 report is
   about **262 to 316 lines**, not 1,760. Section 1.
2. **The point 1,760 is not the centre of its own band.** MEASURED by
   arithmetic on `agents/tasks/LJ-1-273/lj-1.273-report.md:100-106`. The band
   centre is 1,810. The point prices the report's own unpriced tail at ZERO.
   Section 2.1.
3. **The one part with a probe basis contributes ZERO band width.** MEASURED.
   All 300 lines of the band come from the two INFERRED parts. The band is a
   survey wearing a probe's clothes, exactly as the brief feared. Section 2.2.
4. **YES, the brief caused it**, and the mechanism is not the one the
   orchestrator suspected. Section 3.

**What HOLDS.** The 1,089 holds as a probe sum. The chain's SHAPE holds: A7 is
only the statement, and `[LJ-1.7]` plus the final assembly do stand between
today and a proved trophy. The target's C-45 use on A7 is correct.

## 1. THE FOURTH QUESTION: `gch_root` CAN BE DECLARED EARLIER

**This is the money answer and it is MEASURED, not inferred.**

### 1.1 What the tool actually reads

`reuse_report` is `scripts/ledger.py:404-446`. Read it line by line.

- `:417` reads `ac_root` and `gch_root` out of the `[reuse]` table as strings.
- `:419` tests `r not in files`. `files` is `countable_masters()`, bound at
  `scripts/ledger.py:699`. That is every git-tracked `*.lagda.md` under `src/`
  minus the two catalogs at `scripts/ledger.py:97`.
- `:422` returns the "no GCH endpoint" text when `gch_root` is the empty
  string. That is the branch running today.
- `:432` computes `closure(graph, [gch_root])`.
- `closure` is `scripts/ledger.py:391-402`. It is a graph walk.
- `import_graph` is `scripts/ledger.py:377-388`. It applies `IMPORT_RE`
  (`scripts/ledger.py:374`) to `head_text(f)`.

**MEASURED: the tool never reads a proof term. It never reads a type. It never
calls Agda.** It reads lines that match
`^\s*(?:open )?import ([A-Za-z0-9_.]+)`.

**So the requirement at `agents/tasks/LJ-1-273/lj-1.273-report.md:19-21` is
false as a statement about the tool.** The sentence "The theorem in it must be
a proof term. Its type must be `GCHStatement L⊨ZF`" describes HONESTY, not the
code. The target did not separate the two.

### 1.2 The three real conditions

`gch_root` works the day its path meets all three. MEASURED.

| condition | evidence | why |
|---|---|---|
| a tracked `.lagda.md` under `src/` | `scripts/ledger.py:100-117`, `:419` | `git ls-files src/` is the source list |
| not `Everything` or `Landmarks` | `scripts/ledger.py:97` | `countable_masters()` drops both |
| COMMITTED, not only staged | `scripts/ledger.py:119-123` | `import_graph` reads `head_text`, which is `git show HEAD:<path>` |

**The third condition is a trap and no report has named it.** A file that is
added to the index but not committed passes `:419`, because `git ls-files`
lists it. It then gives NO import edges, because `head_text` returns the empty
string, and `count` returns 0 at `scripts/ledger.py:135`. The report would
print a GCH closure of one master and zero lines, and exit 0. **INFERRED that a
reader would take that for a measurement**, because nothing marks it.

**Nothing gates on `[reuse]`.** MEASURED: `--check` builds `defects` at
`scripts/ledger.py:777-783` and `reuse_report` never adds to it. So an early
declaration cannot break `make check`. It can only make the report print one
line instead of five.

### 1.3 The day, and the price

**The day is A7's landing day, Wave 2 of the order at
`agents/tasks/LJ-1-268/lj-1.268-report.md:23-38`.**

A7 lands `src/L/GCH.lagda.md`, 33 lines, MEASURED at
`agents/tasks/LJ-1-253/lj-1.253-report.md:21`. Its prerequisites are A2 and
A4, MEASURED at `agents/tasks/LJ-1-268/lj-1.268-report.md:173-176`: A7 imports
A2's `injAt` and A4's `InjCode` and `IsCardinalL`, and it does NOT import A5 or
A6.

| block | lines | evidence |
|---|---:|---|
| A2, `src/L/Coding/Injection.lagda.md` | 186 | `lj-1.253-report.md:21`, `lj-1.268-report.md:60` |
| A4, into `src/L/Cardinal.lagda.md` | 43 | `lj-1.253-report.md:21`, `lj-1.268-report.md:114-133` |
| A7, `src/L/GCH.lagda.md` | 33 | `lj-1.253-report.md:21`, `lj-1.268-report.md:167-179` |
| **minimum** | **262** | |
| A1, which CREATES `src/L/Cardinal.lagda.md` | 54 | `lj-1.268-report.md:84-99` |
| **as the landing order lands it** | **316** | |

**262 to 316 lines, against the target's 1,760.** The low figure assumes A4
opens `Cardinal.lagda.md` alone. The high figure follows the landing order,
where A1 is Wave 0 and creates the master. **A1 and A2 have NO undelivered
imports, MEASURED at `lj-1.268-report.md:72-83` and `:91-99`.** So Wave 0 is
landable today, and `dev/PLAN.md:96` says the same.

**INFERRED: this is 15 to 18 percent of 1,760.** DD4's report starts working at
about one sixth of the distance the target gave.

### 1.4 What the figure would MEAN, and it UNDERSTATES

**I computed it. The block below is what `ledger.py --reuse` would print on
A7's landing day.**

Method. I loaded `scripts/ledger.py` as a module. I took its own `import_graph`
over the tree at HEAD. I added three nodes for the three new masters, with the
import lists MEASURED at `lj-1.268-report.md:72-83`, `:91-99`, `:106-112`,
`:119-126` and `:173-176`. I then called its own `closure`. No Agda ran.
MEASURED: every import name in those lists resolves to a tracked master, and
the unresolved list is empty.

```
AC closure      73 masters  17,197 lines
GCH closure     48 masters   8,731 lines
SHARED          43 masters   7,596 lines
shared share of the union: 41.4% of 18,332 lines
GCH-only: L/Cardinal, L/Coding/Injection, L/GCH, L/Ordinal/SquareLaw,
          V/Presentation
```

The AC row is not a simulation. **MEASURED today: the AC closure is 73 masters
and 17,197 lines**, computed by the same code from the declared `ac_root`.

**The figure UNDERSTATES sharing, and the cause is one thing.** A hypothesis
carries no import edge. A7 writes `SqShape` and `AbsorbsShape` as hypotheses,
MEASURED at `lj-1.268-report.md:174-176` and at
`agents/tasks/LJ-1-236/ProbeLJ1236A7.agda:113-128`. So A5's
`src/L/InjChain.lagda.md` and A6's `src/L/Absorption.lagda.md` stay out of the
GCH closure that day.

**By how much, and the answer is small for SHARED.** A6 imports A2 only
(`lj-1.268-report.md:159-161`). A5 imports A2 and the delivered
`L.Ordinal.SquareLaw` (`lj-1.268-report.md:143-148`). Both are already inside
the day-one closure. **INFERRED: SHARED moves little when A5 and A6 land. The
GCH TOTAL grows by their own 348 and 399 lines.** So the understatement sits in
the GCH total, not in the intersection.

**The honest reading, and it must be written beside the figure.** The number
answers "what does the GCH STATEMENT reach", not "what will the GCH PROOF
reach". That is a real measurement of a real object. **A reader must not act on
it as the endpoint figure.** Write that sentence into `gch_root_why` on the day
of declaration, and the declaration is honest.

### 1.5 The conditional-statement finding, which the target half-saw

**C-45 CHECK: the target used `exit 0` correctly.** MEASURED at
`agents/tasks/LJ-1-236/ProbeLJ1236A7.agda:165-171`: module `Guard` builds `hω`
and `aω` only. It supplies neither `sq` nor `absorbs`. The target's section 1
is right.

**The target missed the deeper shape, and C-43 names it.** `sq` and `absorbs`
are parameters OF THE STATEMENT TYPE, at `ProbeLJ1236A7.agda:147-157`. So a
term of type `GCHStatement L⊨ZF` is a CONDITIONAL theorem: it proves GCH GIVEN
`SqShape` and `AbsorbsShape`. The probe's own comment says so at `:133-134`.

**Consequence. A term of type `GCHStatement L⊨ZF` is not the trophy.** The
trophy also needs inhabitants of `SqShape` and `AbsorbsShape`, which A5 and A6
supply. The target's chain does fund A5 and A6, so its TOTAL is not affected.
But its section 1 states the endpoint type without saying the type is
conditional, and a reader would take `GCHStatement L⊨ZF` for the trophy.

**Compare `ac_root`, which is the template the brief named.** MEASURED at
`src/L/Model.lagda.md:98-99`: `L⊨ZFC : isZFCModel` takes no hypothesis. Its
only assumption is the module parameter `lem` at `src/L/Model.lagda.md:45`.
**That is a different KIND of assumption**: `lem` is classical logic, while
`SqShape` and `AbsorbsShape` are the mathematics A5 and A6 must prove. So the
two sides are not yet the same kind of object, and the brief's premise that
they must be is what section 3 attacks.

## 2. THE THREE PARTS RE-DERIVED

### 2.1 The arithmetic, and it is a MEASURED defect

The target's table is `agents/tasks/LJ-1-273/lj-1.273-report.md:100-106`.

| part | figure | width | what I found |
|---|---|---:|---|
| 1, A-prime | 1,089 | 0 | RE-DERIVED. Holds, with a caveat |
| 2, `[LJ-1.7]` residue | 450 to 550 | 100 | RE-DERIVED from its two cited lines. The basis is stale |
| 3, final assembly | 120 to 320 | 200 | RE-DERIVED. The basis is the RETIRED route |

**Part 1 RE-DERIVED. MEASURED.** `54 + 186 + 26 + 43 + 348 + 399 + 33 = 1,089`
at `agents/tasks/LJ-1-253/lj-1.253-report.md:21`. The sum is correct.
**The caveat, MEASURED at `lj-1.268-report.md:130-133`: A4's 43 lines become
"about 32 in a master, after dropping the 11-line probe-only `Atω` guard".**
So at least one block lands smaller than its probe count. **INFERRED in the
other direction: five NEW masters each add an OPTIONS header, a module line and
an import block, and those lines are inside the fence and therefore counted.**
The two corrections point opposite ways and no report has netted them.
**Part 1 carries NO band, and a probe sum that is known to differ from the
landed lines at one block should carry one.**

**Part 2 RE-DERIVED. MEASURED.** `dev/PLAN.md:47` gives "about 400", built as
255 for the 28 fields plus a 147-line delivered comparable. `dev/PLAN.md:74`
and `:84-85` move the 255 to "about 255 plus about 50", so 305. Then
`305 + 147 = 452`, which rounds to the target's 450. **The re-derivation is
correct.** Section 2.3 attacks the basis.

**Part 3 RE-DERIVED. MEASURED.** `agents/tasks/archive/LJ-1-1/lj-1.1-recon.md:171`
reads "Size: 150-350 naive. Basis: survey". Subtracting A7's 33 gives 117 to
317, which rounds to the target's 120 to 320. **The subtraction is correct
arithmetic and the target marks it INFERRED, correctly.**

**THE DEFECT, MEASURED by arithmetic.** The point 1,760 is
`1089 + 450 + 220`, as the target states at `:106`. It takes the **LOW end**
of part 2 and the **MIDDLE** of part 3. Two rules in one sum.

- Band centre: `(1660 + 1960) / 2 = 1810`.
- Consistent midpoint sum: `1089 + 500 + 220 = 1809`.
- The target's point: 1,759, written as about 1,760.

**The gap is 50 lines and it is exactly the width the target gave its own
unpriced tail.** The target says at `:109-111` that the tail holds "14 site
facts, `SF`, and the `ω ∈ σ` term" and that "that tail makes the band". **So
the point estimate prices the unpriced tail at ZERO.** DD8 asks for ONE
best-effort number. A number that assumes the unmeasured term is free is not
best-effort. **MEASURED.**

### 2.2 The INFERRED split, and the brief's fear is confirmed

**The brief asked whether a band whose widest term is INFERRED is a survey
wearing a probe's clothes. MEASURED: it is.**

| part | basis the target gave | band width | share of the 300 |
|---|---|---:|---:|
| 1, A-prime | probe | 0 | 0 percent |
| 2, residue | comparable plus survey, INFERRED | 100 | 33 percent |
| 3, final assembly | survey, INFERRED | 200 | 67 percent |

**The one part with a probe basis contributes ZERO of the 300 lines of band
width. One hundred percent of the uncertainty is INFERRED.**

**The widest unmeasured term is part 3, and the target did not name it as
such.** DD8 says to measure the widest unmeasured term. Part 3 is 200 lines of
width, its only source is the RETIRED route's survey, and no probe has ever
run at that site. **The target did not name a probe that would measure it.**

**A second defect in part 3, and the target contradicts itself.** Its section 3
rules that the archive's `CardinalPredicates` "does not transfer", because the
archive uses the bijection form and the current route uses the injection form
(`lj-1.273-report.md:85-92`). **It then takes the archive's PRICE for the block
that consumes those very predicates.** `lj-1.1-recon.md:169` lists Block 6's
dependencies as "Block 5, L.Model, FOL.ZFModel, the certified predicates". So
the target rejects the archived code and keeps the archived price of assembling
it. **INFERRED that the price does not transfer either**, by the same argument
the target itself made. `dev/LESSONS.md` P-l closes with "A CURE DOES NOT
TRANSFER BY ANALOGY. Re-measure it at every new site."

**A third point on part 3, and it cuts the other way.** The archived figure is
"naive". The same recon prices its neighbour Block 5 at "480-1,020 naive.
Basis: survey, class x3" (`lj-1.1-recon.md:161`). So the retired route carried
a class multiplier for survey rows and Block 6 declares none.
**INFERRED: taking a bare naive survey band from a route that multiplied its
survey rows takes the optimistic caliber.**

### 2.3 Part 2's basis is STALE, and this is the strongest finding after section 1

**MEASURED: the target's part 2 rests on `dev/PLAN.md:47` and `:74` only. The
same file's task index records SIX later dispatches on the same block, and the
target cites none of them.**

| row | `dev/PLAN.md` line | what it measured |
|---|---|---|
| `[LJ-1.257]` | `:888` | 5 of 5 built. The five `envK-*` collapse to 67 against 85. Bodies fall 55 to 30 |
| `[LJ-1.260]` | `:889` | **LANDED. Four masters green, net +42** |
| `[LJ-1.258]` | `:890` | 12 of 15 built. Rates are 2, 1 and 1 body lines per field |
| `[LJ-1.259]` | `:891` | The env closure builds. Three `consK` close |
| `[LJ-1.261]` | `:892` | The merge builds at 148 lines. `finSetK` is SUPPLIED |
| `[LJ-1.263]` | `:894` | Three L-rows landed. The master is green |

**Three consequences, each separate.**

**(a) Part of the residue has ALREADY LANDED, so it is not remaining.**
MEASURED at `agents/tasks/LJ-1-260/lj-1.260-report.md:11-18`: 60 insertions and
18 deletions, net +42, across four masters, all green. **Those 42 lines are in
standing today.** A remaining-work figure that does not subtract them counts
them twice. **The target never asked whether any of the residue had landed.**

**(b) The 305 was never re-derived from the measurements under it.** The 305 is
`255 + 50`, and the 255 is an entry projection at 9.1 lines per field
(`agents/tasks/LJ-1-255/lj-1.255-report.md:104`). `[LJ-1.258]` then MEASURED 1
to 2 body lines per field over 12 fields
(`agents/tasks/LJ-1-258/lj-1.258-report.md:14-22`), and `dev/PLAN.md:890` calls
that "Far UNDER 9.1". **Nobody has summed the measured parts.**

**A WARNING ON MY OWN CITATIONS. `dev/PLAN.md` CHANGED WHILE I READ IT.**
MEASURED: my first read put the `[LJ-1.7]` status paragraph at `:56` and the
task index rows in the 860s. My second read, the same session, put them at
`:74` and in the 880s. About 18 lines went in between. **Every `dev/PLAN.md`
line in this report is from my LAST read. Re-grep the quoted words, not the
numbers.**

**(c) I summed what is on the record, and the direction of the error is UP.**

| source | in-fence lines | evidence |
|---|---:|---|
| `[LJ-1.254]`, `envSetK`, `sucK` and the join | 141 | `lj-1.254-report.md:13` |
| the five `envK-*` after the collapse, plus setup | 105 | `lj-1.257-report.md:13`; setup 38 at `lj-1.255-report.md:109-111` |
| `[LJ-1.258]`'s 12 fields, shared proofs plus bodies | 54 | `lj-1.258-report.md:17-22` |
| `[LJ-1.261]`'s finite-supremum merge | 148 | `lj-1.261-report.md:17` |
| **partial sum** | **448** | |
| less the lines already landed | -42 | `lj-1.260-report.md:11-18` |
| **partial remaining** | **406** | |

**INFERRED, and I mark the reason.** Probe lines are not master lines, this sum
omits the four `envInK-*` and `someEnv` bodies that `[LJ-1.257]` built, and
some probe scaffolding never lands. **But 406 against the 305 the target used
is 33 percent above it. If step 6 costs 406, part 2 becomes about 553, which is
ABOVE the target's own band top of 550.**

**The target is not at fault for the staleness of `dev/PLAN.md:74-90`.** That
paragraph is dated 2026-08-15, names `[LJ-1.252]` to `[LJ-1.256]`, and does not
name the six later rows. **The paragraph is behind its own index.** The target
quoted the live status screen, which is what a careful agent does. **C-44 is
still the law: a figure in a paragraph is unchecked until you check it against
the rows under it.** `AGENTS.md` says the same about standing figures.

## 3. DID THE BRIEF CAUSE IT? YES

**MEASURED. The brief caused the answer, and the mechanism is not a plain false
dichotomy.**

**The brief was not a strict binary.** `agents/tasks/LJ-1-273/LJ-1.273.md:75-77`
carries a third branch: "THE ENDPOINT NEEDS SOMETHING NOBODY HAS NAMED." So the
escape existed. **The damage is elsewhere and it is worse.**

**Cause 1. The brief welded a TRUE operational answer to a FALSE mathematical
premise.** `LJ-1.273.md:34-40` states the two branches:

- "If A7 IS the endpoint, then A-prime's landing declares `gch_root`... the
  wait is short."
- "If `[LJ-1.8]` is the endpoint and A7 is only its STATEMENT, then... the wait
  is the whole remaining phase."

**The FIRST half of branch one is TRUE and the SECOND half is FALSE.** A7's
landing DOES let `gch_root` be declared, MEASURED in section 1. A7 is NOT the
endpoint, also MEASURED. **The brief made those one proposition.** The agent
correctly rejected the false half, and the true half went with it.

**Cause 2. The brief told the agent to derive the requirement from a
COMPARABLE, not from the CODE.** `LJ-1.273.md:53-57` says "the GCH side must be
the same KIND of object" and instructs "Read `Model.lagda.md:99` and say what
shape an endpoint is." **The brief cites `scripts/ledger.py:404-407` and `:50`
at `:14-16`, but only for the AXIS.** It never asks what the closure is
computed FROM. **So the one question that decides the answer was never put.**
The agent read `Model.lagda.md:99`, found a proof term, and required a proof
term. **That is P-l's own failure applied to a requirement instead of a cure.**

**Cause 3, and it is the proof of causation.** The brief's own words at
`LJ-1.273.md:39-40` are "the wait is the whole remaining phase". The task index
row the orchestrator wrote for the return, at `dev/PLAN.md:903`, reads "The
wait is the rest of the phase, not the next landing". **MEASURED: the
conclusion is the brief's own sentence returned.**

**What a corrected brief would have asked.** One sentence: "Read
`scripts/ledger.py:404-446` and say what the tool reads at `gch_root`, before
you say what `gch_root` must name." **`[LJ-1.274]`'s own brief DID ask that, at
`agents/tasks/LJ-1-274/LJ-1.274.md:55-60`, and that is why this answer exists.**

## 4. DD4 FIGURES, COMPUTED

**The brief's C-46 instruction: run what can be run. I ran it. No Agda.**

**AXIS, named as C-46 requires: the AC-against-GCH axis, DD4's own.**
`[LJ-1.272]` fixed that at `agents/tasks/LJ-1-272/lj-1.272-report.md:233-235`,
from `scripts/ledger.py:50` and `:404-407`.

### 4.1 What is measurable today

| figure | value | state |
|---|---:|---|
| AC closure from `ac_root` | 73 masters, 17,197 lines | MEASURED today |
| GCH closure from `gch_root` | not computable | `gch_root = ""` at `dev/ledger.toml:177` |
| standing | 30,111 lines over 88 masters | MEASURED, `ledger.py --brief` |

### 4.2 The finding `[LJ-1.272]` did not report

**`--trophy-split` prints a shared figure today, and one fifth of it is not a
measured intersection.** MEASURED.

**I first wrote that the whole figure was an artefact. I then computed it and
that was FALSE. The corrected numbers are below, and I record the correction
because a review that hides its own miss is worth less.**

`ledger.py --trophy-split` prints "shared 18,966". I computed its parts with
the tool's own `trophy_split`.

| part of the 18,966 | lines | share |
|---|---:|---:|
| real intersection of the two closures | 15,152 | 79.9 percent |
| the PARKING RULE, 7 masters in NEITHER closure | 3,814 | 20.1 percent |

The parking rule is `scripts/ledger.py:591-596`. Its own comment says an L
master in neither closure lands in the shared part. The seven are
`L/BoundedSubset`, `L/Coding/Key`, `L/Coding/KeyRead`,
`L/Condensation/LowerAgree`, `L/Condensation/TwelveAgree`,
`L/Condensation/UpperAgree` and `L/StageCardinal`.

**MEASURED: of the 13 GCH-side roots declared in `[[trophy_split]]`, only THREE
exist in the tree**: `src/L/Condensation.lagda.md`, `src/L/Hull.lagda.md` and
`src/L/Ordinal/SquareLaw.lagda.md`. The other ten are absent. No defect fires,
because `trophy_split_suspended` is true at `scripts/ledger.py:479`.

**Consequence for the plan, and it is smaller than I first thought.** A DD4
number does exist today on the trophy-split line, and 79.9 percent of it is a
real closure intersection. **But its GCH side rests on three surviving roots
out of thirteen declared, so it measures a wing that is one quarter declared.**
**INFERRED that this is the class `[LJ-1.272]` swept for**: a figure whose
basis is narrower than its name.

### 4.3 The figure the project gets on A7's landing day

Repeated from section 1.4, because this is the DD4 answer.

```
AC closure      73 masters  17,197 lines
GCH closure     48 masters   8,731 lines
SHARED          43 masters   7,596 lines
shared share of the union: 41.4% of 18,332 lines
```

**INFERRED, because it depends on the import lists MEASURED in
`[LJ-1.268]` rather than on landed masters.** The AC row is MEASURED.

**What the tool still cannot tell the project, on any day.** It counts MASTERS
in a closure. It cannot see a hypothesis, a generic carrier instantiated twice,
or a proof written once and applied at two towers. **So DD4's real subject,
which is written-once code, is invisible to `--reuse` by construction.** The
report measures IMPORT sharing, not CODE sharing. **That limit is not stated in
`scripts/ledger.py:404-446` and it should be.**

## 5. THE VERDICT, ITEM BY ITEM

| the target's claim | verdict | basis |
|---|---|---|
| A7 is only the statement, not the trophy | **HOLDS** | MEASURED, `ProbeLJ1236A7.agda:147-171` |
| `gch_root` must name a proof term | **WRONG** | MEASURED, `scripts/ledger.py:404-446` |
| Part 1 is 1,089 | **HOLDS**, no band | MEASURED, `lj-1.253-report.md:21` |
| Part 2 is 450 to 550 | **RE-DERIVED, basis STALE** | MEASURED, `dev/PLAN.md:887-894` |
| Part 3 is 120 to 320 | **RE-DERIVED, basis RETIRED** | MEASURED, `lj-1.1-recon.md:171` |
| The point is about 1,760 | **WRONG**, its own centre is 1,810 | MEASURED, arithmetic |
| The chain is the distance to `gch_root` | **WRONG**, that is 262 to 316 | MEASURED |
| DD4 stays INFERRED until the chain lands | **WRONG**, computable now | MEASURED, section 4 |

**What I could NOT check.** I did not re-price Route A-prime, by the brief's
instruction. I did not run Agda, so no line count here is a typecheck. I could
not close part 3, because no probe has ever run at the final assembly site, and
naming that probe is the next dispatch, not this one.

## 6. ARCHIVE USED (DD18)

One line read named per file.

- `agents/tasks/LJ-1-273/lj-1.273-report.md:100-106`, the three-part table and
  the point sum. The target, read whole.
- `agents/tasks/LJ-1-272/lj-1.272-report.md:233-235`, "DD4's own text names the
  two trophy proofs, not the two towers".
- `agents/tasks/LJ-1-268/lj-1.268-report.md:173-176`, A7 does not import A5 or
  A6, so `SqShape` and `AbsorbsShape` are hypotheses.
- `agents/tasks/LJ-1-267/lj-1.267-report.md:30-32`, the seven parameters build
  `levelIn` and `cover` at `src/L/BoundedSubset.lagda.md:1555-1556`. **The
  target cites the PROBE at `:500-505` for the same fact; both citations are
  true and the master one is the site.**
- `agents/tasks/LJ-1-253/lj-1.253-report.md:21`, the seven-block sum.
- `agents/tasks/LJ-1-236/ProbeLJ1236A7.agda:147`, `GCHStatement` is a type over
  `isZFModel`.
- `agents/tasks/archive/LJ-1-1/lj-1.1-recon.md:171`, "Size: 150-350 naive.
  Basis: survey".
- `archive/dev/TASKS-archived.md:72`, `L3.32-T37` cardinal predicates, built
  generally, DELIVERED. **Shape only. CHECKED: the target's citation is
  correct.**
- `archive/dev/STATUS-archived.md:116`, `L4.3` closed and absorbed, the GCH
  endpoint is the active campaign. **CHECKED: the target's citation is
  correct.**
- `archive/dev/DECISIONS-archived.md:58`, D39 states "MAXIMIZE THE CODE THE TWO
  PROOFS SHARE" as the route's governing principle. **Read for DD4's axis.**

**WHY NOT.** I did not read `archive/dev/JOURNAL-archived.md`. The two questions
I attacked are settled by the live code and by live reports, and the retired
route's reasons cannot move what `scripts/ledger.py` reads today.

## 7. LITERATURE USED (DD18)

`dev/literature/devlin-II5.md:370-383`, the twelve-row table, read whole. **The
target mapped SEVEN rows at `lj-1.273-report.md:167-175`. I checked all seven
and the five it dropped.**

| row | the target's status | my check |
|---|---|---|
| B, collapse (`:373`) | SUPPLIED by `fwd`, `bwd` | **CORRECT.** MEASURED at `lj-1.267-report.md:53-70`: the collapse iso is delivered at `src/L/BoundedSubset.lagda.md:195-318` and wired at `:780` |
| C1, level-hood (`:374`) | OPEN in the residue | **CORRECT.** MEASURED, `lj-1.267-report.md:16-19` |
| C4, transfer (`:377`) | SUPPLIED by `el` | **CORRECT.** MEASURED at `lj-1.267-report.md:34-51`: `elem` at `src/L/BoundedSubset.lagda.md:759-760` |
| D, well-order (`:380`) | delivered by the `L.Choice` stack | **PLAUSIBLE, INFERRED.** The target gives no `file:line` and neither can I without a search this brief did not fund |
| E, counting (`:381`) | delivered comparable in `SquareLaw` and `StageCardinal` | **MIS-ASSIGNED.** Devlin puts `|L_α| = |α|` in row F at `:382`, not in E |
| F, condensation (`:382`) | partly `[LJ-1.7]`, partly A5 and A6 | **MIS-ASSIGNED.** A5 is the square law and A6 is absorption. Both are cardinal arithmetic, which is Devlin's E, not F |
| G, uniform well-order (`:383`) | delivered by the same stack | **PLAUSIBLE, INFERRED.** Same gap as D |

**Finding 1, MEASURED. Rows E and F are swapped.** The target put
`L.StageCardinal`, which is the `|L_α| = |α|` module, under E, and put A5 and
A6, which are cardinal arithmetic, under F. **The mapping is INFERRED in the
target's own words and the swap does not change any price.** It would change a
reader's view of which delivered module answers which obligation.

**Finding 2, MEASURED. The target dropped five rows and gave no WHY NOT.** Rows
A (`:372`), C2 (`:375`), C3 (`:376`), C5 (`:378`) and C6 (`:379`) are absent
from its table. **C2 is PER-TOWER content by Devlin's own column**, so it is
not obviously free. **DD18 requires a WHY NOT for anything not used.** The
target's section 7 has none.

**Finding 3, MEASURED. "Delivered comparable" is not "delivered".** The target
writes "delivered comparable" in row E and then concludes at `:176` that "No
needed row has no delivered counterpart". A comparable prices work. It supplies
nothing. **C-38 as extended: a hypothesis is discharged when something SUPPLIES
it.** `src/L/Ordinal/SquareLaw.lagda.md` and `src/L/StageCardinal.lagda.md` do
exist as tracked masters, MEASURED by `git ls-files`, so the conclusion
survives. **The word is still wrong and it hides the distinction the whole
report turns on.**

`dev/literature/devlin-II5.md:385-390`, the DD4 verdict paragraph, read for the
axis. It names the per-tower content as exactly two objects, the level-hood
certificate and the definable well-order. **WHY IT MATTERS HERE: that is
Devlin's Def-against-J axis, not DD4's AC-against-GCH axis.** `[LJ-1.272]`
separated them at `:250-258` and the target repeated the separation correctly
at `lj-1.273-report.md:134-138`.

## 8. WHAT I RECOMMEND, in one paragraph

**Declare `gch_root = "src/L/GCH.lagda.md"` on the day A7 lands, and write the
limit into `gch_root_why`.** The condition is section 1.2's three tests, and
the third one, COMMITTED and not merely staged, is the one that will be missed.
The price is 262 to 316 lines, not 1,760. **Then re-price part 2 from the six
dispatch rows at `dev/PLAN.md:887-894`, because its current basis is a
paragraph that its own index has overtaken.** **Then gate part 3**, which is
200 of the band's 300 lines, carries only the retired route's survey, and has
never had a probe.

## 9. WORKING TREE

One file written, inside `agents/tasks/LJ-1-274/`:
`lj-1.274-report.md`. Scratch scripts were written to the session scratchpad,
outside the repository. No master edited. No brief or report edited. No
`dev/ledger.toml` edit. No `src/Everything.lagda.md` edit. No Agda ran. No
commit, no push, no reset, stash, checkout or clean.
