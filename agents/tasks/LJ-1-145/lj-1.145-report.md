# LJ-1.145 report: where the Condensation family's seconds are

**Status: COMPLETE.** DIAGNOSIS ONLY. **No master was edited, nothing was
committed, nothing was pushed.** Four probes were written, all under
`agents/tasks/LJ-1-145/`, all GREEN.

## 0. THE ANSWER, in four lines

1. **The term is ONE CONVERSION, and it is measured.** Taking a component out
   of a pattern split of `⟨ γ ⊨ DefBody w ⟩` and naming its folded type costs
   **2,526 ms**. Splitting and rebuilding the same type costs **12 ms**.
   Applying the supplier to a variable of its own stated type costs **15 ms**.
2. **Both of the brief's leads are REFUTED, by measurement.** The record field
   P-x names is not in the master; the module application P-w names costs
   10 ms and removing it costs MORE.
3. **The cure is one `opaque` on shared upstream machinery, and it is
   measured at the real site: 2,459 ms to below 1 ms.**
4. **It does not close the gap.** 21 s of 55.3 s, so the wing still misses
   DD24's bar. **The remainder is not a craft question I can find a lever
   for.**

## 0.1 Machine load, beside every figure

| when | load 1m / 5m / 15m | note |
|---|---|---|
| dispatch | 4.89 / 5.01 / 5.01 | brief's figure |
| start | 3.95 / 4.59 / 4.84 | measured by me |
| before run 1 (`check-ratio`) | 3.23 / 4.09 / 4.55 | 122.64 s result |
| before run 2 (`--profile=definitions`) | 3.10 / 3.95 / 4.48 | 121.19 s result |
| after run 2 | 3.39 / 3.76 / 4.34 | |

**I ran ONE agda process at a time throughout, at `GHCRTS="-A64m -I0 -M8g"`,
and never raised the cap. NO HEAP WALL was reached.** Verified by
`ps -eo pid,ppid,etime,%cpu,rss` at 18:38: PID 63363 was the only `agda`
binary; the other matches were the repository watchdog and my own wrapper.
**A sibling's agda appeared later and section 6 records where.**

## 1. WHERE THE SECONDS ARE

**MEASURED. `agda --profile=definitions`, cold (interface moved aside),
`GHCRTS="-A64m -I0 -M8g"`, exit 0, total 121,193 ms.**

| bucket | ms | share |
|---|---:|---:|
| **`Miscellaneous`** | **59,590** | **49.2 percent** |
| 321 named definitions | 61,439 | 50.7 percent |
| largest single definition, `LeafAgree.out` | 9,267 | 7.6 percent |

**The dominant term is `Miscellaneous`, and it is not a definition.** It is
the half of the check that Agda attributes to no name.

**The named half is one shape.** 56.2 percent of the 61,439 ms of named
definition time sits in definitions called `out` or `back`: **34,539 ms, 28.5
percent of the whole check.** These are the two-way agreement transfers. Their
bodies are three to five lines each. `LeafAgree.out`
(`src/L/Condensation.lagda.md:7014`) is **9,267 ms for a four-line body**.

| module | ms | share of total |
|---|---:|---:|
| `LeafAgree` | 13,630 | 11.2 percent |
| `SatGraphAgree` | 7,927 | 6.5 percent |
| `PropAgree` | 4,362 | 3.6 percent |
| `ExInAgree` | 3,110 | 2.6 percent |
| `KFactsNS.KFacts` + `KFactsCons` | 833 | **0.7 percent** |

### 1.1 The phase breakdown. MEASURED

**Second run, `agda --profile=internal`, cold, same caliber, exit 0, total
122,520 ms**, load 3.52 before and 5.59 after.

| phase | ms | share |
|---|---:|---:|
| **`Typing`** (all sub-phases) | **83,604** | **68.2 percent** |
| `Typing.CheckRHS` | 37,293 | 30.4 percent |
| **`Typing.CheckLHS`** | **28,912** | **23.6 percent** |
| `Typing.OccursCheck` | 11,242 | 9.2 percent |
| `Typing.TypeSig` | 4,998 | 4.1 percent |
| `InterfaceInstantiateFull` | 11,582 | 9.5 percent |
| `Serialization` | 10,388 | 8.5 percent |
| `DeadCode` | 5,279 | 4.3 percent |
| `Positivity` | 4,766 | 3.9 percent |
| `Parsing` | 2,472 | 2.0 percent |
| `Coverage` | 1,619 | 1.3 percent |
| `Deserialization` | 1,535 | 1.3 percent |

### 1.2 What `Miscellaneous` is. INFERRED by arithmetic across the two runs

The two runs differ by 1.1 percent, so this composition is approximate.

- `Typing` totals 83,604 ms. The named definitions total 61,439 ms.
  **About 22,000 ms of type-checking happens OUTSIDE every definition.** That
  is module telescopes and module-application instantiation.
- `InterfaceInstantiateFull` + `Serialization` + `DeadCode` = **27,249 ms, 22
  percent**. This is interface PRODUCTION, not mathematics. The interface file
  is 5,374,019 bytes.
- `Positivity` + `Parsing` + `Coverage` + `Deserialization` + `Scoping` =
  about 10,900 ms.

22,000 + 27,249 + 10,900 = 60,149 ms, against the 59,590 ms `Miscellaneous`
of run 1. **The two accounts agree to within 1 percent.**

## 2. P-x, the record-field lead: REFUTED. MEASURED

**The lead does not hold at this master, and there are three independent
reasons.**

### 2.1 The field that walled the master is NOT IN THE MASTER. MEASURED

`[LJ-1.109]` measured the wall on a field it ADDED and then removed. Its own
report says so: `agents/tasks/LJ-1-109/lj-1.109-report.md:84-86`, "Removing
exactly the two lines (field + `KFactsCons` line) returns the master to GREEN
at 154-155 s." The commit's title, "a record field walls the master", records
a route that was refused, not a defect that landed.

**I read the live field list.** `src/L/Condensation.lagda.md:5940-5975`, the
`KFacts` record, has 27 fields: `tagEq0` to `tagEq11`, `numK0` to `numK11`,
`innerK`, `innerPairK`, `pairK`, `carrierK`, `arityK`. **There is no `sucK`
and no other field naming `sucV`.** `grep -c "sucK" src/L/Condensation.lagda.md`
returns 0.

### 2.2 The record that IS there costs 0.7 percent. MEASURED

From run 1: `L.Condensation.KFactsNS.KFacts` **553 ms** and
`L.Condensation.KFactsCons` **280 ms**. **833 ms of 121,193 ms.** Eight
telescopes in the master take a `KFacts` parameter
(`src/L/Condensation.lagda.md:6024`, `:6307`, `:6406`, `:6432`, `:6685`,
`:6726`, `:6913`, and `KFactsCons` at `:5983`).

### 2.3 The live field types name a SEALED atom, so there is nothing to seal. MEASURED

P-x asks what the field type constructs transparently. The answer is: almost
nothing.

- 24 of the 27 fields name `numeralL k` for `k` a literal 0 to 11.
  **`numeralL` is `opaque`.** `src/L/Axioms/Numerals.lagda.md:97` opens an
  `opaque` block at column 0; the block's members are indented two spaces and
  the indentation runs unbroken across the literate fences through
  `numeralL` at `:175` and `numeralL-fst` at `:181`. The block ends at
  `numeralL-zero`, `:203`, which is at column 0. So `fst (numeralL 11)` is a
  stuck term, not an eleven-deep `sucV` chain.
- The master's own Chinese prose at `src/L/Axioms/Numerals.lagda.md:90`
  records why: unsealed, the coding chapter's instantiation did not finish in
  ten minutes; sealed, it costs about a third of a second.
- The remaining field types name `prʟ` (`src/L/Coding/Model.lagda.md:326`),
  which is transparent but unfolds ONE step into three applications of the
  sealed `pairʟ`. The unfolding is bounded and does not grow.
- Every field's `lookup Nk γ` is stuck on a telescope variable.

**MEASURED NEGATIVE: the master holds no `opaque` block of its own**
(`grep -c opaque src/L/Condensation.lagda.md` returns 0), and the P-x cure
has no site here, because the record's transparent content is already
bounded.

### 2.4 The seal, measured on the master's LARGEST built formula. MEASURED

I did not seal a record field, because no field holds a transparent
construction to seal. **I sealed the largest formula the master builds
instead**, which is the same law aimed at the same class.

**`agents/tasks/LJ-1-145/ProbeLJ1145A.agda`, GREEN, exit 0.** It restates the
signature of `LeafAgree.out` (`src/L/Condensation.lagda.md:7014`), the
master's single most expensive definition at 9,267 ms, in six spellings at the
master's own generality, then reads them with `--profile=definitions`. Load
3.07 before, 5.20 after. **A sibling's agda (`[LJ-1.144]`, PID 68103) was live
during this run.** Whole file: **1,795 ms total, `real 2.62`.**

| spelling | ms |
|---|---:|
| `sigT`, transparent `DefBodyB` in the type, no pattern | **below 1** |
| `sigS`, the same formula behind an `opaque` alias | **below 1** |
| `sigM`, the machine-side `DefBody` in the type | **below 1** |
| `patM`, pattern split on `⟨ γ ⊨ DefBody w ⟩` | **below 1** |
| **`Cross`, the EXACT type of `LeafAgree.out`** | **below 1** |
| `patT`, pattern split on `⟨ γ ⊨ DefBodyB … ⟩` | **12** |
| `patU`, the same split behind the seal, `opaque unfolding` | **10** |

Agda prints every account with a non-zero millisecond; the five rows marked
"below 1" printed no row at all.

**THE SEAL LEVER IS REFUTED AT THIS SITE. MEASURED.** Stating the master's
biggest built formula in a type is free. Splitting it costs 12 ms. Sealing it
takes 12 ms to 10 ms, which is inside the noise of a 2.6 s run.

**And this settles where the 9,267 ms of `LeafAgree.out` is: its TYPE costs
under 1 ms, so the cost is its BODY.** The body is four lines
(`src/L/Condensation.lagda.md:7016-7019`) and every line is a projection out
of a module-application copy.

## 3. P-w, the module-application lead: REFUTED at this site. MEASURED

### 3.1 The census. MEASURED

**135 module applications in the master**, counted over the in-fence lines
only. By binding site, which is what P-w's amendment says decides the price:

| indent | count | what it is |
|---:|---:|---|
| 0 | 2 | file level (`AbsL`, `Cnt`) |
| 2 | 78 | inside a module, declaration level |
| 4 | 13 | nested |
| 6 | 6 | nested |
| **8 or 10** | **36** | **inside a definition body or a `where` clause** |

**80 of the 135 are one of two targets**: `EnvSet` 18 times and `RowTransfer`
12 times, and the rest are the `*Agree` family.

### 3.2 The controlled pair. MEASURED, and it refutes the lead

**`agents/tasks/LJ-1-145/ProbeLJ1145B.agda`, GREEN, exit 0.** It restates
`LeafAgree`'s telescope cut down to the nine hypotheses `SatGraphAgree` needs,
then uses `SatGraphAgree.out` twice, in the two spellings P-w separates. Whole
file 1,960 ms, `real 2.96`. Load 5.27 before, 5.65 after; a sibling's agda was
live.

| spelling | ms |
|---|---:|
| `useApp`, through `module SG = SatGraphAgree …` | **10** |
| `useFun`, the same definition applied directly, NO module application | **23** |
| `useTel`, a telescope hypothesis applied, the floor | 10 |

**MEASURED NEGATIVE: removing the module application does not help, and here
it cost more.** P-w's class (a), fewer applications, buys nothing at this
site. The application and the floor are the same 10 ms.

**And the same run refutes the lead a second way.** `SG.out h` is the middle
component of `LeafAgree.out`'s body. In the probe it costs **10 ms**. In the
master the whole four-line body costs **9,267 ms**.

### 3.3 The cost DOES transplant, so it is content and it is bisectable. MEASURED

**`agents/tasks/LJ-1-145/ProbeLJ1145C.agda`, GREEN, exit 0.** It copies
`src/L/Condensation.lagda.md:6911-7031`, the whole `LeafAgree` module,
verbatim, and imports its four suppliers from the master instead of writing
them again. Load 3.53 before, 3.78 after. Whole file **9,996 ms, `real
10.79`**.

| definition | probe C | the master | ratio |
|---|---:|---:|---:|
| `out` | **3,857 ms** | 9,267 ms | 0.42 |
| `back` | **3,621 ms** | 4,050 ms | 0.89 |
| `ic-out` | 38 ms | 154 ms | 0.25 |
| `ic-back` | 40 ms | 159 ms | 0.25 |

**This is the pivot of the whole diagnosis.** The seconds follow the content,
not the file. So there is a 10-second reproducer of the master's most
expensive definition, it is tracked beside this report, and the term can be
found inside it instead of by 2-minute master runs.

**The residual gap is the same-file effect, and it is INFERRED**: the probe
reads its four suppliers from a serialized interface, while the master builds
them in the live signature. That accounts for the 0.42 ratio on `out` and is
not measured here.

### 3.4 THE TERM, bisected inside the probe. MEASURED

Same probe, four more definitions, one run, `real 16.47`, load 7.81 before and
6.48 after. **The load was high and a sibling was running; every figure in
this table is from ONE run, so read the ORDERING, which is a factor of 200.**

| definition | ms | what it does |
|---|---:|---|
| `ctrl` | **12** | split `⟨ γ ⊨ DefBody w ⟩`, rebuild it unchanged |
| `sgOnStated` | **15** | `SG.out h` where `h` is a variable of the supplier's OWN stated type |
| `ic-out` | 39 | |
| `compDA` | 44 | split, then the third component's transfer |
| `compIC` | 490 | split, then the first component's transfer |
| `compSG` | 2,471 | split, then the middle component's transfer |
| **`midOf`** | **2,526** | **split, then coerce the middle component to its named type, and NOTHING ELSE** |
| `out` | 3,858 | all three together |
| `back` | 3,587 | the reverse |

**`midOf` costs as much as `compSG`.** The transfer adds nothing; **the whole
2.5 s is one COERCION.** It is 65 percent of `out`.

**The term, stated exactly:** splitting a satisfaction type is free; applying
a supplier to a variable of its own stated type is free; **taking a component
out of the split and naming its folded type is 2,526 ms.**

**The mechanism is INFERRED, not measured:** a pattern split reduces
`⟨ γ ⊨ φ ⟩`, so the component arrives with an UNFOLDED type, and the
consumer's signature names it FOLDED. The two heads differ, so the conversion
checker walks the whole formula tree instead of taking the syntactic short
cut that makes `ctrl` cost 12 ms.

## 4. THE CURE. MEASURED at one site, priced with its basis

### 4.1 What it is

**Seal the machine's built formula `satGraphAt` with `opaque` at its own
definition, `src/L/Coding/Graph.lagda.md:191-192`.** Then a component taken
out of a split arrives with a STUCK head, the consumer's signature names the
same stuck head, and the conversion is syntactic instead of a walk over the
formula tree.

This is P-t's own licence, applied one level upstream of where the seconds
are billed: "Seal a BUILT formula opaque wherever its consumers do not need
to see inside."

### 4.2 The measurement. MEASURED

**`agents/tasks/LJ-1-145/ProbeLJ1145D.agda`, GREEN, exit 0.** It rebuilds
`DefBody`'s exact shape twice, once with the machine's `satGraphAt` open, once
with it behind a seal, and coerces the middle component out of each. Whole
file 3,662 ms, `real 4.60`. Load 3.86 before, 4.19 after.

| definition | ms |
|---|---:|
| **`midOpen`, today's shape** | **2,459** |
| **`midSealed`, the same coercion behind the seal** | **below 1** |
| `ctrlOpen`, split and rebuild | below 1 |

**A factor of at least 2,459, and `bodyOpen` reproduces
`src/L/Coding/Powerset.lagda.md:437-440` line for line, so this is the real
site and not an analogy.**

### 4.3 The price in seconds. DD8: one figure, and here is its basis

**21 seconds off `src/L/Condensation.lagda.md`.**

The basis, built from measurements and stated so it can be attacked:

1. **MEASURED.** The `out`/`back` family in the master is **39,731 ms over 80
   definitions**, 32.8 percent of the check.
2. **MEASURED.** Four of those definitions are `SatGraphAgree`'s own
   (`out` 2,038, `back` 3,418, `body-out` 975, `body-back` 1,012 =
   **7,443 ms**). They are the side that must LOOK INSIDE the formula, so
   they carry `unfolding` and the seal saves nothing there. **Pass-through
   out/back is 32,288 ms.**
3. **MEASURED at one site.** In probe C the coercion is 2,526 ms of `out`'s
   3,858 ms, **65 percent**.
4. **INFERRED.** Applying that share to the 32,288 ms gives **21.0 s**.

**What the 21 s does NOT do.** The master goes from 122.64 s to about 101.6 s,
which is **0.01577 s/line, still over DD24's 0.0136 bar**. The wing goes from
210.77 s to about 189.8 s, **0.0166, still over**. **The cure is about 40
percent of the wing's 55.3 s gap and it does not close it.**

### 4.4 The price in lines

**About 25 in-fence lines added across 5 masters.** Basis: `satGraphAt` is
named in exactly five masters outside `src/Everything.lagda.md` —
`L/Coding/Graph` (4 uses), `L/Coding/Powerset` (5), `L/Condensation` (5),
`L/Choice/Internal` (8), `L/Choice/Adequate` (2), all MEASURED by `grep -rc`.
Each site that reads inside the formula needs an `opaque` line and an
`unfolding` line; the bodies are re-indented, which the ledger's in-fence
counter does not charge.

**This is a LINE-NEUTRAL seconds lever, which is what P-q says to look for.**
Nothing is deleted to improve a ratio.

### 4.5 The widest unmeasured term of the cure

**What the `unfolding` blocks cost.** Every definition that reads inside
`satGraphAt` must sit in `opaque unfolding satGraphAt`, and **nobody has
measured what an unfolding block costs at this scale.** The only figure I have
is probe A's `patU` at 10 ms against `patT` at 12 ms, which is one small site
and settles nothing about `SatGraphAgree.back` at 3,418 ms. **If an unfolding
block is dearer than the transparent form, it eats the saving from the other
end**, and 7,443 ms of the family sits in exactly those four definitions.

**Second unmeasured term:** the coercion share is measured at **1 of the 80**
out/back definitions. Step 4 of the basis above is the analogy P-l forbids as
a price, and I mark it INFERRED rather than pretend otherwise.

**How to close both cheaply:** seal `satGraphAt`, run `make check`, read the
master's `--profile=definitions` again. One edit, one cold run, and the whole
21 s becomes MEASURED. **That is a two-hour dispatch, not a block.**

### 4.6 What I did NOT find, and it matters

**MEASURED NEGATIVE: there is no single dominant definition.** The largest is
7.6 percent of the check, the top ten are 23.5 percent, the top fifty are 40.6
percent. **The dominant TERM is a mechanism, not a place**, and it is spread
across the out/back family.

**MEASURED: 22 percent of the check is interface production**
(`InterfaceInstantiateFull` 11,582 ms + `Serialization` 10,388 ms + `DeadCode`
5,279 ms = 27,249 ms). At 834 bytes of interface per in-fence line the master
is BELOW the tree's 1,229 average over 87 masters, so this is a floor the
whole repository pays, not a defect here. **No cure is proposed for it and I
do not think one exists.**

## 5. DD4: the cure is GENERIC, and it is upstream

**Maximize the code the two proofs share, and write it generic.**

**The cure is not local to this master. It is one `opaque` on shared
machinery.** `satGraphAt` lives in `src/L/Coding/Graph.lagda.md`, which the AC
wing already imports: `src/L/Choice/Internal.lagda.md` names it 8 times and
`src/L/Choice/Adequate.lagda.md` twice, both MEASURED. **So both trophies get
the seal from one edit, and neither pays for the other's copy.**

**The law behind it is generic too, and it is not in `dev/LESSONS.md` yet.**
P-t says a built formula unfolds. This measurement says something sharper and
it is new: **splitting a satisfaction type is free, and applying a supplier to
a variable of its own stated type is free; what costs is taking a component
OUT of a split and naming its folded type. 12 ms, 15 ms, and 2,526 ms, in one
run, on one formula.** If the orchestrator wants a law, that is the
measurement, and the action it prescribes is: **seal the machine formula, so
both sides of every such crossing stay folded.**

### 5.1 What this bears on `[LJ-1.144]`, which I did not touch

**I did not read or edit the three `*Agree` masters.** But the diagnosis bears
on the sibling's question and the brief asked me to say so.

The three masters check at 0.0819, 0.0731 and 0.0424 s/line, four to seven
times this master's rate, and what they DO is instantiate this master's
transfers. **The term I measured is a conversion between two spellings of a
satisfaction type, and an instantiation site is where that crossing happens
most.** So their rates may be an artifact of the same uncured mechanism.

**Do not decide whether those masters live on their current seconds until the
seal is measured.** That is a statement, not an action.

## 6. THE MACHINE, and whether the figures mean anything

**A sibling ran Agda for part of this dispatch.** I saw `[LJ-1.144]`'s
`ProbeLJ1144A.agda` as PID 68103 at 18:46 with `ps -eo pid,command`. I ran ONE
agda process at a time throughout, at `GHCRTS="-A64m -I0 -M8g"`, never raised
the cap, and hit **no heap wall**.

| run | load before | load after | result |
|---|---|---|---|
| `check-ratio --module` | 3.23 / 4.09 / 4.55 | — | 122.64 s |
| `--profile=definitions` | 3.10 / 3.95 / 4.48 | 3.39 / 3.76 / 4.34 | 121,193 ms |
| `--profile=internal` | 3.52 / 3.73 / 4.30 | 5.59 / 4.19 / 4.38 | 122,520 ms |
| probe A | 3.07 / 3.62 / 4.06 | 5.20 / 4.05 / 4.16 | 1,795 ms |
| probe B | 5.27 / 4.66 / 4.37 | 5.65 / 4.74 / 4.40 | 1,960 ms |
| probe C, bisect | 3.04 / 3.96 / 4.13 | 3.08 / 3.93 / 4.12 | 13,286 ms |
| probe C, isolation | 7.81 / 4.81 / 4.41 | 6.48 / 4.70 / 4.39 | 15,613 ms |
| probe D | 3.86 / 4.60 / 4.41 | 4.19 / 4.66 / 4.43 | 3,662 ms |

**The machine is noisy and I say so.** The two master runs differ by 1.1
percent, and `[LJ-1.135]` measured 6.9 percent drift on an identical tree
today. **So no figure here is a price to two significant figures.**

**It does not matter for this verdict, and here is why.** Every load-bearing
finding is a RATIO INSIDE ONE RUN, where the load is one number by
construction: 2,459 against below 1 in probe D; 2,526 against 12 and 15 in
probe C; below 1 against 9,267 in probe A against the master. **A factor of
2,459 does not turn on 6.9 percent of drift.**

## 7. LITERATURE (DD18)

**Nothing in the literature governs elaboration cost.** The term measured here
is a property of Agda 2.8.0's conversion checker, not of the mathematics.

## 8. ARCHIVE USED

- `agents/tasks/LJ-1-109/lj-1.109-report.md`, read WHOLE. **TOOK:** section 2
  at `:78-90`, the three wall configurations and the green pair, and the
  sentence at `:84-86` that the field was REMOVED. That is what refutes lead
  one. Section 6 at `:161-190` for the 151.2 to 155.2 s figures at the bare
  `-M8g` caliber, which is why I did not compare them to today's 122.64 s.
- `agents/tasks/LJ-1-136/lj-1.136-report.md`, read section 0 and section 1.
  **TOOK:** the report's method, one process at the cap and a wall reported as
  a wall. Its heap-wall figures did not transfer: I hit no wall.
- `dev/PLAN.md:513`, the `[LJ-1.57-A]` row. **TOOK:** the prediction "0.0220,
  1.73x over DD24's bar". Today measures 0.0190 at the same caliber. **The
  row's CLASS was right and its number was 16 percent high.** The row does not
  name the term; it names a placement.
- `dev/PLAN.md:509-527`, the `[LJ-1.58]` to `[LJ-1.63]` rows. **TOOK:**
  `[LJ-1.61]`'s "63 pc of the cost was module-header elaboration, not any
  definition", which is the earlier form of this report's `Miscellaneous`
  finding, and `[LJ-1.62]`'s "KFacts cuts Miscellaneous by 34 s", which is why
  section 2 treats the record as a delivered WIN rather than a suspect.
- `agents/tasks/archive/LJ-1-57/`, listed; not read, because `[LJ-1.57-A]`'s
  row already carries the number and the term it names is a placement.
- `dev/LESSONS.md`: P-x at `:3582`, P-w at `:3112`, P-t at `:2619`, P-q at
  `:2651`, P-m at `:2478`, P-n at `:2501`, P-o at `:2527`, P-l at `:2323`,
  C-12 at `:2093`, D-1 at `:1038`, C-40 at `:3620`. **TOOK:** P-t's licence to
  seal a built formula, which is the cure; P-w's three classes, which is what
  probe B tested and refuted; P-q's warning, which is why the cure adds lines
  and deletes none.
- `dev/ledger.toml:2632`, `ac_baseline_ghcrts = "-A64m -I0 -M8g"`, and
  `:2712-2713`, the 0.011828 baseline over 17,185 lines. **TOOK:** the
  caliber, so every run above is comparable to the bar.
- `scripts/check-probes.py:1-40`, the owner's ruling of 2026-08-13. **TOOK:**
  the probe's home and that it is tracked and never deleted.
- `agents/tasks/LJ-1-144/ProbeLJ1144A.agda:57`. **TOOK:** the module-naming
  convention `LJ-1-144.ProbeLJ1144A` for a probe under `agents/tasks/<task>/`.
  I read one line and nothing else in that directory.

## 9. THE PROBES

Four files, tracked, beside this report, all GREEN at exit 0 under
`--safe`:

| file | question | verdict |
|---|---|---|
| `ProbeLJ1145A.agda` | does the TYPE cost? does a seal on it help? | NO and NO |
| `ProbeLJ1145B.agda` | does the module APPLICATION cost? | NO |
| `ProbeLJ1145C.agda` | does the cost transplant, and where is it? | YES, and it is one coercion |
| `ProbeLJ1145D.agda` | does the seal on the MACHINE formula cure it? | **YES, 2,459 ms to below 1** |

## 10. NEGATIVES, classified as the brief asks

- **P-x, the record-field lead: REFUTED. MEASURED.** Section 2. The field is
  not in the master, the record that is costs 0.7 percent, and its field types
  name a sealed atom.
- **P-w, the module-application lead: REFUTED at this site. MEASURED.**
  Section 3.2. Removing the application cost more, not less.
- **A seal on the master's own built formula: REFUTED. MEASURED.** Probe A,
  12 ms to 10 ms.
- **A single dominant definition: DOES NOT EXIST. MEASURED.** Section 4.6.
- **Interface production as a curable term: REFUTED. MEASURED.** Section 4.6.
  The master is below the tree's bytes-per-line average.
- **The same-file effect (the master's `out` at 9,267 ms against the probe's
  3,858 ms for identical text): INFERRED.** I did not measure it.
- **The 65 percent coercion share at the other 79 out/back definitions:
  INFERRED.** Measured at one.
- **The mechanism (a split reduces the type, the signature names it folded):
  INFERRED.** The three timings are measured; the explanation is mine.
