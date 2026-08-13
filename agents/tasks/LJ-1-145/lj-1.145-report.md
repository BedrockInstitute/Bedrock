# LJ-1.145 report: where the Condensation family's seconds are

**Status: IN PROGRESS.** This file is written incrementally (C-22).

## 0. Machine load, beside every figure

| when | load 1m / 5m / 15m | note |
|---|---|---|
| dispatch | 4.89 / 5.01 / 5.01 | brief's figure |
| start | 3.95 / 4.59 / 4.84 | measured by me |
| before run 1 (`check-ratio`) | 3.23 / 4.09 / 4.55 | 122.64 s result |
| before run 2 (`--profile=definitions`) | 3.10 / 3.95 / 4.48 | 121.19 s result |
| after run 2 | 3.39 / 3.76 / 4.34 | |

**One agda process throughout.** Verified by `ps -eo pid,ppid,etime,%cpu,rss`
at 18:38: PID 63363 was the only `agda` binary. The other matches were the
repository watchdog and my own wrapper.

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

## 3. P-w, the module-application lead

TBD

## 4. The cure, its lines and its seconds

TBD

## 5. DD4: generic or local

TBD

## 6. LITERATURE (DD18)

Nothing in the literature governs elaboration cost.

## 7. ARCHIVE USED

TBD
