# LJ-1.331 report: the `RowTies` probe on the `Agree` family

STATUS: COMPLETE. The abort branch that fired is THE RECORD MAKES IT WORSE.
Written incrementally (C-22). Every figure comes from the raw `.out` file named
beside it, never from an excerpt (C-53). Every negative is marked MEASURED or
INFERRED, in those words. ASD-STE100 applies.

## Headline

**NO. The record does not cut seconds. It removes the file's ability to check
at all.** The control checks in **32 and 33 s**, twice, exit 0. The record arm
**exhausts the 8 GB heap after 130 s**, exit 251, and prints no profile.

**THE ABORT BRANCH THAT FIRED IS "THE RECORD MAKES IT WORSE", and the archive's
warning repeats at a new site.** `dev/LESSONS.md` P-l already carries one
measurement of a telescope restructuring that made a `Condensation` worse, 204.7
s to 308.8 s. This is the second, on a different route and a different tree, and
it is not a slowdown but a wall.

**AND THE WALL IS IN THE RECORD DECLARATION, NOT IN THE ROW MODULE.** Arm C
declares the record and leaves `ForallAgree`'s twelve-parameter telescope
untouched. **It walls too, at 131 s.** So the twelve ties cannot even be STATED
as one record at this site, before any caller or any body uses it.

**`no-eta-equality` does not cure it.** Arm D adds the directive the literature
names as the cure for the record-eta hazard. **It walls at 133 s.**

**THE PROPERTY THAT DECIDES IT IS ONE FIELD, NOT TWELVE.** A record of FOUR
`KFacts`-shaped fields is free, 34 s. A record of ONE field, `codesK`, is a
wall, and so is a record of one field `valK`. The two that wall share a type
that states an equation against a `pr` chain over a numeral. The four that are
free do not.

**A stop is a deliverable.** The seconds line that this gate funded is closed by
measurement, not by argument.

## A LAW THIS PROBE PROPOSES, with its measurement

**A hypothesis whose type states an equation against a transparent coded term is
free as a MODULE PARAMETER and a heap wall as a RECORD FIELD.**

**The measurement.** `src/L/Condensation.lagda.md:3857`'s `codesK`, whose type
contains `fst c ≡ pr (fst ar) (pr (# 9) (fst a))`, is one of twelve module
parameters of `ForallAgree` in a 3,959-line copy that checks in **32 s, exit
0**. The same hypothesis, alone, as the ONE field of a record declared at the
same point in the same copy, **exhausts 8 GB after 138 s, exit 251**. Four
`KFacts`-shaped fields declared the same way check in **34 s, exit 0**.
Runs `a1-base`, `h1-codesk`, `g4-kfacts-shaped` in
`agents/tasks/LJ-1-331/runs/`.

**The orchestrator assigns the ID.** I state the measurement, not the number.

## The machine, and it was NOT quiet

| moment | agda slots | load averages | note |
|---|---|---|---|
| task start, 01:51 | 0 | 11.98 10.66 9.07 | `uptime` |
| before `a1-base`, 01:56 | 1 | 19.57 14.23 11.12 | a sibling holds one slot |
| before `a3-base`, 02:02 | 0 | 10.00 11.21 10.68 | |
| before `g2-prchain`, 02:14 | 1 | 9.04 10.81 10.74 | my own paired arm |
| before `h1-codesk`, 02:18 | 1 | 12.47 11.72 11.11 | `[LJ-1.332]`'s probe |
| task end, 02:25 | 1 | 8.91 11.85 11.56 | |

The largest non-agda consumer is `mediaanalysisd` at 126.8 percent CPU, with
`GF-Trader`, `pCloud` and `photolibraryd` behind it. The repository does not
control any of them. Load averages ran between 8.6 and 19.6 across the session, read from the
`# load before` line of each run file.
**Every absolute figure below is INDICATIVE.**

**The verdict does not depend on any absolute figure.** It is a green exit
against a heap exhaustion, and no background load turns 32 s into 8 GB. The
same-session control was run twice and its noise floor is measured below.

**C-12 was held at every invocation.** I counted the slots with the brief's
`awk` command before each run, and `agents/tasks/LJ-1-331/run.sh` refuses to
start at two. I never exceeded one process of my own, except in the three
declared pairs of my own arms, which the run table names.

**THE INTERFACE CACHE IS RESTORED. MEASURED.** The final flagless check,
`GHCRTS="-A64m -I0 -M8g" agda src/L/Condensation.lagda.md`, returns in **3 s,
exit 0** (`agents/tasks/LJ-1-331/runs/r1-restore.out`). It is warm because this
task never edited `src/`: every arm is a copy in `agents/tasks/LJ-1-331/`.
The only interface I deleted was my own probe's `CondA.agdai`, so that the
control could be re-checked cold.

## The module I picked, and why

**`ForallAgree`, `src/L/Condensation.lagda.md:3849`.**

I read the raw profile `agents/tasks/LJ-1-322/runs/a1.out`, not a report's
excerpt (C-53). The file has 127 charged rows whose name contains `Agree`, and
they sum to **36,600 ms**, which reproduces the brief's 36.60 s exactly. The
rows belong to **28** distinct `Agree` modules, so the family's **mean charge is
1,307 ms**.

| candidate | charge | rank of 28 | line |
|---|---|---|---|
| `SatGraphAgree` | 8,594 ms | 1 | 6844 |
| `PropAgree` | 4,816 ms | 2 | 3282 |
| **`ForallAgree`** | **1,301 ms** | **10** | **3849** |
| `TopAgree` | 756 ms | 14 | 3663 |
| `ClauseAgree` | 10 ms | 28 | 4143 |

`ForallAgree` is the module whose charge is **closest to the family mean**: it
is 6 ms from 1,307 ms, and no other module is nearer. It is not the most
expensive, which is `SatGraphAgree` at 6.6 times the mean, and it is not cheap.
It sits early enough in the file that the probe can stop at its end.

## The arms

**Every arm is `src/L/Condensation.lagda.md` lines 1 to 3958**, which is the
prefix that ends with the last line of `ForallAgree`, plus one line to close the
code fence. Nothing after that line can change what comes before it, because
Agda checks a module top to bottom. **Every arm differs from the control in ONE
region, around line 3849, and nowhere else**, which
`agents/tasks/LJ-1-331/make_arms.py --check` proves for all twelve.

| arm | what it changes |
|---|---|
| `CondA` | nothing. The control |
| `CondB` | the twelve ties become a record and the row module takes it |
| `CondD` | the same, plus `no-eta-equality` |
| `CondC` | the record is DECLARED; the row module keeps its telescope |
| `CondF0` | a record of NO fields is declared; telescope kept |
| `CondF1` | a record of one plain `≡` field is declared; telescope kept |
| `CondF6a` | a record of the first six ties is declared; telescope kept |
| `CondF6b` | a record of the last six ties is declared; telescope kept |
| `CondG4` | a record of four `KFacts`-shaped ties; telescope kept |
| `CondG2` | a record of `tagEq` plus `codesK`; telescope kept |
| `CondH1` | a record of `codesK` alone; telescope kept |
| `CondH2` | a record of `valK` alone; telescope kept |
| `CondE` | built, NEVER RUN. See the inventory section |

- **`agents/tasks/LJ-1-331/CondA.lagda.md`**, the control. Verbatim, with the
  module name changed on line 10 and the fence closed.
- **`agents/tasks/LJ-1-331/CondB.lagda.md`**, the record arm. It differs from
  the control in ONE region, lines 3849 to 3900: the twelve tie hypotheses of
  `ForallAgree` become the fields of a `ForallTies` record in the style of the
  file's own `KFacts` block (`src/L/Condensation.lagda.md:6076`), and the row
  module takes one parameter instead of twelve. `open ForallTiesNS.ForallTies
  ties` puts the same twelve names back in scope, so **the body of the row
  module is unchanged**. `agents/tasks/LJ-1-331/make_b.py` builds arm B from
  arm A and asserts both boundaries before it writes.

The control reproduces the source module's cost. `ForallAgree.back` charges
**691 ms** in the control against **696 ms** in the source profile, and
`ForallAgree.out` charges **603 ms** against **605 ms**. The truncation
therefore measures the same module.

## Measurements

Command: `GHCRTS="-A64m -I0 -M8g" agda --profile=definitions <file>`, one
process, through `agents/tasks/LJ-1-331/run.sh`, which refuses to start when two
agda processes already run.

| run | file | wall (s) | exit | Total (ms) | Miscellaneous (ms) | Misc share | slots before |
|---|---|---|---|---|---|---|---|
| `a1-base` | `CondA` telescope | 32 | 0 | 31,242 | 13,251 | 42.4 percent | 1 |
| `b1-record` | `CondB` record | **130** | **251, HEAP EXHAUSTED** | none | none | none | 0 |
| `a2-base` | `CondA` | 3 | 0 | 1,915 | 1,915 | n/a | 0 |
| `a3-base` | `CondA` | 33 | 0 | 31,020 | 13,232 | 42.7 percent | 0 |
| `d1-noeta` | `CondD` record, `no-eta-equality` | **133** | **251, HEAP EXHAUSTED** | none | none | none | 0 |
| `c1-decl-only` | `CondC` record DECLARED, telescope kept | **131** | **251, HEAP EXHAUSTED** | none | none | none | 0 |
| `f1-onefield` | `CondF1` record of 1 field, declared | 34 | 0 | 32,507 | 13,478 | 41.5 percent | 0 |
| `f0-nofield` | `CondF0` record of 0 fields, declared | 33 | 0 | 31,932 | 13,314 | 41.7 percent | 1 |
| `f6a-membership` | `CondF6a` first six ties, declared | **146** | **251, HEAP EXHAUSTED** | none | none | none | 0 |
| `f6b-formula` | `CondF6b` last six ties, declared | **146** | **251, HEAP EXHAUSTED** | none | none | none | 1 |
| `g4-kfacts-shaped` | `CondG4` four `KFacts`-shaped ties | 34 | 0 | 32,406 | 13,406 | 41.4 percent | 0 |
| `g2-prchain` | `CondG2` `tagEq` plus `codesK` | **125** | **251, HEAP EXHAUSTED** | none | none | none | 1 |
| `h1-codesk` | `CondH1` `codesK` alone, one field | **138** | **251, HEAP EXHAUSTED** | none | none | none | 1 |
| `h2-valk` | `CondH2` `valK` alone, one field | **136** | **251, HEAP EXHAUSTED** | none | none | none | 1 |

`f0-nofield` and `f1-onefield` ran together, as did `f6a` and `f6b`, and `g4`
and `g2`. Two agda processes is C-12's cap and never more. **A paired run
inflates the wall seconds of both members**, which is why `f6a` and `f6b` read
146 s to the solo arms' 130. It does not change a green into a wall.

## THE DISCRIMINATING PROPERTY (C-52)

**It is the SHAPE of one field, not the number of fields.**

| record declared | fields | verdict |
|---|---|---|
| none, the control | n/a | **green, 32 and 33 s** |
| `ForallTies0`, the skeleton | 0 | **green, 33 s** |
| `ForallTies1` | 1, a plain `≡` | **green, 34 s** |
| `ForallTiesG4` | 4, every one shaped like a `KFacts` field | **green, 34 s** |
| **`ForallTiesH1`** | **1, `codesK` alone** | **WALL, 8 GB** |
| **`ForallTiesH2`** | **1, `valK` alone** | **WALL, 8 GB** |
| `ForallTiesG2` | 2, one plain plus `codesK` | **WALL, 8 GB** |
| `ForallTies6a` | 6, the membership ties | **WALL, 8 GB** |
| `ForallTies6b` | 6, the formula ties | **WALL, 8 GB** |
| `ForallTies`, the faithful record | 12 | **WALL, 8 GB** |

**FOUR fields of the `KFacts` shape are free. ONE field is a wall when it is
`codesK`, and ONE field is a wall when it is `valK`.** So the field count does
not explain it. **MEASURED.**

**The property the two walling fields share, and the four green ones do not:
their type states an equation against a `pr` chain over a numeral.**

```agda
fst c ≡ pr (fst ar) (pr (# 9) (fst a))
```

`codesK` carries it and then a truncated sum; `valK` carries it and no truncated
sum. **Both wall, so the truncated sum is not the property and the `pr` chain
is. MEASURED.**

**THE SAME TYPE IS FREE AS A MODULE PARAMETER.** Arm A holds `codesK` and `valK`
in `ForallAgree`'s telescope and finishes in 32 s, exit 0.

**This also explains why the file's own `KFacts` works with 29 fields**
(`src/L/Condensation.lagda.md:6076`). Every `KFacts` field states a membership
or an equality of a NAME: `fst (lookup N0 γ) ≡ fst (numeralL 0)`,
`⟨ fst (numeralL 0) ∈ fst (lookup K γ) ⟩`. **None of them builds a coded term
inside its own type. MEASURED, by reading all 29 fields.** So `KFacts` is not a
precedent for `RowTies`: it is a record of a different KIND of tie.

**THIS IS `dev/LESSONS.md` P-l's LAW AT A NEW SITE.** P-l says a statement may
be ABOUT a concrete object without dragging that object's PRESENTATION into its
type. A module parameter's type is elaborated once at the module header and the
variable is then an atom. **A record field's type is part of a type former, and
the transparent `pr` chain inside it is re-formed rather than held as an atom.**

### The confound I ruled out

A heap wall could be my record spelled wrongly rather than the record as such.
**It is not, MEASURED.** Arms `f0-nofield`, `f1-onefield` and `g4-kfacts-shaped`
declare a record with the SAME parameters `{m : ℕ} (C T B N K : Fin m)
(γ : S ^ m)`, the SAME level ascription `Type (ℓ-suc ℓ)` and the SAME
surrounding namespace module, and all three are green at 33 to 34 s. **So the
skeleton, the level and the placement are all sound, and only the field type
separates green from wall.**

Raw files: `agents/tasks/LJ-1-331/runs/`.

**`a2-base` is not a check.** Agda found the interface of `CondA` up to date and
skipped the module, so the run reports 1,915 ms and all of it
`Miscellaneous`. I deleted `_build/2.8.0/agda/agents/tasks/LJ-1-331/CondA.agdai`
and ran the control again as `a3-base`. **The row stays in this table because a
run that measured nothing must be visible, not deleted.**

**`b1-record` printed no profile at all.** Agda prints its profile when it
finishes. It exhausted the 8 GB heap, so it never printed a Total, a
`Miscellaneous` share or one charged row. That absence is a MEASUREMENT and not
an omission.

### The charged rows of the module under test, and the session noise floor

The two control runs are the same content, checked cold twice in one session.
They give this session its own noise floor, at three levels.

| row | `a1-base` | `a3-base` | spread |
|---|---|---|---|
| **Total** | 31,242 ms | 31,020 ms | **0.72 percent** |
| `Miscellaneous` | 13,251 ms | 13,232 ms | 0.14 percent |
| **`ForallAgree.back` plus `.out`** | 691 plus 603, **1,294 ms** | 693 plus 621, **1,314 ms** | **1.55 percent** |
| `PropAgree.subB2T-back`, the same-run charged control | 3,313 ms | 3,218 ms | **2.95 percent** |

**The session noise floor is 0.72 percent at the Total and 2.95 percent at the
largest charged row.** Both sit at or under the 1.35 percent the brief carries
for four flagless full checks, at the Total. **The record arm never printed a
row to compare, because it never finished.**

**The `Miscellaneous` share is 42.4 percent** in `a1-base` and 42.7 percent in
`a3-base`, against the 58.3 percent `[LJ-1.322]` measured on the whole file. So
the truncated arm attributes MORE of its run than the full file does, and the
charged rows below are a larger share of the whole.

## Lines delta

The caliber is non-blank lines inside ` ```agda ` fences.

| arm | whole file | the `ForallAgree` header region |
|---|---|---|
| `CondA`, telescope | 3,603 | 42, lines 3849 to 3890 |
| `CondB`, record | 3,612 | 51, lines 3849 to 3900, of which 4 are comment |

**The record COSTS lines at one module: plus 9 on the file, plus 5 of code in
the region. MEASURED.** The record does not remove the module header; it adds a
declaration beside it. `[LJ-1.307]`'s 990-line saving is a saving at
INSTANTIATION SITES, where a caller spells the telescope again. `ForallAgree`
has **zero** instantiation sites inside `src/L/Condensation.lagda.md`.

**The instantiation census, MEASURED.** `src/L/Condensation.lagda.md` holds
**47** in-file instantiations of an `Agree` module, over **17** of the thirty.
**Thirteen of the thirty are instantiated nowhere in the file**: `BotAgree`,
`AndAgree`, `OrAgree`, `TopAgree`, `NegAgree`, `ForallAgree`, `ClauseAgree`,
`MemAgree`, `AllInAgree`, `ExInAgree`, `ImpAgree`, `EqAgree` and `LeafAgree`.
Their callers sit in `src/L/Condensation/LowerAgree.lagda.md` and
`src/L/Condensation/UpperAgree.lagda.md`, which the funding profile
`agents/tasks/LJ-1-322/runs/a1.out` does not cover.

## The evidence that was already in the funding profile

**The six modules that ALREADY state their ties as a record are the most
expensive in the family. MEASURED, from `agents/tasks/LJ-1-322/runs/a1.out`.**

Six `Agree` modules take a `KFacts` record as a parameter:
`ShapesAgree` (`f` at `src/L/Condensation.lagda.md:6160`), `ClosedAgree`
(`:6449`), `ShapedAgree` (`:6550`), `WitnessAgree` (`:6578`), `SatGraphAgree`
(`:6847`) and `LeafAgree` (`:7109`).

| group | modules | charge | mean per module |
|---|---|---|---|
| the six `KFacts` consumers | 6 | **15,543 ms** | **2,591 ms** |
| the other twenty two | 22 | 21,057 ms | 957 ms |
| the family | 28 | 36,600 ms | 1,307 ms |

**The six carry 42.5 percent of the family's charge from 21 percent of its
modules, and their mean charge is 2.7 times the mean of the modules that do
NOT take a record.** The two most expensive modules in the family,
`SatGraphAgree` at 8,594 ms and `LeafAgree` at 3,041 ms, are both record
consumers.

**This is a correlation and I do not call it a cause.** The record consumers are
also the largest modules by subject matter. It is recorded because it is the
same direction as the measurement above, it was available in the funding profile
before any run, and it is the symptom the literature names.

## Extrapolation to thirty, and its basis (DD8)

**There is no extrapolation, and refusing one is the honest answer.** An
extrapolation multiplies a measured saving. **The measured value at one module
is not a saving and it is not a loss in seconds. It is a heap wall**, so there
is no number to multiply.

**The basis I would have used, named as DD8 asks:** the delta at one module in
the charged middle, times thirty, corrected by the family's mean charge of
1,307 ms. That basis is now unavailable, because the one module returned no
finish.

**What CAN be stated with a basis.** The `Agree` family charges 36,600 ms of a
137,453 ms Total in `agents/tasks/LJ-1-322/runs/a1.out`, which is 26.6 percent.
**A `RowTies` build would have to hold all of it and lose none, and at one
module it loses the whole file.** So the account the gate opened is closed.

## The extent of this refutation (C-42)

**A refutation measures ONE site.** This one measures `ForallAgree` in a
truncated copy of `src/L/Condensation.lagda.md`. Here is the sweep, so the
count is on the record before any cure is priced again.

- **The shape swept:** an `Agree` module whose ties would move from a telescope
  into a record. **Thirty modules carry it**, `agents/tasks/LJ-1-307/lj-1.307-report.md`
  section 1.
- **What I measured:** ONE of the thirty, and only the DECLARATION side of it
  in arms C, F and G.
- **What I did NOT measure, INFERRED nothing about:** the twenty-nine others,
  and the caller side in `src/L/Condensation/LowerAgree.lagda.md` and
  `src/L/Condensation/UpperAgree.lagda.md`. **The caller side is where
  `[LJ-1.307]`'s 990-line saving sits and where the file's own `KFacts` comment
  at `src/L/Condensation.lagda.md:6072` says the record pays.** Nothing here
  refutes a LINES saving at the caller. It refutes the SECONDS claim at the
  definition, which is the account the gate summed.

## Premise check (C-44)

The brief told me to assume it carries a false premise. **It carries three, and
one of them changes what a reader concludes.**

1. **THE ATTRIBUTION IN THE ARCHIVE WARNING IS WRONG, and it matters.** The
   brief says "`[T102]` argued from resemblance and `[T106]` refuted it".
   `dev/LESSONS.md:2355` says the opposite about `[T102]`: **`[T102]` MEASURED
   the telescope lift at its own site and it WORKED, 374.3 s to 82 ms.**
   `[T104]` is the task that argued from resemblance and ran no Agda, and
   `archive/dev/TASKS-archived.md:139` records it as "OVERTURNED (by T106)".
   **The brief's wording discredits the technique. P-l discredits the
   TRANSPLANT.** The action is the same, so the probe was still the right call,
   but a reader of the brief would carry away a false statement about a
   technique this project has measured to work.
2. **THE LEDGER CITATION IS WRONG.** The brief cites `dev/ledger.toml:3106` for
   `src/L/Condensation.lagda.md` being a declared `gch_wing` member. Line 3106
   is prose about the membership criterion. **The declaration is at
   `dev/ledger.toml:565`**, a `[[trophy_split]]` entry with `side = "gch"`.
   The substance holds; the line does not.
3. **THE BRIEF ASSUMES THE RECORD'S SAVING AND THE GATE'S 36.60 s ARE THE SAME
   ACCOUNT. They are not.** The gate summed DEFINITION charges inside
   `src/L/Condensation.lagda.md`. The file's own `KFacts` comment says a record
   "re-elaborates it once per module instead of once per instantiation site", so
   the mechanism pays at INSTANTIATION SITES. **Thirteen of the thirty `Agree`
   modules, `ForallAgree` among them, have ZERO instantiation sites in that
   file. MEASURED.** So for those thirteen the record's own documented mechanism
   had nothing to act on before any run started. **This does not rescue the
   proposal**, because arms C, F6a and F6b wall on the DECLARATION, which every
   module would pay whatever its caller count.

**Two figures in the brief I checked and CONFIRMED.** The `Agree` rows of
`agents/tasks/LJ-1-322/runs/a1.out` sum to exactly **36,600 ms**, and the six
`KFacts` consumers sum to exactly **15,543 ms**. Both reproduce the brief.

## DD4, and its axis (C-46)

**Maximize the code the two proofs share, and write it generic.** The axis is
AC against GCH, fixed in code at `scripts/measure/ledger.py:50`.

`src/L/Condensation.lagda.md` is a declared **GCH-side** master,
`dev/ledger.toml:565`. It is in neither trophy statement, so a cure there serves
the GCH wing's SECONDS account and not the trophy. **This probe lands nothing,
so it changes no shared line in either direction.** What it delivers to DD4 is a
refusal: a `RowTies` build would have spent GCH-wing budget on a form that does
not check.

## ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-322/lj-1.322-report.md:296`.** "measured run-to-run
  spread of the same content in this one session is 1.35 percent". TAKEN: the
  noise floor I had to beat, and I measured my own session's at 0.72 percent.
- **`agents/tasks/LJ-1-322/runs/a1.out:2`.** `Total 137,453ms`. TAKEN: the
  denominator for every share in this report, read from the raw file (C-53).
- **`agents/tasks/LJ-1-307/lj-1.307-report.md:52`.** The list of the thirty
  `Agree` modules with their line numbers. TAKEN: the population I sampled from.
- **`agents/tasks/LJ-1-306/lj-1.306-report.md`.** READ, TAKEN NOTHING, and
  TOUCHED NOTHING. The ruling forbids disturbing that port and my arms are
  copies in my own directory.
- **`dev/LESSONS.md:2355`.** P-l's table row on the telescope lift. TAKEN: the
  shape of the warning, and the correction in the premise check above.
- **`archive/dev/TASKS-archived.md:139`.** "L3.32-T104 | Does T102's cure apply
  to Condensation? | OVERTURNED (by T106)". TAKEN: the SHAPE, that a cure argued
  from resemblance was overturned by measurement, never the claim.
- **`agents/tasks/LJ-1-275/CondControlToday.lagda.md:10`.** The module line of
  an earlier full copy of this file. TAKEN: the proof that a renamed copy of
  this master compiles standalone, which retired the "will not compile as a
  copy" abort branch before I spent a run on it.

## What this task leaves in the tree

**Nothing landed. `src/`, `dev/`, `AGENTS.md` and every other task directory are
untouched.** `git status` shows additions under `agents/tasks/LJ-1-331/` and
nothing else. I ran no `git` command that changes the tree.

**The arms are thirteen near-identical copies of 212 KB each, 2.7 MB in all,
and the record does not have to carry them.** `make_arms.py --check` rebuilds
all twelve derived arms from `CondA.lagda.md` plus `arms.json` and reports
**every one identical, exit 0**. So `CondA.lagda.md` (212 KB), `arms.json`
(21 KB) and `make_arms.py` are a complete and verified record at **233 KB**.
**The orchestrator decides what to commit.** `make_b.py` and `make_e.py` are the
readable originals for arms B and E; `make_arms.py` is the canonical
regenerator, and its `--check` mode is what proves the two agree.

**`CondE.lagda.md` WAS BUILT AND NEVER RUN, and that is deliberate.** It puts
the first six ties in a record AND uses it. Arm `f6a-membership` already walls
on DECLARING those same six, so arm E could only wall for a reason already
measured. **It is kept because it is written, not because it was run.** No
figure in this report comes from it.

## LITERATURE USED (DD18)

**In one line: the literature predicts the record HURTS here, and it did.**

- **`agents/tasks/LJ-1-317/lj-1.317-report.md:143-163`, RANK 3.** Agda issue
  **#6509**, "Agda seems to be very slow at typechecking records with many
  fields", labelled performance, records, **regression in 2.6.0, OPEN**. One
  more line took a file from 30 s to "upwards of a minute". **USED: it is the
  reason I bisected by field count rather than by field position.**
- **The same report, same section.** Danielsson, AIM 32, 2020: "Try to avoid
  making Agda compare large terms", and "records with η-equality don't block
  evaluation". **USED: it names `no-eta-equality` as the cure, so I ran arm D.
  The cure MISSED, 133 s and a heap wall.**
- **The same report at `:46`.** "`no-eta-equality` directives: ZERO. MEASURED"
  in this tree. **USED: it told me arm B's record would carry η by default, so
  arm D was worth its run.**
- **WHY NOT the lossy-unification arm.** `agents/tasks/LJ-1-317/lj-1.317-report.md:172`
  proposes `--lossy-unification` as the flag test for this exact shape.
  **`[LJ-1.322]` already ran it on this file and it returned exit 42 with one
  `UnequalTerms` error**, so the flag is unusable here and I spent no run on it.
- **WHY NOT the with-abstraction literature (RANK 4).** This probe changes no
  `with` block.
