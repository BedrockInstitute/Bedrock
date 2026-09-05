# LJ-1.575 report: `TFacts` IS UNINHABITED AT EVERY FRAME, SO THERE IS NO VALUE TO BUILD

slot: `coder`. I wrote this file early as a skeleton and I filled it as the runs
landed (C-22, `dev/LESSONS.md:2297`). No commit, no push. I wrote only in
`agents/tasks/LJ-1-575/`. Agda ran under the caliber that the program set on this
pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. **No heap event, no WALL.**

TARGET: one term `tfacts-value` in `agents/tasks/LJ-1-575/Probe575.agda`, a
`TFacts` value at `KValue`'s frame. **I did not deliver it, and section `D-10`
says why: the type has no value.** Nothing lands in `src/`. I did not edit
`src/`. I postulated nothing. I built no `TFacts` value and I applied none.

The standing direction (`dev/pod/direction.md:37`) says one SRC collection after
LJ-1, not after `[LJ-2.5]`. This task is still LJ-1 work. It does not start that
collection and it does not start phase 3. No Boundary clause is in conflict.

## VERDICT

**NO-GO, AND IT IS A REFUTATION AND NOT A SHORTFALL.**

1. **`record TFacts` (`src/L/Condensation/TwelveAgree.lagda.md:129-335`) IS
   UNINHABITED.** Not at `KValue`'s frame only: at EVERY frame, for every `n`,
   every choice of the fifteen indices and every `γ'`. `tfacts-absurd`
   (`Probe575.agda:170-176`) has type
   `TFacts ... → Empty.⊥` and takes no other hypothesis. `--safe` at `:1`,
   exit 0, no hole, no postulate, no `TERMINATING`, no warning on any run
   (`runs/full-0.out`). It typechecked on its first full run
   (`runs/Ref575.first-d10-run.agda.txt` is that run's file, 2.12 s).

2. **THREE FIELDS ARE FALSE, AND EACH ONE ALONE IS ENOUGH.** `valV` (`:244`),
   `valW` (`:250`) and `wKfact` (`:256`). The cause is one dropped hypothesis:
   `tmValAt` is a DISJUNCTION whose right disjunct asks for no membership at
   all (`src/L/Coding/Model.lagda.md:1701-1702`), and the tree's own honest form
   `Fact.tmValK` spends its `tK` exactly there
   (`src/L/Coding/EnvSupply.lagda.md:589-592`). The record's fields quantify
   over the tag cell and take no `tK`.

3. **THE SAME SHAPE IS IN THE TWO PARTIAL BLOCKS, AND I MEASURED THAT TOO.**
   `LFacts.valV`, `LFacts.valW` and `UFacts.wKfact` are refuted at
   `Probe575.agda:199-221`. **Six fields, three records.**

4. **THE COUNT THE BRIEF GIVES IS WRONG IN BOTH DIRECTIONS, AND THE SECOND
   ERROR IS THE ONE THAT MATTERS.** The brief says 54 of 59 collected and five
   uncovered. The predecessors' own reports say 49 and ten. Section `D-10`.

5. **W3 IS GO.** The four predecessors' extra hypotheses DO hold together at one
   frame, with the five free cells PINNED and `[LJ-1.553]`'s membership PAID
   rather than assumed (`Probe575.agda:277-300`). The collections compose. That
   does not make the record true.

6. **THE REPAIR IS SMALL AND IT IS MEASURED.** The three false fields need their
   two memberships back and no new lemma. The repaired block is collected at
   `KValue`'s frame at `Probe575.agda:388-410`.

7. **THREE OF `[LJ-1.512]`'s FIVE "NO SUPPLIER" FIELDS NEED NO SUPPLIER.**
   `t0eq`, `t1eq` and `t0K` are `KFacts`'s own `tagEq0`, `tagEq1` and `numK0`
   once `t0` and `t1` are chosen as frame indices. Collected at
   `Probe575.agda:479-486`.

8. **THE DELIVERED FILE COSTS 786,972,672 B AND 3.97 to 4.07 s, WHICH IS 9.16
   PERCENT OF THE 8 GiB CAP.** Section `THE PRICE`.

I wrote `agents/tasks/LJ-1-575/review-of-tfacts-value.md`. The obligation is NOT
inhabited and it cannot be, so the verdict on the obligation is NO-GO.

**A NOTE ON THE RATIO BAR.** My write scope is one raw `.agda` probe and two
`.md` files. A raw `.agda` file carries no ` ```agda ` fence, so the in-fence
divisor is 0 and the bar cannot fire on this return, as my role section states.

## 0. THE PREDECESSORS, TAKEN FROM THEIR REPORTS

| task | brief's count | the report's count | basis |
|---|---:|---:|---|
| `[LJ-1.512]` | 54 honest forms, 16 ask more | 54 and 16, and FIVE with no supplier | `agents/tasks/LJ-1-512/lj-1.512-report.md:41-42` |
| `[LJ-1.551]` | 38 clean | **37** | `agents/tasks/LJ-1-551/lj-1.551-report.md:23` |
| `[LJ-1.553]` | 13 from one membership | **9** | `agents/tasks/LJ-1-553/lj-1.553-report.md:25-27` |
| `[LJ-1.563]` | 3 | 3, but **each with a named EXTRA** | `agents/tasks/LJ-1-563/lj-1.563-report.md:49-51` |

`[LJ-1.545]` measured the heap and its curve is at
`agents/tasks/LJ-1-545/lj-1.545-report.md:157-190`.

## D-10, BEFORE ANY AGDA: THE COUNT, THEN THE TRUTH

**D-10 says price the TRUTH of the target before pricing its proof
(`dev/LESSONS.md:1375`). I did the count first, then the truth, and the truth
made the count secondary.**

### THE COUNT: TEN UNCOVERED, NOT FIVE

I counted the fields myself. `record TFacts` has **59** field declarations
(`src/L/Condensation/TwelveAgree.lagda.md:133-332`), which agrees with
`[LJ-1.512]` and with `[LJ-1.563]`.

| state | count | which |
|---|---:|---|
| collected at the record's OWN type | **46** | `[LJ-1.551]`'s 37, `[LJ-1.553]`'s 9 |
| collected only WITH a named extra | **3** | `someEnv`, `consK-forall`, `consK-allin` |
| **have a collected value of some kind** | **49** | |
| NOT collected at all | **10** | named below |

**37 + 9 + 3 = 49, and 49 + 10 = 59.** The brief's 54 comes from adding the
brief's own 38 and 13 instead of the reports' 37 and 9. `[LJ-1.563]` already
recorded this arithmetic (`agents/tasks/LJ-1-563/lj-1.563-report.md:332-352`)
and I reproduce it at first hand.

**AT THE RECORD'S OWN TYPE THE GAP IS THIRTEEN AND NOT TEN**, because the three
that `[LJ-1.563]` collected carry extras the record's fields do not have
(`agents/tasks/LJ-1-563/Probe563.agda:149-176`, every extra marked `EXTRA`).

### THE TRUTH: THREE OF THE FIFty-NINE ARE FALSE

The brief's D-10 clause says: if the uncovered fields cannot be supplied, the
record cannot be built and that is the result. **The result is stronger. Three
fields are not merely unsupplied. They are FALSE, and no frame repairs them.**

`tmValAt t e v` is a DISJUNCTION (`src/L/Coding/Model.lagda.md:1701-1702`):

    tmValAt t e v = ∃̇ (tagAtL (suc t) 1 zero ∧̇ appAt (suc e) zero (suc v))
                  ∨̇ tagAtL t 0 v

The right disjunct is `tagAtL t 0 v`, which says only `T ≡ pr (# 0) Val`. **It
asks for no membership: not of the value, not of the environment, not of the
tag.**

`Fact.tmValK` (`src/L/Coding/EnvSupply.lagda.md:575-579`) takes TWO
memberships, `eK` and `tK`, and its `conCase` (`:589-592`) is the one place
`tK` is spent: from `T ≡ pr (# 0) Val` and `T ∈ K` it reads `Val ∈ K` off
`prK`. **Without `tK` there is nothing to read, and a field that quantifies over
the tag cell has no `tK` to spend.**

So one instance refutes the field. Put the K slot itself in the value cell and
`prʟ (numeralL 0)` of the K slot in the tag cell. The field returns `K ∈ K`,
and `∈-irrefl` (`src/V/Hierarchy.lagda.md:155-156`) closes it. That is
`Probe575.agda:92-157`, generic in the frame: **`γ` and `Ks` are free, so the
refutation holds at `KValue`'s frame and at every other frame.**

### WHAT I DID FIRST, AND IT WAS NOT W3

The brief orders W3 first among the Agda. **I ran the D-10 refutation first and
W3 second, and I say so rather than reordering the report.** D-10 comes before
any Agda in the brief's own reasoning section, and the refutation IS the Agda
that settles D-10. Once it landed, W3 could no longer be the guard the brief
wants it to be, so I ran it as a measurement rather than as a gate.

## THE FIVE UNCOVERED

**THE BRIEF ASKS FOR FIVE. THERE ARE TEN.** Each is named at `file:line`, with
what it asks and whether I supplied it.

| # | field | at | what it asks that the record does not give | supplied here? |
|---:|---|---|---|---|
| 1 | `codesK` | `TwelveAgree.lagda.md:162` | that the code slot's members decompose into K AND that the arity is a NUMERAL | **NO** |
| 2 | `codesK-un` | `:168` | the same, at a unary code | **NO** |
| 3 | `t0eq` | `:181` | that the `t0` slot holds `numeralL 0` | **YES** |
| 4 | `t1eq` | `:182` | that the `t1` slot holds `numeralL 1` | **YES** |
| 5 | `t0K` | `:183` | that the `t0` slot is in K | **YES** |
| 6 | `valV` | `:244` | nothing. **IT IS FALSE** | **REFUTED** |
| 7 | `valW` | `:250` | nothing. **IT IS FALSE** | **REFUTED** |
| 8 | `wKfact` | `:256` | nothing. **IT IS FALSE** | **REFUTED** |
| 9 | `envSetK` | `:306` | `envSetGen B ar ∈ K` at a QUANTIFIED `B` | **NO** |
| 10 | `consK-exist` | `:317` | an environment witness for `z`, plus `z ∈ K` and `x ∈ K` | **NO** |

**ROWS 3, 4 AND 5 ARE NEW AND THEY CORRECT `[LJ-1.512]`.** That census looked
for a SUPPLIER and found none. It did not look at the FRAME. `t0` and `t1` are
frame indices the instantiator chooses
(`src/L/Condensation/TwelveAgree.lagda.md:130`), and at `t0 := KV.i0`,
`t1 := KV.i1` the three fields are `KFacts`'s own `tagEq0`, `tagEq1` and
`numK0`, which `KValue` already delivers
(`src/L/Condensation.lagda.md:7411-7425`). They are collected at
`Probe575.agda:479-486` and the type match is Agda's word at `:457-463`.

**ROWS 1 AND 2 ARE UNSUPPLIED ALL THE WAY UP AND THE TREE SAYS SO.**
`gCodesK` and `gUnCodesK` are still unsupplied parameters at `LeafAgree`
(`src/L/Condensation.lagda.md:7262-7275`), which is the outermost module of
this chain. The master's own comment records `[LJ-1.153]` refuting the untied
form (`src/L/Condensation.lagda.md:6977-6987`). **I did not re-open that and I
did not measure it.**

**ROW 9 IS `[LJ-1.551]`'s FINDING AND I DID NOT RE-OPEN IT EITHER.**
`SupplyEnv.envSetK` pins the carrier to `B₀` and has no `B` binder at all
(`src/L/Coding/EnvSupply.lagda.md:140-146`), while the record's field
quantifies over `B` (`agents/tasks/LJ-1-551/lj-1.551-report.md:418-419`).

**ROW 10 IS `[LJ-1.563]`'s THIRD SHAPE.** Its two siblings collect only with the
extras, and `[LJ-1.563]` refuted the blanket supply of those extras
(`agents/tasks/LJ-1-563/Probe563.agda:436-437`).

**ROWS 6, 7 AND 8 END THE TASK.** The other seven rows do not need an answer,
because three fields of the record are false and no answer to the seven can
change that.

## W3, THE WIDEST UNMEASURED TERM

The brief names it: whether all four predecessors' hypotheses hold together at
one frame. **THEY DO.** `four-hypotheses-hold-together`
(`Probe575.agda:277-300`) is one value carrying, at `[LJ-1.551]`'s frame with
the five free cells PINNED to `numeralL 0`:

- `[LJ-1.551]`'s `EnvSupply` conjunct at the record's own K slot;
- `[LJ-1.553]`'s ONE supplied membership at cell 1, **PAID from `KFacts.numK0`
  and not assumed**;
- `[LJ-1.563]`'s environment witness for `z₀`, its two memberships, and its
  truncated numeral arity.

**PINNING THE FIVE CELLS IS WHAT MAKES THIS AN INHABITATION.** `[LJ-1.553]`
records that its `graphK` reads a FREE cell and that its own guard was weaker
for that reason (`agents/tasks/LJ-1-553/lj-1.553-report.md:47-49`). Here the
cell is `numeralL 0` and the tree pays the membership.

**WHAT W3 NOW PROVES, AND WHAT IT DOES NOT.** It proves the four collections
compose: nothing in the union is contradictory, and a later task may put all
four in one file. **It does not make the record true**, and after the D-10
refutation it could not.

## THE C-42 SWEEP: HOW FAR THE SHAPE EXTENDS

C-42 says a refutation measures one site and the next action is the SWEEP, with
the COUNT before any cure (`dev/LESSONS.md:3752`). Here is the count.

**TWENTY declarations in the condensation chain mention `tmValAt`. SEVENTEEN of
them conclude a K membership from it.** Of the seventeen:

| group | count | tag cell | measured? |
|---|---:|---|---|
| record FIELDS: `TFacts` × 3, `LFacts` × 2, `UFacts` × 1 | **6** | QUANTIFIED | **REFUTED, all six** |
| module PARAMETERS of `MemAgree`, `AllInAgree`, `ExInAgree`, `EqAgree` | **6** | QUANTIFIED | **not measured** |
| module PARAMETERS of `AtomLeaf`, `BndLeaf` | **3** | a module parameter with `aK` beside it | **not measured** |
| transfer lemmas that conclude a formula and not a membership | **2** | n/a | not applicable |

The six refuted are at `src/L/Condensation/TwelveAgree.lagda.md:244`, `:250`,
`:256`; `src/L/Condensation/LowerAgree.lagda.md:179`, `:185`; and
`src/L/Condensation/UpperAgree.lagda.md:179`.

The six unmeasured parameters are at `src/L/Condensation.lagda.md:4446`,
`:4452`, `:5064`, `:5193`, `:5404`, `:5410`. **They quantify over the tag cell
exactly as the record fields do**, so the same instance applies by inspection.
**I did not typecheck any of them and I claim nothing about them.** Refuting a
module parameter needs the module's whole telescope, and AD12 gives this brief
one obligation.

The three at `src/L/Condensation.lagda.md:4219`, `:4226` and `:4811` are
DIFFERENT. `AtomLeaf` and `BndLeaf` fix the tag cell as a module parameter and
carry `aK` beside it (`src/L/Condensation.lagda.md:4208-4214`), so the right
disjunct is closed there. They are untied only at the ENVIRONMENT cell, which is
the left disjunct, and that needs a different instance. **I did not build it.**

**SO THE CURE IS NOT PRICED HERE, WHICH IS WHAT C-42 ASKS.** The count is 6
refuted, 6 of the same shape unmeasured, 3 of a weaker shape unmeasured.

## WHAT THE REPAIR COSTS

**TWO MEMBERSHIPS PER FIELD, ALREADY IN THE TREE, AND NO NEW LEMMA.**

`Fact.tmValK` (`src/L/Coding/EnvSupply.lagda.md:575-579`) is already generic in
the vector length and in the three slots. So each repaired field is ONE
application of it and nothing else (`Probe575.agda:363-386`), and the three are
collected at `KValue`'s frame with `Ktr` paid from the tree
(`Probe575.agda:388-410`), exactly as `[LJ-1.553]` pays it
(`agents/tasks/LJ-1-553/Probe553.agda:346-350`).

`statement-matches` (`Probe575.agda:352-361`) is Agda's word that the three
repaired types are the master's own weakened by the two RESTORED memberships and
by nothing else. **IT CAN NEVER BE CALLED**, because section 2 of the probe
shows its argument type has no value. That is exactly what it is here to
certify, and it is the strongest statement certificate this task can give.

**WHETHER THE CONSUMERS CAN PAY THE TWO MEMBERSHIPS AT THEIR CALL SITES IS A
MATHEMATICAL QUESTION AND IT IS NOT MINE (AD3).** `[LJ-1.563]` named the four
consuming call sites (`agents/tasks/LJ-1-563/lj-1.563-report.md:517-523`).

## THE SIXTH POINT

**EVERY ROW IS A WHOLE-FILE TOTAL ON ONE PANE.** No row is a baseline
subtraction. Three forced rechecks per row, with the interface deleted before
each. The cap is 8 GiB, 8,589,934,592 B.

| fields collected | file | seconds | peak RSS (median) | of the cap | runs |
|---:|---|---|---:|---:|---|
| 0 | the refutation alone, 223 lines | 3.42 to 3.47 | 669,237,248 B | 7.79 % | `runs/refut-0..2.time` |
| 3 tags | **the DELIVERED file, 486 lines** | **3.97 to 4.07** | **786,972,672 B** | **9.16 %** | `runs/full-0..2.time` |
| 3 | `[LJ-1.563]`'s obligation, HERE | 3.83 to 3.91 | 739,672,064 B | 8.61 % | `runs/rerun563-0..2.time` |
| 9 | `[LJ-1.553]`'s obligation, HERE | 3.57 to 3.68 | 695,451,648 B | 8.10 % | `runs/rerun553-0..2.time` |
| 37 | `[LJ-1.551]`'s obligation, HERE | 5.42 to 5.51 | 1,066,844,160 B | 12.42 % | `runs/rerun551-0..2.time` |

**THE PANE IS COMPARABLE AND I CHECKED IT RATHER THAN ASSUMING IT.** I copied
the three predecessors' obligation-only files, changed the module line only, and
ran all three here (`runs/Rerun551.agda.txt`, `runs/Rerun553.agda.txt`,
`runs/Rerun563.agda.txt`).

- `[LJ-1.553]`'s obligation gives 695,451,648 B here against the 695,435,264 B
  `[LJ-1.563]` measured: a difference of 16,384 B, **0.0024 percent**.
- `[LJ-1.563]`'s obligation gives 739,672,064 B here against its own
  740,835,328 B: **0.157 percent**.
- `[LJ-1.551]`'s obligation gives 1,066,844,160 B here, against 1,071,005,696 B
  on `[LJ-1.563]`'s pane (**0.389 percent**) and 1,067,859,968 B on its own
  (**0.095 percent**).

**SECONDS DO NOT CARRY ACROSS PANES AND I DO NOT COMPARE THEM.**
`[LJ-1.553]`'s obligation takes 3.57 to 3.68 s here and `[LJ-1.563]` reports
2.82 to 2.83 s for the same file: this pane is about 27 percent SLOWER.
`[LJ-1.563]` measured the same direction reversed against `[LJ-1.553]`'s pane
(`agents/tasks/LJ-1-563/lj-1.563-report.md:382-384`). **So I compare peak RSS
across panes and I do not compare seconds.**

### WHETHER THE LINEAR READING STILL HOLDS

**MY OWN TWO ROWS ARE NOT POINTS ON `[LJ-1.545]`'s CURVE AND I WILL NOT PUT
THEM THERE.** That curve is peak RSS against the number of `TFacts` fields a
file COLLECTS. My refutation file collects none, and my delivered file collects
three tag fields plus a repaired block that is not a `TFacts` block. **A row
whose x is undefined is not a sixth point.**

**WHAT I CAN TEST IS THE THREE ROWS I MEASURED MYSELF.** A model linear in
field count through (9, 695,451,648 B) and (37, 1,066,844,160 B) has slope
13,264,018 B per field and predicts **615,867,538 B** at three fields. The
measurement at three fields is **739,672,064 B**, an excess of
**123,804,526 B**. `[LJ-1.551]` measured a reproducible band of
**136,265,728 B** in whole-file peak RSS whose cause it could not isolate
(`agents/tasks/LJ-1-551/lj-1.551-report.md:297-324`). **123,804,526 B is 0.91 of
that band, so the linear model is neither confirmed nor refuted at this
resolution.** That is `[LJ-1.563]`'s finding reproduced on a second pane, and it
is the only honest reading of these numbers.

**AND THE BRIEF'S PREMISE 6 IS NARROWER THAN THE BRIEF USES IT.**
`[LJ-1.545]`'s own second table gives THREE different per-field rates for three
different field families under one dominant baseline
(`agents/tasks/LJ-1-545/lj-1.545-report.md:177-190`): 22.8 MB a field for
`subK`, 17.6 MB for the env forms, 9.6 MB for `numK`. **"Linear in the field
count" is a statement about ONE family with that family's constant. It is not a
cross-family law, and it must not fund a task at this scale.**

**NO HEAP EVENT AT ANY AGDA RUN OF THIS TASK.** The highest row is 12.42 percent
of the cap and it is not mine. Mine is 9.16 percent.

### AGAINST THE BRIEF'S ESTIMATE

The brief estimated about 300 lines in the probe, of which the obligation is
about 80, and W3 at about 25 lines and under 60 seconds. Delivered: **486
lines**. The obligation is **0 lines**, because it cannot exist. W3 is
`Probe575.agda:243-300`, **58 lines**, and the whole file typechecks in 4.07 s.
**The refutation that replaced the obligation is 3 shape lemmas and 6
one-line projections, `Probe575.agda:92-221`, 130 lines.**

## THE TWO THINGS THAT RESISTED

1. **`fst (numeralL 0)` DOES NOT REDUCE TO `# 0`.** `numeralL-fst zero` is
   `refl` (`src/L/Axioms/Numerals.lagda.md:180`), which reads as a definitional
   identity, but `numeralL` is not transparent at the use site and the
   elaborator reports `fst (numeralL 0) != V.sett ... EmptyStructure`. The cure
   is one `cong`: `prʟ-fst (numeralL 0) Ks ∙ cong (λ w → pr w (fst Ks))
   (numeralL-fst 0)` (`Probe575.agda:99-100`). **This is the whole difference
   between the first run and the second.**

2. **NOTHING ELSE RESISTED, AND THAT IS THE FINDING'S SIZE.** Every other term
   in this file typechecked on its first run: the three shape lemmas, the six
   projections, W3, the repaired block and the tag block. **A defect that costs
   three lines to expose was in `src/` through four collection tasks and an
   audit.**

## W2 AND W4, ANSWERED

**W2.** `Shape` (`Probe575.agda:92-157`) states the refutation ONCE at a free
`γ` and a free `Ks`, and the six record refutations are six applications of it
(`:170-221`). `ThreeRepaired` (`:316-345`) and `Repair` (`:363-386`) are stated
once at a generic `K` and a generic `γ'`, and `RepairAtFrame` (`:388-410`)
instantiates in exactly one place. `TagFields` (`:449-455`) is the same shape at
the tag block. **No block in this file is written twice, and nothing is stated
in a fixed form that could have been stated generically.** No deadline pushed me
toward a fixed form, so there is no conflict to report. DD4's core constraint is
at `archive/dev/DD-archived.md:22`.

**THE ONE PLACE W2 IS NOT FULLY HONOURED IS NOT MINE.** `W3`, `RepairAtFrame`
and `TagsAtFrame` are concrete in `lam` and `gam` because `SupplyEnv` is, and
`SupplyEnv` is the tree's own concrete-site module
(`src/L/Coding/EnvSupply.lagda.md:107-112`). I did not make it concrete and I
did not make it generic; a module redesign is the mathematician's call under
AD3.

**W4.** Nothing is retired by this task and nothing moves to `archive/`, so
`dev/ARCHIVE.md` gains no row. **The clause's second half asks me to price the
ideal form written fresh today against the chapter I have, and this task has an
unusually sharp answer: the ideal `TFacts` written fresh today is the record it
already is with `Fact.tmValK`'s two memberships on the three `tmVal` fields.**
The measurement is in this file: the repaired block is 30 lines
(`Probe575.agda:316-345`), it uses no lemma the tree does not already have, and
its proof is three applications of an existing generic
(`Probe575.agda:363-386`). **I propose no move**, because C-42 says I must count
the sites before I price a cure. I counted seventeen and I priced nothing.

## WHAT THE NEXT BRIEF NEEDS

1. **DO NOT QUEUE ANOTHER `TFacts` COLLECTION.** The record has no value and
   four tasks collecting its fields cannot change that. The next mathematical
   act is a STATEMENT change, and it is the mathematician's under AD3.
2. **THE STATEMENT CHANGE IS NAMED AND IT IS THREE FIELDS.** Give `valV`,
   `valW` and `wKfact` the two memberships `Fact.tmValK` already asks for. Then
   ask the four consuming call sites whether they can pay them. **The second
   half is the real question and I did not touch it.**
3. **THE SAME QUESTION IS OPEN AT SIX MORE PARAMETERS AND IT IS CHEAP TO
   SETTLE.** `MemAgree`, `AllInAgree`, `ExInAgree` and `EqAgree`
   (`src/L/Condensation.lagda.md:4446`, `:4452`, `:5064`, `:5193`, `:5404`,
   `:5410`) carry the same quantified tag cell. **They are unmeasured and one
   task settles all six**, because `Shape` is already generic in the frame.
4. **`AtomLeaf` AND `BndLeaf` NEED A DIFFERENT PROBE AND IT IS A REFUTATION
   TARGET.** Their tag cell is tied, so the right disjunct is closed. Ask
   whether the LEFT disjunct is refutable there: it needs `z` outside `K` with
   `pr k v ∈ z`, which is a singleton in `L` and nothing more. **Nobody has
   measured it.**
5. **`[LJ-1.512]`'s CENSUS METHOD MISSES FRAME-FREE FIELDS.** It searched for a
   supplier. Three of its five "no supplier" fields need no supplier, only a
   choice of `t0` and `t1`. **A census over the fields of a record whose indices
   are chosen by the instantiator must state the frame it assumes.**
6. **THE FOUR COLLECTIONS DO COMPOSE.** W3 says so at one frame with the free
   cells pinned. If the record is repaired, a single-file collection of all 59
   is not blocked by any interaction between the four groups.
7. **A FIELD COUNT STILL PREDICTS NOTHING AT THIS FRONT'S SIZE**, and I
   reproduced `[LJ-1.563]`'s reading on a second pane. Do not fund a task of
   this size against the brief's premise 6.
8. **A GREEN COLLECTION STILL DOES NOT PREDICT A GREEN APPLICATION**
   (`archive/dev/LJ-dispatch-index.md:137`). I built no value and applied none,
   so I claim nothing about applying one.

## THE WORKING TREE

Files I created, all inside my write scope:

- `agents/tasks/LJ-1-575/Probe575.agda` (486 lines)
- `agents/tasks/LJ-1-575/lj-1.575-report.md` (this file)
- `agents/tasks/LJ-1-575/review-of-tfacts-value.md` (the NO-GO)
- `agents/tasks/LJ-1-575/runs/` (measurement outputs, timings, and the four
  renamed measurement files as `.txt`)

I created and modified nothing else. I did not touch `src/`, `dev/` or
`scripts/`. I did not commit and I did not push.

**GATES, ALL RUN AFTER THE LAST EDIT.** `.venv/bin/python` is absent in this
worktree, as `[LJ-1.512]`, `[LJ-1.545]`, `[LJ-1.551]`, `[LJ-1.553]` and
`[LJ-1.563]` all found; I used `/opt/homebrew/bin/python3.11` and I added no
dependency.

| gate | exit | evidence |
|---|---:|---|
| `scripts/pod/witness.py --code LJ-1-575` | 1 | **1 UNRESOLVED of 1**, `probe_red=False`, `runs/witness-1.out` |
| `scripts/gate/check-probes.py --check` | 0 | 6836 tracked files, `runs/check-probes.out` |
| `scripts/gate/check-fences.py --check` | 0 | 102 masters, `runs/check-fences.out` |
| `scripts/gate/check-rule-ids.py` | 0 | 56 files, 165 lessons, `runs/check-rule-ids.out` |
| `scripts/gate/lint-agda.py --check` | 0 | `runs/lint-agda.out` |
| `scripts/gate/lint-prose.py --check` | 0 | `runs/lint-prose.out` |

**THE WITNESS METER IS RED ON PURPOSE.** It classifies the obligation
`missing exit=42`, which is the code branch `no-go-stated` reads, and I wrote
`review-of-tfacts-value.md` for it. `probe_red=False`: the probe itself is
green.

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md`. READ AND USED.** `:135` reads
  "| LJ-1.71 | Consume TwelveAgree, which nothing consumed | CONVICTS c21b417 | The telescope's tagEq is uninhabited at EVERY frame, machine-checked. The module is vacuous. The LJ-1.55 slot fix HOLDS |".
  **THIS IS THE SAME MODULE AND IT IS NOT THE SAME DEFECT.** `[LJ-1.71]`
  convicted the telescope's `tagEq`; `:137` records that `[LJ-1.72]` FIXED the
  statement. The `tmVal` fields were never in that repair, so `TwelveAgree` has
  now been uninhabited twice for two different reasons. `:137` reads
  "| LJ-1.72 | Repair TwelveAgree, then consume it | STATEMENT FIXED, APPLICATION WALLS | The per-row telescope and the union frame both check green. The application heap-walls at the 8 GB cap |",
  and it is why I say plainly that I applied nothing. `:142` reads
  "| LJ-1.75 | Give each partial only the facts its rows use | 43 of 69; 122.45 s | Better than proportional: 41.6 pc cheaper for a 37.7 pc smaller telescope. Two partials plus composer, 273.88 s |",
  and I took the METHOD only: my import list is trimmed to what the file uses,
  and I funded nothing against that old price.
- **`archive/dev/JOURNAL.md`. READ AND USED.** `:1063` reads
  "- **`[LJ-1.233]:247` calls the `TwelveAgree:519-522` comment STALE. It is NOT.**".
  It records that `[LJ-1.251]` checked `KValue` against `AbstractFrame` and that
  the comment holds at HEAD. **That check was of the INDICES and not of the
  record's inhabitation**, which is why it did not catch what this task caught.
- **`archive/dev/JOURNAL-archived.md`. READ AND USED.** `:4066` reads
  "  vacuously). The repair is a code-set slot with the key required to lie in".
  This is the `[L2.4]` C5 entry, and it is the closest precedent in the archive
  for rows 1 and 2 of `THE FIVE UNCOVERED`: a clause that holds VACUOUSLY at a
  free code-set slot, repaired by tying the slot. I did not price that repair
  and I did not re-open `codesK`.
- **`dev/ARCHIVE.md`. READ, NOT USED.** `:3` reads
  "The registry of Bedrock's retired modules. One entry per module, written at".
  Nothing is retired by this task, so the registry gains no row and it holds no
  entry that bears on `TFacts`.
- **`archive/dev/DECISIONS-archived.md`. NOT READ, DECLINED.** It is the
  archived `D` series. This task rests on no `D` code: W2's constraint is DD4,
  whose text I cite at `archive/dev/DD-archived.md:22`, and the live laws came
  from `dev/LESSONS.md`.

## LITERATURE USED

- **`dev/literature/truncation-and-selection.md`. READ, NOT USED.** `:7` reads
  "`∥ A ∥₁`, and then the proof may not take it. **This file records what each**".
  I opened it because `codesK`'s arity conjunct is a `∥ ∥₁` and I expected to
  need the untruncation question. **I did not need it**: the refutation runs
  through `tmValAt`'s right disjunct, which carries no truncation at all, and I
  did not re-open `codesK`.
- **`dev/literature/devlin-II5.md`. NOT READ, DECLINED.** It is the source
  dossier for the Condensation Lemma's MATHEMATICS. This task is about whether a
  fact-block record has a value in the tree, which is a question about the
  formalisation and not about Devlin. No line of it would change the
  refutation.
- **`dev/literature/digest.md`. NOT READ, DECLINED.** It pins the orthodox form
  of the rud route. This task touches no route choice.
- **`dev/literature/terms-2026-08.md`. NOT READ, DECLINED.** It is a
  terminology dossier for a glossary ruling. I added no term and I named
  nothing new.
- **`dev/literature/glossary-review-2026-08.md`. NOT READ, DECLINED.** Same
  reason: no glossary entry is proposed or touched by this task.
