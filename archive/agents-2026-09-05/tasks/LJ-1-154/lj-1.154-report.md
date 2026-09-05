# LJ-1.154 report: carve the identity graph by separation, not by replacement

**STATUS: COMPLETE against the abort criterion.** Written incrementally (C-22).
Four probe files, 34 Agda runs, zero heap walls, no master touched.

## 0. LEAD FINDING

**GO, and by a factor of 17 against the criterion and a factor of 147 against
the object it replaces.**

**The identity graph on an L-set carves with ONE `hasSeparationL` and NO
replacement. The whole file elaborates in 1.67 to 1.81 s cold. The mean of NINE
kept runs is 1.73 s, over three independent series, each with its warm-up
discarded, at one-minute loads of 4.32 to 5.48.** The criterion asked for under
30 s.

**`[LJ-1.136]`'s `src/ProbeLJ1136A.agda` builds the same graph by
`hasReplacementL` and costs 254.22 s.** The same file ran 260.37 s and 270.53 s
for `[LJ-1.152]`. **My file does MORE than that file: it adds the bound, the
readback to an honest function, and a C-38 witness that shows the graph is
exactly `{<a,a>}`.**

**Net of the import baseline the carve costs 0.46 s.** The baseline is measured
here and not carried over (P-l): `ProbeLJ1154B.agda` is my import block with no
body, and it costs 1.23 to 1.31 s, mean 1.27.

**So the answer to the open question is YES: the device BUILDS, it does not only
COMPOSE.** The pairs `<x, x>` for `x` in `A` live inside a set you can name
before you build them. The set is a stage, the family is indexed by `⟪ fst A ⟫`,
and naming it needs no replacement. Section 6 gives the bound.

**A SECOND FINDING, and it closes a gap `[LJ-1.152]` named and left open.**
`ProbeLJ1154C.agda` is `ProbeLJ1154A.agda` with EVERY `opaque` block removed and
nothing else changed. **It is green, it costs 1.62 to 1.67 s, and it hits no
heap wall. MEASURED: the three seals are not load-bearing at this site.**
`[LJ-1.136]` measured an 8g heap exhaustion for an unsealed `Small` application
(report section 16.4). **That measurement did not transfer to this site. P-l
again, and this time in the direction that costs nothing to check.**

**A THIRD FINDING, and it answers an objection to the DD4 answer.**
`ProbeLJ1154D.agda` names `hasSeparationL` inside the carve instead of taking it
as a module parameter. **It costs 1.60 to 1.61 s, which is at or below Probe A's own
band. MEASURED: the generality is free, and the parameter hides no cost.**

## 1. THE ABORT CRITERION, restated BEFORE the run (D-1)

Copied from the brief, `agents/tasks/LJ-1-154/LJ-1.154.md:47-57`, and fixed
before the first line of probe code:

- **GO** if the identity graph carves by separation, proves the same four
  conjuncts as `src/ProbeLJ1136A.agda`, and its cold seconds are **under 30**.
- **NO-GO** if the carve needs a `hasReplacementL` after all. Then
  `[LJ-1.136]`'s 254 s stands and A5 is six replacements.
- **STOP** if the carve needs a bound nobody can supply. Name the bound.

The same three lines are inside the probe file, written before its body:
`agents/tasks/LJ-1-154/ProbeLJ1154A.agda:28-33`. **The criterion was not moved
after a number appeared.**

**VERDICT: GO.**

## 2. MACHINE STATE, and it was NOT quiet for the first two series

**16 cores, 64 GB, macOS 25.6.0, Agda 2.8.0. ONE agda process of mine at a time,
always `GHCRTS="-A64m -I0 -M8g"`, cap never raised.**

**A sibling Agda process WAS running for the first two series.** MEASURED,
`ps aux` at 22:04: `agda src/L/Condensation.lagda.md` at 98.7 percent CPU and
11.3 percent memory. That is the orchestrator's `make check`, and the brief said
it would be there. **It had finished before the C, D and second A series.**

**Every figure below carries the one-minute load at the start of its run.** The
load band over all six series is 4.32 to 5.53. **The band is narrow, and the
result does not turn on it:** the widest gap between any two of the three
full-file variants is 0.21 s, against a criterion of 30 s.

**A SECOND SOURCE OF CONTENTION APPEARED, and I did not see it during the
runs.** A sibling task, `[LJ-1.155]`, has files in the tree
(section 12). **I checked `ps aux` for a sibling Agda process before series A1
and after series A2, and not during the C, D and A3 series.** Those three
series ran at loads of 5.27 to 5.53, against 4.32 and 4.66 for the first two.
**MEASURED: the load was higher. INFERRED: a sibling is the likely cause.**
The C, D and A3 figures may carry contention that A1, A2 and B do not.

`[LJ-1.148]` measured a fixed first-run penalty of about 0.9 s per series.
**Reproduced, and it is smaller here.** The six discarded warm-ups were 1.87,
2.67, 1.91, 1.25, 1.65 and 1.64 s, against first kept runs of 1.74, 1.67, 1.81,
1.26, 1.67 and 1.61 s. **The penalty was 0.00 to 0.99 s per series, so 0.9 s is
an upper bound at this site.** Every series below discards its warm-up.

## 3. THE DESIGN, and why it is the cheapest decisive one

### 3.1 The description takes ONE place, and that is the whole difference

Replacement takes a TWO-place description plus a functionality proof
(`src/ProbeLJ1136A.agda:72-93`). Separation takes a ONE-place formula. **The
identity graph fits the one-place shape because the set goes in as a CONSTANT:**

```
idFo A = ∃̇∈ (con A) (prAtL (suc zero) zero zero)
```

`agents/tasks/LJ-1-154/ProbeLJ1154A.agda:94-95`. It reads "p is the pair
`<x, x>` for some x in A". **One line, and the delivered precedent for a
constant is `[LJ-1.152]`'s `appC` (`ProbeLJ1152E.agda:94-95`) and `subFo`
(`src/L/Axioms/Power.lagda.md:108`).**

**Both readings cost 13 lines together**, `ProbeLJ1154A.agda:97-110`. Compare
`[LJ-1.152]`, which needed 20 lines for `appC` alone because a composite
condition must carry TWO graphs out of the context. **A one-graph condition
carries one constant and needs no new reader.**

### 3.2 The bound is GENERIC, and that is a DD4 improvement on `[LJ-1.152]`

`[LJ-1.152]`'s `PairBound` bounds the pairs between two sets
(`ProbeLJ1152E.agda:195-248`). **Nothing in it is about pairs.** It bounds a
small family of L-elements and no more. **So `StageBound` here takes the index
type and the family as parameters** (`ProbeLJ1154A.agda:128-152`), and
`PairBound` is that module at the index type of pairs. 16 lines, against
`PairBound`'s 38.

### 3.3 The carve knows nothing about L

`module Carve` takes the bound AND the separation field as parameters
(`ProbeLJ1154A.agda:167-170`). **No line of Part 3 names an L axiom or an L
stage.** Part 4, `module IdGraph`, is 17 lines and supplies both
(`:287-312`). Section 8 gives the DD4 answer in full, with the residue that
`Carve` still carries.

## 4. THE MEASUREMENTS

**All runs cold: the file's own interface under `_build/` was deleted before
every run. All under `GHCRTS="-A64m -I0 -M8g"`. Load is the one-minute average
at the start of the run.**

### 4.1 The four files, four runs per series, warm-up discarded

| probe | what it is | kept | seconds | load |
|---|---|---:|---|---:|
| `ProbeLJ1154B` | my import block, no body | 3 of 4 | 1.26, 1.31, 1.23 | 4.35 to 4.48 |
| `ProbeLJ1154A` series 1 | **THE CARVE, whole file** | 3 of 4 | 1.74, 1.76, 1.74 | 4.32 |
| `ProbeLJ1154A` series 2 | the same file, later window | 3 of 4 | 1.67, 1.69, 1.68 | 4.66 |
| `ProbeLJ1154A` series 3 | the same file, after a comment-only edit | 3 of 4 | 1.81, 1.77, 1.72 | 5.27 to 5.48 |
| `ProbeLJ1154C` | **the same file, ALL seals removed** | 3 of 4 | 1.67, 1.65, 1.62 | 5.49 to 5.53 |
| `ProbeLJ1154D` | **the same file, separation NAMED** | 3 of 4 | 1.60, 1.61, 1.60 | 5.29 |

**The three A series have means of 1.75, 1.68 and 1.77 s. The widest gap is
0.09 s, which is 5 percent.** `[LJ-1.148]` prices between-series uncertainty at
12.8 percent. **So A, C and D are ONE figure and not three: 1.60 to 1.81 s.**

**C and D sit 0.05 to 0.15 s under A at comparable load. I do not claim that
difference.** It is inside `[LJ-1.148]`'s band. **If it is real it is under
0.2 s, and no verdict in this report turns on it.**

### 4.2 The comparison the task turns on

| | seconds | lines | source |
|---|---:|---:|---|
| the identity graph **BY REPLACEMENT**, whole file | **254.22** | 98 | `[LJ-1.136]` |
| the same file, re-run twice | 260.37, 270.53 | 98 | `[LJ-1.152]` |
| the identity graph **BY SEPARATION**, whole file | **1.73** | 176 | this task |
| the carve, **net of my own import baseline** | **0.46** | 140 | this task |

**Ratio on the whole file: 147 to 1 against `[LJ-1.136]`'s own figure, and 151
to 1 against the three-run mean of 261.71 s. MEASURED, at this site, today.**

**Net against net the ratio is about 550 to 1.** `[LJ-1.152]` measured the
import baseline for `ProbeLJ1136A.agda` at 1.18 s
(`agents/tasks/LJ-1-152/lj-1.152-report.md:140-143`), which puts the
replacement at about 253 s net against my 0.46 s net.

**The comparison understates the result, and I state that rather than hide it.**
My file has 176 non-comment lines against 98, and the extra 78 do work that
`ProbeLJ1136A.agda` never did: the stage bound, the readback through `Small`,
and a C-38 witness. **The 1.73 s buys more than the 254.22 s did.**

### 4.3 The lines

Counted as non-blank non-comment lines. **`scripts/ledger.py` CANNOT count a
probe**, and that is structural, not an omission: "this scan is scoped to
`src/*.lagda.md`, so `agents/` is outside it by construction"
(`scripts/ledger.py:13-15`). **So the caliber is the ledger's, applied by hand to
a `.agda` file, and the figures are consistent within this report.**

| part of `ProbeLJ1154A.agda` | lines | what it is |
|---|---:|---|
| header and imports | 36 | |
| Part 1, `idFo` and both readings | 13 | the one-place description |
| Part 2, `StageBound` | 16 | the bound, generic in index and family |
| Part 3, `Carve` | 77 | the graph, four conjuncts, readback |
| Part 4, `IdGraph` | 17 | **the L instantiation, and the only site of `hasSeparationL`** |
| Part 5, the C-38 witness | 17 | |
| **whole file** | **176** | |

## 5. THE FOUR CONJUNCTS, and they are the same four

**All four closed. The statements are `src/ProbeLJ1136A.agda:134-169` word for
word, with the parameter renamed from `a` to `A`.**

| conjunct | statement | site |
|---|---|---|
| `sv` | `⟨ γ ⊨ svAt zero ⟩` | `ProbeLJ1154A.agda:223` |
| `ij` | `⟨ γ ⊨ injAt zero ⟩` | `:230` |
| `dm` | `⟨ γ ⊨ domAt zero (suc zero) ⟩` | `:237` |
| `ran` | every value lands back in `A` | `:249` |

**`ProbeLJ1154A.agda` is green with `--safe`, exit 0, zero postulates, zero
holes, zero heap walls.** The string `hasReplacementL` appears four times in the
file and **all four are comments** (`:9`, `:32`, `:155`, `:175`).

**The file proves two things `ProbeLJ1136A.agda` does not.**

1. **The readback.** `idFun : ⟪ fst A ⟫ → ⟪ fst A ⟫` with `idFun-inj`, through
   `[LJ-1.134]`'s `Small` (`:259-267`).
2. **`idFun-is-id : (m : ⟪ fst A ⟫) → idFun m ≡ m`** (`:271-278`). **The carved
   graph reads back as the IDENTITY, not as some function.** A graph that
   carves, proves four conjuncts and reads back as something else is the wrong
   graph, and nothing else in the file would catch that.

### 5.1 The C-38 guard, and it is stronger than inhabitation

C-38 as extended: instantiate at a real graph or the GO is vacuous.
`module Witness` (`:325-350`) instantiates the whole interface at
`[LJ-1.134]`'s concrete non-degenerate set `{a}`
(`src/ProbeLJ1134A.agda:190-222`), and `module WitnessZero` fixes `a` at the
numeral zero (`:353`).

**The witness proves the carved graph is EXACTLY `{<a,a>}`:**

- `inG : ⟨ pr (fst a) (fst a) ∈ fst Id.G ⟩`, so it is not empty (`:331`);
- `onlyPair : (z : S) → ⟨ z ∈ˢ Id.G ⟩ → fst z ≡ pr (fst a) (fst a)`, so it
  holds nothing else (`:336`);
- `theIdFun-is-id`, so it runs and returns its argument (`:349`).

**Member for member, the carved graph on `{a}` is `[LJ-1.134]`'s concrete graph
`{<a,a>}` (`src/ProbeLJ1134A.agda:192-193`). Nothing above is vacuous.**

## 6. THE BOUND, AND WHO SUPPLIES IT

**This is the question the brief said to test rather than assume, and the answer
is that the pairs live inside a set you can name before you build them.**

The family is `dg m = prʟ (toA m) (toA m)` over the index type `⟪ fst A ⟫`
(`ProbeLJ1154A.agda:298-300`). **Read that line again, because it is the whole
finding: the family exists BEFORE the graph does.** Four facts supply it, and
every one is delivered:

| step | what supplies it | site |
|---|---|---|
| the index type `⟪ fst A ⟫` is SMALL | the presentation of any set | `src/V/Presentation.lagda.md` |
| each pair `<x,x>` is an element of L | `prʟ`, built from `pairʟ` | `src/L/Coding/Model.lagda.md:326-327` |
| a small family of stages has a bound | `boundingOrd` | `src/L/Ordinal.lagda.md:154-155` |
| a stage is an element of L | `LsetS` | `src/L/Axioms/Basic.lagda.md:160-161` |

**No replacement appears in that column.** It is `hasPowerL`'s own device
(`src/L/Axioms/Power.lagda.md:143-190`) with the resizing dropped, exactly as
`[LJ-1.152]` used it, and this task measures that it BUILDS as well as
COMPOSES.

**Why the composition result did not settle it, stated plainly.**
`[LJ-1.152]`'s composite got its index type from the two END SETS, which
already existed. **A construction has no second set to index by. The identity
graph indexes by the domain's own members instead, and that is the step nobody
had tried.** MEASURED: it works, and it costs 16 lines.

**No bound was missing, so the STOP branch did not fire.**

## 7. A5 RE-PRICED, and it is UNPRICED rather than priced low

### 7.1 What was refuted

`[LJ-1.136]` measured 254 s for ONE write direction and INFERRED A5 at "six
replacements, about 25 minutes"
(`agents/tasks/LJ-1-136/lj-1.136-report.md:1117-1121`). It marked the
multiplication as not a price.

**`[LJ-1.152]` refuted the COUNT: composition is not a replacement.**

**This task refutes the UNIT PRICE, at the exact site where it was measured.**
`ProbeLJ1136A.agda` is the file the 254 s came from, and it builds the identity
graph. **The identity graph costs 1.73 s. So the 25-minute figure has lost its
multiplier AND its multiplicand.** MEASURED.

### 7.2 The six built objects, re-read

`[LJ-1.136]` section 3.1 lists six (`lj-1.136-report.md:206-215`).

| built object | verdict | classification |
|---|---|---|
| composition of two injections | **CARVES.** 2.50 s | **MEASURED**, `[LJ-1.152]` |
| the identity graph, which set the 254 s unit price | **CARVES.** 1.73 s | **MEASURED**, this task |
| `Incl`, the inclusion `β ↪ κ` | carves from a stage bound | **INFERRED** |
| `ShiftAbs` / `Shiftω` | carves from a stage bound | **INFERRED** |
| `pairω`, the pairing on `ω` | carves from a stage bound | **INFERRED** |
| the column square `pair` | carves from a stage bound | **INFERRED** |
| the `CSB` bijection | **UNPRICED, and I did not open it** | **NOT MEASURED** |

**The four inferences are stronger than they were this morning and they are
still inferences.** `[LJ-1.152]` could only say that the device composes. **Now
it also builds, so a graph whose pairs are indexed by a small type is inside the
device whether it is new or derived.** Each of the four still has its own
one-place description to write, and P-l says a measured cure does not transfer
by analogy.

### 7.3 The price, stated as DD8 requires

**A5's seconds are UNPRICED. I will not multiply 1.73 by five.**

**What I state as a price, one number with its basis (DD8): a built injection
that this device reaches costs about 1.7 s cold as a whole file, and about 0.5 s
net of imports. The basis is this task's own measurement at this site, not a
comparable.**

**What is still open is the COUNT, not the unit price.** CSB is the only object
that can put a replacement back into A5, and `[LJ-1.152]` already recorded why
it is different: its graph comes from a back-and-forth recursion, not from a
first-order condition on pairs. **Whether that recursion has a one-place
description is the next question and it is not this one.**

**The DD24 question the brief reserved for the owner is now smaller, and it may
have gone away.** `[LJ-1.136]` framed A5 as "can it be written at a rate the
project accepts". **At 1.73 s for 176 lines the rate is about 0.0098 s per line,
against DD24's bar of about 8.5 s for 590 lines. The rate is not the problem at
any site this device reaches.**

## 8. DD4, ANSWERED AS THE RULE REQUIRES

**Maximize the code the two proofs share, and write it generic. No stop-line
made me write fixed.**

**`[LJ-1.152]` recommended taking the separation field and the stage device as
module parameters. I took the recommendation, and I measured what it costs.**

| part | lines | generic in | names an L axiom or an L stage? |
|---|---:|---|---|
| `idFo`, `IdFo` | 13 | the set, as a plain argument of type `S` | **NO** |
| `StageBound` | 16 | **the index type AND the family** | **YES.** The stage device is its content |
| `Carve` | 77 | the set, the bound, and **the separation field** | **NO** |
| `IdGraph` | 17 | the set | **YES.** It supplies both to `Carve` |

**MEASURED, and the check is one grep: no line of `Carve` names
`hasSeparationL`, `hasReplacementL`, `stage`, `Lset`, `LsetS` or
`boundingOrd`.** The bound, its membership witness and the separation field all
enter as parameters at `ProbeLJ1154A.agda:167-170`. **`[LJ-1.152]` said the gap
to a shared composer was "exactly two names". For the carve the gap is now
closed: both names are arguments.**

**So Parts 1 and 3, which are 90 non-comment lines, carry no L axiom and no L
stage. The J tower instantiates them instead of writing them again. Part 2, 16
lines, is the L bound, and J supplies its own.**

**The honest residue, and I name it rather than claim more.** `Carve` still
sits over the fixed structure `𝒮ʟ` and L's coding layer, because it uses
`prʟ`, `prAtL`, `svAt`, `domAt` and `injAt`. **Those are the model's pair and
graph vocabulary, not L's axioms.** A full two-tower form takes the structure
itself as a module parameter, as `FOL.ZFModel` and `FOL.Absoluteness` already
do. **That refactor is not measured here, and a probe is the wrong place to
run it.**

**And the generality is FREE. MEASURED.** `ProbeLJ1154D.agda` names
`hasSeparationL` inside `Carve` instead of taking it as a parameter. It costs
1.60 s against Probe A's 1.67 to 1.81 s. **The gap is 0.07 to 0.21 s, which is
inside `[LJ-1.148]`'s 12.8 percent between-series band. The parameter costs
nothing that this machine can resolve.**

**`StageBound` is a strict generalization of `[LJ-1.152]`'s `PairBound`.** It
never mentions pairs. `PairBound` is `StageBound` at the index type
`⟪ fst D ⟫ × ⟪ fst C ⟫`. **If A5 lands in a master, one `StageBound` serves
every carve in both towers.**

**One further DD4 note the literature supplies, and section 10 gives the
citation.** The J tower may not need `StageBound` at all: the rud basis
delivers the product `F2(x, y) = x × y` outright
(`dev/literature/rudimentary-functions.md:68`). **So the J side gets the bound
cheaper than the L side, and it re-instantiates `Carve` with a different bound
and the same 90 lines.** INFERRED, from the basis list, not measured.

## 9. THE NEGATIVES, EACH CLASSIFIED

- **MEASURED. The carve needs no `hasReplacementL`.** The string appears four
  times in `ProbeLJ1154A.agda` and all four are comments. The file is green with
  `--safe`, exit 0.
- **MEASURED. The pairs live inside a set you can name before you build them.**
  The family is `dg` at `ProbeLJ1154A.agda:298-300` and the bound is a stage.
  The STOP branch did not fire.
- **MEASURED. The whole file costs 1.67 to 1.81 s cold**, three series, three
  kept runs each, nine runs, loads 4.32 to 5.48. The mean is 1.73 s.
- **MEASURED. The net carve costs 0.46 s**, against my own import baseline of
  1.23 to 1.31 s, re-measured rather than carried over from
  `[LJ-1.152]`.
- **MEASURED. The three seals are NOT load-bearing at this site.**
  `ProbeLJ1154C.agda` removes every `opaque` block and stays green at 1.62 to
  1.67 s. **This closes `[LJ-1.152]` section 6's named gap.** It does NOT say
  the seals are useless elsewhere: `[LJ-1.136]` measured a real heap wall for an
  unsealed `Small` at ITS site. **P-l, in the direction that is cheap to check.**
- **MEASURED. Taking the separation field as a parameter hides no cost.**
  `ProbeLJ1154D.agda`, 1.60 s.
- **MEASURED. Zero heap exhaustions across 34 runs at the 8g cap**, four files.
  The cap was never raised.
- **MEASURED. `dev/literature/devlin-II5.md` names NEITHER axiom.** Zero hits
  for "replacement" and zero for "separation" over 626 lines. **The file the
  brief named cannot answer the literature question.** Section 10 answers it
  from the literature that can.
- **MEASURED. `scripts/ledger.py` cannot count a probe.** Its scan is scoped to
  `src/*.lagda.md` by construction (`scripts/ledger.py:13-15`).
- **INFERRED. Four of the remaining five built objects carve by separation.**
  The device is now measured twice, once composing and once building. The four
  instances are still not measured.
- **INFERRED. The J tower gets the bound cheaper than the L tower.** From the
  rud basis, which delivers `x × y`. Not measured.
- **NOT MEASURED. Whether CSB's graph has a one-place description.** It is the
  only object that can put a replacement back into A5. I did not open it.
- **NOT MEASURED. Peak heap for any run.** No exhaustion is not a heap figure.
- **NOT MEASURED. Whether the 254 s file would get faster if it were re-run
  today.** I did not re-run `src/ProbeLJ1136A.agda`. `[LJ-1.152]` ran it twice
  today at 260.37 and 270.53 s, and I use those figures rather than make a
  fourth run of a file that costs four minutes.

## 10. LITERATURE USED (DD18)

**The brief asked whether Devlin builds these graphs by replacement or carves
them by separation. `dev/literature/devlin-II5.md` cannot answer it, and I say
so first.** MEASURED: that digest covers II.5, the condensation lemma, and it
names neither axiom anywhere in its 626 lines.

**The literature that CAN answer it says: separation, and not replacement.**

- **Devlin's own base theory for this material has Δ0 separation and does not
  have replacement.** `dev/literature/devlin-errata.md:180`, verbatim: "DS = S0
  + Δ0 separation + Π1 foundation + ω ∈ V + S(x) ∈ V".
- **The comprehension theorem is the standard route to these sets.**
  `dev/literature/rudimentary-functions.md:326-327`: "transitive sets closed
  under the rud functions are closed under Δ0 separation, by simulating each Δ0
  formula by a rudimentary function/term." Schindler and Zeman state it as
  Lemma 1.4, Mathias and Bowler as the Bernays theorem "All instances of Δ0
  separation are provable in the system DB0"
  (`dev/literature/rudimentary-functions.md:371`).
- **The bound my carve had to build is DELIVERED in that setting.** The rud
  basis has `F2(x, y) = x × y` (`dev/literature/rudimentary-functions.md:68`),
  and the closure list has "bounded separation y ∩ {z ; R(z, x~)}"
  (`:54`). **So the identity graph on `a` is `(a × a)` cut by a Δ0 condition,
  which is one bounded separation.**

**The conclusion the brief asked for, and it is the conditional the brief
wrote: our 254 s was OUR choice and not the mathematics.** Nothing in the
literature builds an identity graph by replacement. **CAUTION, and it is a real
one: no digest in `dev/literature/` states the identity graph case in those
words. The axiom inventory is quoted; the application to this one graph is
mine.** INFERRED, and marked.

## 11. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-152/ProbeLJ1152E.agda:1-425`, read WHOLE.** **Taken:**
  the constant-carrying formula idiom from `appC` (`:94-95`), the seal
  discipline, the `Small` readback pattern (`:378-386`), and `PairBound`
  (`:195-248`), which I generalized to `StageBound`.
- **`agents/tasks/LJ-1-152/lj-1.152-report.md:1-438`, read WHOLE.** **Taken:**
  the two figures the task turns on (`:32-36`), the seal refutation
  (`:147-163`), section 5.3's naming of this measurement (`:243-252`), and
  section 6's open gap on the seals (`:281-287`), which section 9 closes.
- **`src/ProbeLJ1136A.agda:1-170`, read WHOLE.** **Taken:** the four conjuncts,
  word for word (`:134-169`), and the target the carve replaces (`:99-103`).
- **`agents/tasks/LJ-1-136/lj-1.136-report.md:197-224` and `:1113-1145`.**
  **Taken:** the six built objects, and the "six replacements, 25 minutes"
  inference that section 7 re-prices.
- **`src/ProbeLJ1134A.agda:1-329`, read WHOLE.** **Taken:** `injAt` and
  `injAt-in` (`:61-93`), `module Small` (`:299-328`) for the readback, and
  `module Concrete` (`:190-222`) for the C-38 witness.
- **`src/L/Axioms/Power.lagda.md:143-190`.** **Taken:** the stage-bound device
  in its original home, with the resizing dropped.
- **`src/L/Axioms/Full.lagda.md:144-168`, `hasSeparationL`.** **Taken:** the
  field, and its exact type, which `Carve` takes as a parameter.
- **`src/L/Coding/Model.lagda.md:118-135`, `prAtL` and its adequacy; `:326-330`,
  `prʟ` and `prʟ-fst`.** **Taken:** the description, and the pair builder.
- **`src/L/Ordinal.lagda.md:154-155`, `boundingOrd`; `src/L/Axioms/Basic.lagda.md:160-161`,
  `LsetS`; `src/L/Stage.lagda.md:180-189`, `stage` and its two properties;
  `src/V/Presentation.lagda.md:37-38`, `↪-inj`.** **Taken:** the four facts that
  supply the bound in section 6.
- **`dev/LESSONS.md`: D-1 (`:1038`), C-12 (`:2093`), P-l (`:2323`), P-w
  (`:3112`), C-34 (`:3189`), C-38 (`:3445`), P-y (`:3704`)**, read through
  `scripts/rules.py --for probe` and then in the file.

**`archive/dev/TASKS-archived.md`, `JOURNAL-archived.md`,
`DECISIONS-archived.md` and `STATUS-archived.md` were NOT read.** The task is a
measurement of today's tree, and the retired route has no `hasSeparationL`.
**I record the omission rather than claim a survey.**

## 12. WORKING TREE, as my report describes it

**Five new files, all in `agents/tasks/LJ-1-154/`. No master touched. No file
under `src/` touched. Nothing committed, nothing pushed. No Agda process was
killed and none of mine is running.**

| file | non-comment lines | state |
|---|---:|---|
| `ProbeLJ1154A.agda` | **176** | green, exit 0, `--safe` |
| `ProbeLJ1154B.agda` | 38 | green, exit 0, the import baseline |
| `ProbeLJ1154C.agda` | 173 | green, exit 0, every seal removed |
| `ProbeLJ1154D.agda` | 175 | green, exit 0, separation named |
| `lj-1.154-report.md` | n/a | this file |

**Three files in the tree were already modified when I started and I did not
touch them:** `agents/tasks/LJ-1-153/lj-1.153-report.md`, `dev/PLAN.md` and
`src/L/Condensation.lagda.md`. They are the orchestrator's, and they were
committed while I worked.

**A SIBLING TASK IS ALSO WRITING. MEASURED**, `git status` after my last run:
`agents/tasks/LJ-1-155/` holds two probes, a report, a script and a `runs/`
directory. **None of it is mine and I did not touch it.** Section 2 records
what that may mean for my last three series.

**Interface files under `_build/` for my four probes were deleted repeatedly to
force cold runs. That is a build directory and nothing tracked changed.**

**What is run, after the last Agda run and before this line:**
`scripts/lint-agda.py --check` on all four probes, exit 0 on each;
`scripts/check-probes.py --check`, clean over 1,655 tracked files;
`scripts/lint-prose.py --check` on this report.
**`make check` was NOT run; the brief reserves it to the orchestrator.**

## 13. WHAT IS NOT DONE, named rather than hidden

1. **CSB is not opened.** It is the only object that can put a replacement back
   into A5, and section 7.3 says so.
2. **The four remaining built objects are not measured.** Each needs its own
   one-place description. Each looks like a short file now that the device
   builds as well as composes.
3. **`src/ProbeLJ1136A.agda` was not re-run today.** I compare against
   `[LJ-1.136]`'s 254.22 s and `[LJ-1.152]`'s 260.37 and 270.53 s.
4. **Peak heap was not measured**, only the absence of exhaustion.
5. **The identity graph carved here is not proved EQUAL to `[LJ-1.136]`'s
   replacement graph as an L-element.** The witness proves the two agree member
   for member at the concrete set `{a}` (section 5.1). **A general equality
   would need extensionality and nothing in A5 asks for it.**

**None of the five touches the abort criterion. GO stands on `ProbeLJ1154A.agda`
alone.**
