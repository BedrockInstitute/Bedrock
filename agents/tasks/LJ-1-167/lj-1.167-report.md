# LJ-1.167 report: the definable power at a general argument, and the pairing closure at a general limit

tier: opus (version `override`). **No master is edited. `git status` shows two
new files, both mine, both in `agents/tasks/LJ-1-167/`. No commit, no push.**
Every negative is marked **MEASURED** or **INFERRED**. Written incrementally
(C-22).

## 0. THE CRITERIA, FIXED BEFORE ANY RUN (D-1, DD8)

### 0.1 The wall-clock criterion, written before the first `agda` invocation

**15 minutes of wall time per `agda` invocation.** `GHCRTS="-A64m -I0 -M8g"`,
**ONE** agda process, **cap NEVER raised.** A sibling is running Agda. Past 15
minutes I record a WALL with its wall clock and its resident set, and I report
the price without that term.

**One run was needed. It took 2.83 s.** Section 4.3.

### 0.2 The line criteria, taken from the brief and NOT moved

- **GAP 1, `pow∈λ`: GO at or below 40 in-fence lines.** NO-GO above, **or if it
  needs a fact nothing supplies**, and then I name that fact.
- **GAP 2, the pairing closure at a general limit: GO at or below 60 lines.**

**I did not move either criterion after I saw a number.** The criteria are also
written into the probe's own header, `ProbeLJ1167A.agda:9-14`, before the code.

### 0.3 How a line is counted

**Non-blank, non-comment lines.** I re-derived `[LJ-1.166]`'s two published
figures with this rule and got **48** for its BLOCK 1 and **40** for its BLOCK 2,
which are its report's own numbers (`agents/tasks/LJ-1-166/lj-1.166-report.md:208-212`).
**The convention is therefore the same one, checked, not assumed.**

## 1. WHAT WAS ALREADY DELIVERED, and this is the lead

**The brief told me to search first and to report the finds before the builds.
Three finds, and the FIRST one closes GAP 2 outright.**

### 1.1 GAP 2 was already CLOSED, by the immediately preceding dispatch

**MEASURED. `[LJ-1.166]` already proved the pairing closure at an arbitrary
limit.** It is `pr∈λ`, at `agents/tasks/LJ-1-166/ProbeLJ1166A.agda:113-136`,
inside a module parameterised by `HullStage`'s own three hypotheses
(`:85-87`). It typechecked at exit 0 in that task.

```
pr∈λ : (x y : S) → ⟨ x ∈ˢ Lset lam ⟩ → ⟨ y ∈ˢ Lset lam ⟩ → ⟨ pr x y ∈ˢ Lset lam ⟩
```

**`lam` is a parameter, not `ω`.** `IsOrd lam` with successor-closure and
`∅ ∈ lam` is a limit ordinal, so this IS the general-limit `κ → κ` pairing
closure that the brief describes as missing.

**`[LJ-1.166]`'s own report offers it for the job**, section 7.3
(`agents/tasks/LJ-1-166/lj-1.166-report.md:371-377`): "Block 1's 48 lines could
instead REPLACE `src/L/Choice/Name.lagda.md:123-132`".

**So GAP 2 needed no new mathematics. It needed a DELIVERY, and the brief
forbids a master.** What no task had measured is whether the replacement is a
drop-in. **I measured that, and it is.** Section 3.

**This is the pattern for the THIRD time in five dispatches, and this time the
missed work is one directory away, in the previous dispatch's own deliverable,
named in its own section 7.3.** `[LJ-1.163]` missed `ElemDown`; `[LJ-1.166]`
missed `src/L/Choice/Name.lagda.md:120-135`; this brief missed
`ProbeLJ1166A.agda:118-141`. **Two of the three misses were of TRACKED, GREEN,
TYPECHECKED code.**

### 1.2 `src/L/Ordinal/StageArith.lagda.md` is a delivered kit with ZERO consumers

**MEASURED, and no brief in this phase has ever cited it.** `grep -rl StageArith
agents/` returns `[LJ-1.7]`, `[LJ-1.20]`, `[LJ-1.21]`, `[LJ-1.26]`, `[LJ-1.46]`,
`[LJ-1.135]` and `[LJ-1.147]`, **none of them in the `K(u)` wing**. In `src/`
the module is imported by `src/Everything.lagda.md:322` and **by nothing else**.

It holds exactly the vocabulary both gaps need:

| name | `src/L/Ordinal/StageArith.lagda.md` | what it is |
|---|---|---|
| `sucIter` | `:34-36` | the finite successor chain above a stage |
| `+ω` | `:41` | the ω-block above a stage, **sealed at birth** |
| `+ω-iter` | `:68` | every finite iterate lies in the block |
| `closedω` | `:81-82` | closure of an ordinal under `d ↦ +ω d` |
| `boundCloses` | `:86-89` | **the climb: `b ∈ Lset (+ω δ)` and `δ ∈ α` give `b ∈ Lset α`** |
| `envCloses` | `:92-96` | the same at `sucIter 3` |

**Its own comment at `:84-85` says what it was built for**: "The code set over
the carrier at δ sits at stage δ+ω. Under closure, the stage δ+ω stays below α
for every δ below α, so the bound lands in Lset α." **That is the `K(u)` bound
question, answered structurally, in a live green file, before this wing began.**

### 1.3 The live tree has NO limit predicate

**MEASURED. `grep -rn "isLimit\|IsLimit" src/` returns nothing.** The retired
route had one (`archive/src/2026-08-09-rud-route/L/Rud/Bridge.lagda.md:56`). The
live tree says "limit" only by carrying `HullStage`'s three parameters
(`src/L/BoundedSubset.lagda.md:903-905`). **That is why `[LJ-1.166]` had to
parameterise rather than re-instantiate, and it is a fact about the tree, not
about the mathematics.**

## 2. GAP 1, the definable power: **NO-GO**, and the reason is NOT the one the brief hoped for

### 2.1 The verdict in three sentences

1. **NO-GO, by the brief's second clause: `pow∈λ` needs a fact nothing in `src/`
   supplies.** I name it in 2.3 and I reduce `pow∈λ` to it in 24 lines, exit 0.
2. **The brief's most-wanted negative does NOT hold. "The definable power is
   FALSE at a general argument" is INFERRED FALSE: the statement is TRUE at
   every limit.** I say this first because the brief asked for the opposite and a
   brief transmits its expectation (C-39). Section 2.5 gives the accounting and
   marks it INFERRED.
3. **The missing fact is the SUCCESSOR-STAGE half. The LIMIT half is free**, and
   it needs nothing about `lam` beyond `HullStage`'s own `succλ`. **MEASURED: my
   reduction uses no limit hypothesis at all except successor-closure.**

### 2.2 What `src/` holds about `𝒟ₒ` at a general argument

**`[LJ-1.166]` wrote "the tree has NO lemma about `𝒟ₒ x` for a general `x`"
(`agents/tasks/LJ-1-166/lj-1.166-report.md:328`). MEASURED: as written that is
FALSE, and the correction matters.** Four lemmas quantify over a general `A`:

| lemma | `file:line` | what it says |
|---|---|---|
| `𝒟ₒ-intro` | `src/L/Constructible.lagda.md:301-304` | a formula plus an equation puts `x` into `𝒟ₒ A` |
| `𝒟ₒ-inv` | `:306-308` | and reads that formula back out |
| `𝒟ₒ∋⊆` | `:313-314` | a member of `𝒟ₒ A` has no member outside `A` |
| `𝒟ₒ-layer` | `:243-244` | `𝒟ₒ` preserves layer-hood |

**What is true is the sharper statement, and it is the one the gap turns on:
NO lemma in `src/` puts `𝒟ₒ x` back into the TOWER for a general `x`.** Every
lemma that lands in the tower is at `𝒟ₒ (Lset δ)`: `Lset-in`
(`src/L/Constructible.lagda.md:319`), `Lset⊆𝒟ₒ` (`:310-311`), `Lset-suc`
(`src/L/Axioms/Basic.lagda.md:196`), `isL-𝒟ₒ` (`:230-231`), `𝒟ₒS` (`:234`),
`𝒟ₒ→isL` (`:98`).

### 2.3 THE FACT NOTHING SUPPLIES, named

**`𝒟ₒ` of a member of a stage lands a bounded number of stages above it.**

```agda
powIter : (δ y : S) → ⟨ y ∈ˢ Lset δ ⟩
        → ∥ Σ[ k ∈ ℕ ] ⟨ 𝒟ₒ y ∈ˢ Lset (sucIter k δ) ⟩ ∥₁
```

**And `src/` already carries this fact as a HYPOTHESIS, twice, in its `isL`
form.** MEASURED:

| hypothesis | `file:line` | statement |
|---|---|---|
| `DefOK` | `src/L/Coding/Powerset.lagda.md:445-446` | `(x : V ℓ) → ⟨ x ∈ 𝒟ₒ (fst A) ⟩ → ⟨ isL x ⟩` |
| `PowOK` | `src/L/Coding/Sequence.lagda.md:131` | `(c w : S) → Records b f γ c w → ⟨ isL (𝒟ₒ (fst w)) ⟩` |

**`PowOK` is the `isL` form of GAP 1 word for word: the definable power of a
general recorded value is constructible.** It is assumed, never proved.

**And MEASURED: it is discharged in exactly one place, and only because the
value is a STAGE.** `src/L/Hierarchy.lagda.md:169-171` rewrites the recorded
value to `Lset (fst c)` and then applies `isL-𝒟ₒ`
(`src/L/Axioms/Basic.lagda.md:230`), which is the stage-only lemma.

**So the tree's own architecture already treats GAP 1 as a side condition.** No
gate in this phase said so.

### 2.4 What Devlin does with the same fact: he asserts it and leaves it

**MEASURED, verbatim, `_build/literature/dev2.txt:632-635`:**

> Proof. As in 2.2 and 2.3. (The details are left as an exercise for the reader.)
> Noting that if lim (α) and α > ω, the set Lα is closed under the function Def
> (this observation forms part of the proof of 2.4), we often state part (ii) of
> 2.4 in the following form:

**Two things follow and both are load-bearing.**

- **Devlin ASSERTS the closure and PROVES nothing.** The closure is a
  parenthetical inside a lemma whose entire proof is "left as an exercise".
  **The one fact GAP 1 needs is the one fact the source leaves unwritten.**
- **He states it for limit `α > ω`**, so his own hypothesis is a limit, not a
  stronger closure. That agrees with section 2.5.

**A correction to the record.** `[LJ-1.166]` cited this remark at
`dev2.txt:640` (`agents/tasks/LJ-1-166/lj-1.166-report.md:90`, `:547`). **The
remark is at `:634`.** Line 640 is the start of `E(f, α)`, a different formula.

### 2.5 Is `pow∈λ` TRUE at a general limit? INFERRED YES, and I show my working

**I mark this INFERRED. It is classical rank accounting, not an Agda
measurement, and C-36 binds.**

For `x ∈ L_δ`, the satisfaction fragments for each formula over `x` are all
first-order definable over `L_δ` from `x`, so **every fragment is already in
`L_{δ+1}`, whatever the formula's quantifier complexity.** Hence `Sat_x` is
definable over `L_{δ+1}` by one existential over those fragments, so
`Sat_x ∈ L_{δ+2}`, and `Def(x)` is definable over `L_{δ+2}` from `Sat_x`, so
`Def(x) ∈ L_{δ+3}`.

**The cost is a UNIFORM FINITE number of stages. It is not `+ω`.** One L-stage
absorbs every quantifier complexity at once, so the recursion on formula
complexity does not cost one stage per step.

**Three consequences, and the second is the one that protects `K(u)`'s price.**

1. **`powIter` should hold with `k = 3`.** INFERRED. I did not fix `k` in the
   probe, because the `∃k` form is the weaker hypothesis and therefore the
   honest one to name.
2. **`closedω` is NOT required.** `HullStage`'s `succλ` is enough. **So GAP 1
   does not re-open `[LJ-1.166]`'s choice of bound, and `KFacts` does not need a
   fourth parameter on `lam`.** I checked this because it was the live risk.
3. **The brief's most valuable negative does not exist.** Section 2.1, point 2.

### 2.6 The reduction, MEASURED

**`agents/tasks/LJ-1-167/ProbeLJ1167A.agda:296-332`, exit 0, first run.**

| part | lines | lines | figure |
|---|---|---:|---|
| `module Pow` header | `:296-297` | 2 | the same three parameters, minus `∅∈λ` |
| `below`, the stage decomposition | `:300-306` | 7 | `Lset-out` then `Lset-suc` |
| `suc^∈λ`, climbing any finite iterate | `:311-313` | 3 | **`succλ` alone** |
| `module Iter`, the reduction proper | `:315-332` | 12 | |
| **TOTAL** | | **24** | |

**24 lines, against a 40-line criterion.** **This is NOT a GO.** The criterion
prices a PROOF of `pow∈λ`; 24 is the price of everything except the fact of
section 2.3. **I report it so the next brief can subtract it, not so it can be
read as a pass.**

**A second reduction, and it is the one that uses the tree's own kit.**
`ProbeLJ1167A.agda:334-344`, **9 lines**, replaces `suc^∈λ` by `closedω` and the
delivered `boundCloses`. It assumes MORE about `lam` and LESS about `𝒟ₒ`.
**`ProbeLJ1167A.agda:353-357` proves the finite-iterate fact implies the
ω-block fact, so the ω-block form is the weaker of the two.** I name the
finite-iterate form as the gap anyway, because section 2.5 says the finite
bound is the true one and a gap should be named at its true strength.

## 3. GAP 2, the pairing closure at a general limit: **GO at 35**

### 3.1 The verdict

**GO. 35 lines against a 60-line criterion, and the 35 were already written by
`[LJ-1.166]`.** I add 15 lines that measure something nobody had: **the general
lemma is a DROP-IN for all three delivered `ω`-only lemmas.**

### 3.2 What the 35 lines are

**`agents/tasks/LJ-1-167/ProbeLJ1167A.agda:104-155`, byte-identical to
`[LJ-1.166]`'s BLOCK 1** except the module name of the file.

| part | lines | lines |
|---|---|---:|
| `module Bound` header, the three parameters | `:104-106` | 3 |
| `At` and `at`, the stage decomposition | `:120-128` | 8 |
| `pr∈λ`, with `climb` and `both` | `:132-155` | 24 |
| **THE PRICED FIGURE** | | **35** |
| `prʟ∈λ`, the same at the model's own pair | `:158-161` | 4 |

**35, and the criterion was 60.**

### 3.3 The new measurement: the general lemma REPLACES the delivered one

**`ProbeLJ1167A.agda:251-277`, 15 lines, exit 0.** It instantiates `Bound` at
`ω` and re-states `src/L/Choice/Name.lagda.md:120-135` from the instance alone.

| delivered lemma | `src/L/Choice/Name.lagda.md` | re-proved at | how |
|---|---|---|---|
| `numeral∈limit` | `:120-121` | `:267-269` | `Bω.num∈λ` plus `numeralL-fst` |
| `pr∈limit` | `:123-124` | `:271-273` | **`Bω.pr∈λ`, with no adapter at all** |
| `tag∈limit` | `:134-135` | `:275-276` | one line from the two above |

**`pr∈limit′ = Bω.pr∈λ` typechecks with nothing between the two sides.** The
general lemma's type at `lam := ω` IS the delivered lemma's type.

**The two hypotheses `ω` must satisfy cost 5 lines**
(`ProbeLJ1167A.agda:255-260`): successor-closure of `ω` from `#∈ω`, and
`∅ ∈ ω` as `#∈ω 0`. **`ω-ord` is delivered** (`src/L/Ordinal.lagda.md:263`).

**So the replacement `[LJ-1.166]` offered is priced: 35 lines in, 20 lines out,
plus 5 lines of `ω` instances.** The 20 are `src/L/Choice/Name.lagda.md:112-135`
counted in-fence, which is the private `AtStage` and `raiseTo` pair, plus the
three lemmas. **`code∈limit`'s consumers keep their exact types.** I did not
perform the replacement. **No master.**

### 3.4 What the archive had, which the brief asked for by name

**The brief asked whether `archive/src/2026-08-09-rud-route/L/Axioms/` had a
general-limit pairing closure. MEASURED: NO.** Its four files
(`Basic`, `Full`, `Power`, `Separation`) hold no limit-indexed closure at all.

**The retired route's general-limit pairing closure is one directory away, and I
measured it: 51 in-fence lines**,
`archive/src/2026-08-09-rud-route/L/Rud/Bridge.lagda.md:252-300`.

| lemma | `:line` | lines |
|---|---|---:|
| `Lstage` | `:252-258` | 12 |
| `Lstage₂` | `:260-278` | 19 |
| `Lpair-limit` | `:280-289` | 10 |
| `Lpr-limit` | `:291-300` | 10 |
| **total** | | **51** |

**TAKEN: the SHAPE, and only that** (`[LJ-1.11]` ruled that route's
condensation target classically false). The shape is the same argument as
`[LJ-1.166]`'s: decompose, merge two stages by trichotomy, climb by successors.
**The live version is 35 against 51, and the difference is structural, not
craft: the retired route had `isLimit`, `limit-succ-mem` and `limit-mem-ord` as
delivered lemmas, and the live tree has none of the three** (section 1.3), so
`[LJ-1.166]` inlined what the retired route imported.

## 4. LINE COUNTS AGAINST THE CRITERIA, AND THE RUN

### 4.1 The two criteria, answered

| gap | criterion | figure | verdict |
|---|---|---:|---|
| **GAP 1**, `pow∈λ` | **40 lines** | **24 for the reduction** | **NO-GO.** It needs the fact of section 2.3, which nothing supplies |
| **GAP 2**, pairing at a general limit | **60 lines** | **35** | **GO** |

**Neither criterion was moved.** GAP 1's NO-GO is by the brief's second clause,
not by the line count: **24 is below 40 and it is still a NO-GO**, because the
24 lines buy the limit half and the fact buys the rest.

### 4.2 The whole probe, part by part

| block | `ProbeLJ1167A.agda` | lines | whose |
|---|---|---:|---|
| BLOCK 1, the bound at an arbitrary limit | `:104-165` | 48 | `[LJ-1.166]`'s, copied |
| BLOCK 2, the `KFacts` value | `:176-220` | 40 | `[LJ-1.166]`'s, copied |
| BLOCK 3, the consumer test | `:222-237` | 6 | `[LJ-1.166]`'s, copied |
| **BLOCK 4, the ω instantiation** | `:251-277` | **15** | **mine** |
| **BLOCK 5, the `pow∈λ` reduction** | `:296-344` | **33** | **mine** |
| **BLOCK 6, which fact is weaker** | `:353-357` | **5** | **mine** |
| **MY TOTAL** | | **53** | |

**BLOCKS 1 to 3 are byte-identical to `[LJ-1.166]`'s file.** Only the module
name changed, and I added a header saying so (`:3-18`). **`[LJ-1.166]`'s file is
not edited.**

### 4.3 One run, no wall

| figure | value |
|---|---|
| runs | **ONE** |
| exit | **0** |
| wall | **2.83 s** |
| resident set | **644 MB** |
| heap cap | `-M8g`. **No heap exhaustion. Cap NEVER raised** |
| process count | **ONE** |
| criterion | 15 minutes. **Not approached** |

**Basis: `/usr/bin/time -l`, warm dependencies, the whole file.** `[LJ-1.166]`
measured the same file, less my 53 lines, at 2.69 s. **So my 53 lines cost 0.14 s
against a 2.69 s fixed load, and I mark that difference as being inside the
noise of one process start rather than as a per-line measurement.**

**DD24 is not usefully answered at this size** and I say so rather than publish
a ratio that means nothing: the numerator is import loading.

## 5. DID P-i's IMPLICIT-INDEX REPAIR FIRE? **NO, and it was never needed**

**MEASURED. It did not fire, because nothing walled: run 1 was exit 0.**

**So this task does NOT give P-i's implicit-index repair its third measurement.**
The brief said a third firing would admit it as a law. **I did not produce one,
and I will not manufacture one from a wall I did not meet.**

**What I can report is that the repair was applied PROPHYLACTICALLY and the
first run passed.** Every implicit set index in my 53 lines is given explicitly:
`Lset-mono {α = lam} {β = sucIter k (sucV δ)}` and `{x = 𝒟ₒ x}`
(`ProbeLJ1167A.agda:325-326`), and `Lset-mono {α = +ω δ} {β = sucIter ... δ}`
with `{x = 𝒟ₒ y}` (`:356-357`). **INFERRED, and I mark it: I cannot tell whether
those would have walled without the annotations, because I never ran the
un-annotated version.** A prophylactic that is never tested is not a
measurement.

## 6. DD4

**Maximize the code the two proofs share, and write it generic. One rule, two
ends, no metric and no checker.**

### 6.1 The measurement, by counting lines that name a tower token

Tokens counted: `Lset`, `𝒟ₒ`, `layer`, `numeralL`, `prʟ`, `LsetS`.

| block | lines | naming a tower | tower-blind |
|---|---:|---:|---:|
| BLOCK 4, the ω instantiation | 15 | **5** | 10 |
| BLOCK 5, the `pow∈λ` reduction | 33 | **19** | 14 |
| BLOCK 5A, the `Iter` form alone | 24 | **13** | 11 |
| BLOCK 5B, the `Block` form alone | 9 | **6** | 3 |
| BLOCK 6, `iter→block` | 5 | **5** | 0 |

### 6.2 Are my two lemmas template? **Split, and I say which half**

**GAP 2's contribution, BLOCK 4: TEMPLATE in shape, per-tower in names.** Ten of
its fifteen lines are tower-blind, and they are the whole `ω` half: `succω` and
`∅∈ω` speak only of the ordinal `ω`, which both towers share. **The five
tower-naming lines are the three re-statements, and they exist only to prove the
drop-in.** At the J end the instantiation argument is the same and the three
statements change name.

**GAP 1's contribution, BLOCK 5: NOT template as written, and the reason is
structural rather than stylistic.** Nineteen of its 33 lines name a tower,
because the STATEMENT does: `pow∈λ` is about `𝒟ₒ` and `Lset`, and the J tower's
definable-power step is its own operator. **`below`, `suc^∈λ` and the two
`PT.rec` skeletons are tower-blind and are 14 lines.**

**The load-bearing DD4 fact is the SHAPE, not the count.** Both reductions have
one form: decompose at the limit, apply the missing successor-stage fact, climb.
**Nothing in that form is L-specific.** Parameterise over the stage function and
the missing fact, and the same reduction serves the J tower.

**I do NOT price the generic variant, because I did not write it.** The brief
forbids estimating a variant I did not write, and `[LJ-1.166]` already published
a +6/−42 figure for BLOCK 1 that my work neither confirms nor tests.

**No stop-line pushed me toward writing fixed.** I wrote the reduction against
the L names because the probe's job was to name the missing fact, and a generic
wrapper would have added elaboration cost to the thing under measurement.

## 7. WHAT THE NEXT BRIEF SHOULD FUND, offered not assumed

1. **Deliver GAP 2.** The mathematics is done and the drop-in is measured. The
   work is a rewrite of `src/L/Choice/Name.lagda.md:112-135` with a regression
   surface of one consumer, `code∈limit` at `:153-165`. **Nobody has run
   `make check` against it, and that is the only open item.**
2. **Gate `powIter` before anything else in the closure layer.** It is the one
   fact GAP 1 needs, `src/` assumes it twice under `DefOK` and `PowOK`, and
   **Devlin leaves its proof as an exercise.** Section 2.5 says the bound should
   be `sucIter 3`, INFERRED. **The decisive probe is whether `L.Coding`'s
   delivered satisfaction machinery can produce `Sat_x` for a general `x` as a
   member of a stage.**
3. **Read `src/L/Ordinal/StageArith.lagda.md` before pricing any bound.** It is
   green, it is imported by nothing, and it was written for this exact question.

**And one line for the brief writer.** This wing has now missed already-built
work three times in five dispatches, and this time the miss was the previous
dispatch's own file, cited in the previous dispatch's own section 7.3. **The
search that would have found it is `grep -rn "∈ˢ Lset lam" agents/tasks/`.** A
brief that names a term should carry the grep that would find it already
supplied, and this wing has now paid three times.

## 8. EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| the pairing closure at a general limit exists | **MEASURED TRUE, and it was ALREADY BUILT.** `agents/tasks/LJ-1-166/ProbeLJ1166A.agda:118-141` |
| the general lemma is a drop-in for the delivered `ω` ones | **MEASURED TRUE.** `pr∈limit′ = Bω.pr∈λ`, no adapter, exit 0 |
| `pr∈limit` cannot generalise from `ω` | **MEASURED FALSE as a claim about the mathematics.** It is true only of `src/`, where the delivered proof is `ℕ`-indexed |
| `src/` holds a lemma putting `𝒟ₒ x` into the tower for general `x` | **MEASURED FALSE.** Every such lemma is at `𝒟ₒ (Lset δ)` |
| the tree has NO lemma about `𝒟ₒ x` for general `x` | **MEASURED FALSE as written.** Four exist; none lands in the tower. Section 2.2 |
| `src/` assumes the general definable-power closure | **MEASURED TRUE, twice.** `DefOK` (`Powerset:445-446`), `PowOK` (`Sequence:131`) |
| that hypothesis is discharged anywhere for a non-stage | **MEASURED FALSE.** One discharge, `src/L/Hierarchy.lagda.md:169-171`, and it rewrites the value to a stage first |
| Devlin proves the closure | **MEASURED FALSE.** `dev2.txt:632-635`. He asserts it inside a lemma whose proof is "left as an exercise for the reader" |
| the definable power is FALSE at a general argument | **INFERRED FALSE.** Section 2.5. This was the brief's most-wanted negative and it does not hold |
| `pow∈λ` needs `closedω`, not just `succλ` | **INFERRED FALSE.** A uniform finite bound suffices; `succλ` is enough. **So `KFacts` needs no fourth parameter** |
| `pow∈λ` is proved | **MEASURED FALSE. NO-GO.** Only the reduction is proved, 24 lines, and it rests on `powIter` |
| the limit half of `pow∈λ` is the hard half | **MEASURED FALSE.** It is 24 lines and it needs no hypothesis beyond `succλ` |
| the ω-block form is weaker than the finite-iterate form | **MEASURED TRUE.** `iter→block`, `ProbeLJ1167A.agda:353-357`, exit 0 |
| `src/L/Ordinal/StageArith` has consumers in `src/` | **MEASURED FALSE.** Only `src/Everything.lagda.md:322` imports it |
| the live tree has a limit predicate | **MEASURED FALSE.** No `isLimit` anywhere in `src/` |
| the retired route's `L/Axioms/` had a general-limit pairing closure | **MEASURED FALSE.** It is in `L/Rud/Bridge.lagda.md:252-300`, at 51 lines |
| P-i's implicit-index repair fired | **MEASURED FALSE.** One run, exit 0, no wall. **This task does not give the law its third measurement** |
| the prophylactic explicit indices were necessary | **NOT MEASURED.** I never ran the un-annotated version. Section 5 |
| anything walled | **MEASURED FALSE.** One run, 2.83 s, against a 15-minute criterion |
| my 53 lines cost 0.14 s | **NOT CLAIMED as a per-line figure.** The difference is inside one process start. Section 4.3 |
| a cheaper reduction exists | **NOT CLAIMED. C-36.** I measured two and named which is weaker |
| the generic two-tower variant costs +6 and saves 42 | **NOT CLAIMED, and NOT TESTED.** That is `[LJ-1.166]`'s figure for its own block. Section 6.2 |

## 9. CHECKERS AND PROHIBITIONS

| checker | result |
|---|---|
| `scripts/lint-agda.py --check` | **exit 0** |
| `scripts/check-probes.py --check` | **clean, 1,783 tracked files** |
| `scripts/lint-prose.py --check` on this report | **exit 0.** No em dash in either file |
| `make check` | **NOT RUN.** The orchestrator runs it |

**Prohibitions, answered one by one.** **No master edited.** `git status` shows
exactly two new files of mine, `agents/tasks/LJ-1-167/ProbeLJ1167A.agda` and
this report. **`agents/tasks/LJ-1-166/ProbeLJ1166A.agda` is NOT edited**; I
copied it. `src/Everything.lagda.md` never opened. The three `*Agree` masters
and `src/L/Coding/Graph.lagda.md` **read by `grep` and `sed` only, never
edited**. `[LJ-1.164]`'s move untouched. **No commit, no push, no
`git checkout .`, no `stash`, no `reset`, no `clean`.** No probe under `src/`.
**No `postulate`, no hole, no unsolved meta**, and `--safe` is on.

**C-12.** ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, **cap NEVER raised.** A
sibling was running; my single run took 2.83 s, which cannot be explained by
machine load either way.

**I did not build `pow∈λ` into the tree, and I did not build the pairing closure
into the tree.** `src/` is byte-identical to HEAD.

## 10. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-166/lj-1.166-report.md`, READ WHOLE.** TOOK the
  `KFacts`-to-Devlin correspondence (`:107-119`), the already-built closure trio
  (`:151-155`), the "`pr∈limit` is `ℕ`-indexed" measurement (`:167-172`), the
  one-`κ→κ`-closure count (`:185-192`), the `powK` probe (`:337-347`) and the
  in-place-generalisation option (`:371-377`). **Section 1.1 says its BLOCK 1
  already closed GAP 2; section 2.2 corrects its `𝒟ₒ` sentence; section 2.4
  corrects its `dev2.txt:640` citation to `:634`.**
- **`agents/tasks/LJ-1-166/ProbeLJ1166A.agda`, READ WHOLE and COPIED, not
  edited.** BLOCKS 1 to 3 of my probe are its BLOCKS 1 to 3.
- **`archive/src/2026-08-09-rud-route/L/Rud/Bridge.lagda.md:252-300`, READ and
  MEASURED at 51 in-fence lines.** **TOOK the SHAPE**: decompose, merge by
  trichotomy, climb by one successor. **TOOK no claim** (`[LJ-1.11]`).
  Section 3.4.
- **`archive/src/2026-08-09-rud-route/L/Axioms/`, all four files, GREPPED for
  limit-indexed closures. Result: NONE.** This answers the brief's question
  directly and negatively.
- **`archive/src/2026-08-09-rud-route/L/Definability.lagda.md:77-249`, READ
  structurally.** It is the `DefOf` operator itself, with `A∈Def` (`:190`),
  `Def∋⊆A` (`:193`) and `Refine.A⊆Def` (`:249`). **It builds NO closure of `Def`
  at a general argument**, and the live `src/L/Constructible.lagda.md:301-314`
  re-exports the same three facts. **So the archive holds no shape for GAP 1.**
- **`agents/tasks/LJ-1-165/lj-1.165-report.md:186-199`**, the seven K-adequacy
  facts. TOOK the fact that `powK` is one of seven and that none has a supplier.
- **`dev/LESSONS.md`: P-i, C-38 as extended, D-1, P-l, C-36 read whole**; C-12,
  C-22, D-10, R-40 and the rest loaded through
  `.venv/bin/python scripts/rules.py --for probe`. **P-i produced no repair this
  task**, and section 5 says so rather than claim one.
- `archive/dev/`: **NOT read.** No `D`-series ruling bears on a closure lemma or
  a line count, and I mark the omission rather than imply a survey.

## 11. LITERATURE USED (DD18)

- **`_build/literature/dev2.txt:625-637`, READ VERBATIM, and it answers the
  brief's literature question exactly.** **What Devlin assumes about the
  definable power at a general set: that `L_α` is closed under `Def` for limit
  `α > ω`. Whether he proves it: NO.** It is a parenthetical observation
  (`:634-635`) attached to Lemma 2.4, whose entire proof reads "As in 2.2 and
  2.3. (The details are left as an exercise for the reader.)" (`:632`).
  **Corollary 2.5 (`:637`) then rests on it.** Section 2.4.
- **`_build/literature/dev2.txt:590-624`, READ.** `K(u)`'s three pieces and the
  Σ₁ formula `K(w, u)`. **TOOK the confirmation that `Def(u)` is what `D(v, u)`
  describes, so the closure remark is about the same operator my `pow∈λ` names.**
- **`dev/literature/devlin-II5.md:240-260`, READ**, the passage the brief names.
  `:245-255` is the digest's statement that the substrate needs "some bounded
  description with a bound inside the carrier". **It does NOT mention the
  closure of `L_α` under `Def`.** MEASURED: **the digest drops the one fact GAP 1
  turns on**, which is why no gate in this wing has priced it.
- `dev/literature/devlin-errata.md`: **NOT read**, on `[LJ-1.136]`'s measurement
  that the errata touch no part of II.5.
