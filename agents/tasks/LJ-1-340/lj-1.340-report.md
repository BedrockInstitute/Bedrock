# LJ-1.340 report: write the `mu` apparatus generic

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. Build probe. It
lands nothing. Written incrementally (C-22).

## LEAD LINE

**IT WRITES GENERIC AND IT SAVES. MEASURED: 10 lines with every delivered export
kept, and 14 lines if `meet-suc` is retired, against a baseline of 74.** The
generic form is 29 lines. It typechecks. **The seconds delta is ZERO**, and a
third negative control proves the zero is a real zero and not a floor artifact.

## 0. THE BASELINE, RE-MEASURED. The brief's 45 is off by one to three

**MEASURED**, by non-blank code lines inside ` ``agda ` fences:

| block | lines | range |
|---|---:|---|
| Stage `below-case`, `same-case`, with `private` | 7 | `src/L/Choice/Stage.lagda.md:172-179` |
| Stage `meet-suc` | 20 | `src/L/Choice/Stage.lagda.md:181-201` |
| Stage `thePred` | 4 | `src/L/Choice/Stage.lagda.md:255-258` |
| Stage `defStage` seal, 3 definitions | 11 | `src/L/Choice/Stage.lagda.md:260-272` |
| **Stage total, the exact parallel** | **42** | |
| Stage `IsPredOf`, if added | 2 | `src/L/Choice/Stage.lagda.md:169-170` |
| Step `decideSuc`, with `private` | 8 | `src/L/Choice/Step.lagda.md:106-113` |
| Step `atCarve` | 12 | `src/L/Choice/Step.lagda.md:115-126` |
| Step `theCarve` | 3 | `src/L/Choice/Step.lagda.md:128-130` |
| Step `birth` seal, 3 definitions | 9 | `src/L/Choice/Step.lagda.md:132-142` |
| **Step total** | **32** | |

**Step's 32 is exact. MEASURED.** Stage's is 42, or 44 with `IsPredOf` added.
**It is never 45.** `[LJ-1.339]:153` says 45 for the same five items. The delta is
one to three lines. It changes no verdict. I use **42 plus 32 = 74**.

**THE SPLIT THAT DECIDES THE PRICE.** Each site divides into an ARGUMENT and a
SEAL.

- Stage: argument 31 lines (`:172-201` and `:255-258`); seal 11 lines
  (`:260-272`).
- Step: argument 23 lines (`:106-130`); seal 9 lines (`:132-142`).

**The seals are not shared code and they never can be.** They name two different
functions with two different arities. **54 lines of ARGUMENT is all a generic
form can attack.** Every saving below is a saving inside those 54.

## 1. WHAT IS ACTUALLY SHARED

Both sites do the same three things in the same order.

1. **They read a truncated carve out of the least stage.** Stage calls
   `Lset-out` at `:201`. Step calls `Lset-out` at `:130`.
2. **They rename the carve to a successor stage.** Stage substitutes over
   `sym (Lset-suc δ)` at `:194`. Step does the same at `:123`.
3. **They split a `suc∈or≡` disjunction and refute the low branch by
   minimality.** Stage does this at `:196-197`, through `below-case` and
   `same-case`. Step does this at `:125-126`, through `decideSuc`.
4. **They close the truncation on `isPropPredOf`.** Stage at `:257`. Step at
   `:129`.

**THE FOUR LEMMAS BOTH CALL. MEASURED**, by reading both blocks whole:
`Lset-out`, `Lset-suc`, `mem-ord` and `suc∈or≡`. Both also close on
`isPropPredOf` and both use `suc-ord`. **So the shared count is six delivered
names, not four.** `[LJ-1.339]:155` names the four and states the close on
`isPropPredOf` separately, so the two counts agree.

### 1.1 WHAT DIFFERS. Not the carrier, and not the motive

**The carrier is the same. MEASURED.** Both quantify over `S`, both name the
same tower `Lset`, and both conclude at the same `IsPredOf σ δ`.

**The motive is the same. MEASURED.** Both conclude `Σ[ δ ∈ S ] IsPredOf σ δ`,
at `src/L/Choice/Stage.lagda.md:256` and `src/L/Choice/Step.lagda.md:128`.

**ONE THING DIFFERS, AND IT IS THE ORDINAL PROPERTY.**

| site | the property `P` | `P`'s witness |
|---|---|---|
| Stage | `meets u σ`, `:96` | **truncated**: an existential over a member `z` of `u` |
| Step | `x ∈ˢ Lset σ`, through `L.Stage`'s `stage` | **untruncated**: `stage-mem x p` |

**THAT IS A DIFFERENCE OF TRUNCATION DEPTH AND NOTHING ELSE.** Stage pays one
outer `PT.rec` that Step does not: `src/L/Choice/Stage.lagda.md:183` and the
`atMember` helper at `:199-201`. **Step has no counterpart to either line.
MEASURED.**

**So the answer to the brief's question is: neither the carrier nor the motive.
It is only the instantiation, plus one truncation layer.**

## 2. THE GENERIC FORM

**It is 29 lines. It lives in `agents/tasks/LJ-1-340/ProbeGeneric.agda:54-88`.**
It is generic in the ordinal property, and **the property is a MODULE parameter
and never a record field** (C-55).

The form has three parts.

| name | lines | what it is |
|---|---:|---|
| `Carved` | 2 | the datum: an ordinal below `σ` whose successor already has `P` |
| `below-case`, `same-case`, `atCarve` | 18 | the split, written once, with both conclusions written down |
| `predOf` | 3 | the truncation close, on `isPropPredOf` |
| `carveAt` | 7 | `Lset-out`, then the `Lset-suc` rename, then the caller's re-wrap |
| **total** | **29** | |

**`predOf` is the whole successor argument:**

```agda
predOf : (σ : S) → IsOrd σ → isLeastOrd P σ → ∥ Carved σ ∥₁
       → Σ[ δ ∈ S ] IsPredOf σ δ
```

**IT IS NOT A TWO POINT CURVE FIT, AND A THIRD SITE PROVES IT.** Section 6
records the third instance. It typechecks.

### 2.1 The two applications

**Step, 4 lines**, at `agents/tasks/LJ-1-340/ProbeGeneric.agda:120-123`:

```agda
theCarve : (x : S) (p : ⟨ isL x ⟩) → Σ[ δ ∈ S ] IsPredOf (stage x p) δ
theCarve x p = predOf (λ σ → x ∈ˢ Lset σ) (stage x p) (stage-ord x p)
  (stage-earliest x p)
  (carveAt (λ σ → x ∈ˢ Lset σ) (stage x p) x (stage-mem x p) (λ δ hz → hz))
```

**Stage, 11 lines with `meet-suc` kept**, at
`agents/tasks/LJ-1-340/ProbeThird.agda:54-66`. It is `carveMeets` (4 lines),
which strips the extra truncation, then `meet-suc` (3 lines) and `thePred`
(4 lines).

**Stage, 7 lines if `meet-suc` goes**, at
`agents/tasks/LJ-1-340/ProbeGeneric.agda:94-100`.

### 2.2 EVERY DELIVERED SIGNATURE IS REPRODUCED VERBATIM

**MEASURED, mechanically.** A script compared the nine delivered declarations
against the probe declarations, character for character.

| name | delivered at | probe at | result |
|---|---|---|---|
| `meet-suc` | `Stage.lagda.md:181` | `ProbeThird.agda:59` | MATCH |
| `thePred` | `Stage.lagda.md:255` | `ProbeThird.agda:63` | MATCH |
| `defStage` | `Stage.lagda.md:261` | `ProbeGeneric.agda:103` | MATCH |
| `defStage-ord` | `Stage.lagda.md:266` | `ProbeGeneric.agda:108` | MATCH |
| `defStage-suc` | `Stage.lagda.md:270` | `ProbeGeneric.agda:112` | MATCH |
| `theCarve` | `Step.lagda.md:128` | `ProbeGeneric.agda:120` | MATCH |
| `birth` | `Step.lagda.md:133` | `ProbeGeneric.agda:126` | MATCH |
| `birth-ord` | `Step.lagda.md:138` | `ProbeGeneric.agda:131` | MATCH |
| `birth-suc` | `Step.lagda.md:141` | `ProbeGeneric.agda:134` | MATCH |

**So the generic form proves the delivered statements and not weaker ones.**
Both seals sit on top of it and both typecheck.

## 3. THE PRICE

**BASIS (DD8): a probe. Three probe files, all typechecked in this session.**

| | generic form | Stage argument | Step argument | seals | total |
|---|---:|---:|---:|---:|---:|
| **today** | 0 | 31 | 23 | 20 | **74** |
| **generic, `meet-suc` KEPT** | 29 | 11 | 4 | 20 | **64** |
| **generic, `meet-suc` retired** | 29 | 7 | 4 | 20 | **60** |

**IT SAVES 10 LINES with every delivered export kept. MEASURED.**
**IT SAVES 14 LINES if `meet-suc` goes. MEASURED.**

**`meet-suc` has no consumer outside its chapter**, at `[LJ-1.339]:39`. **I did
not re-run that search and I did not price the retirement.** DD13 prices a
retirement from the rewrite side. **So the 14 is INFERRED on that one point, and
the 10 is MEASURED with nothing assumed.**

### 3.1 WHAT THE SAVING IS NOT

**It is not a large saving, and the brief said that answer counts.** 10 lines out
of 54 is 19 percent of the argument, and 10 out of 74 is 14 percent of the pair.

**The real return is not the 10 lines. It is three things the lines do not
show.**

1. **One import edge is retired.** Section 5.2.
2. **Every future site costs 4 to 11 lines instead of 23 to 31.** Section 6
   builds one and measures it at 10.
3. **The chapter stops holding two names for one construction.** `[LJ-1.339]:104`
   measured that `defStage` and `birth` are the same construction under two
   names, and that a search for either misses the other.

## 4. THE SECONDS

**ZERO. MEASURED, same session, one agda process, `GHCRTS="-A64m -I0 -M8g"`, cap
never raised.** The slot count ran before every invocation, with the exact
command the brief fixed. **It returned 0 every time.**

| file | round 1 | round 2 | round 3 |
|---|---:|---:|---:|
| `ProbeEmpty.agda`, imports only | 0.82 s | 0.86 s | 0.82 s |
| `ProbeControl.agda`, both originals verbatim | 0.85 s | 0.82 s | 0.85 s |
| `ProbeGeneric.agda`, form plus both applications | 0.86 s | 0.80 s | 0.88 s |

**The three files are within 0.06 s of each other, and the spread inside one
file is 0.06 s and 0.03 s and 0.08 s. So the spread between files is smaller than
the spread inside one file.**

**C-55 DID NOT FIRE.** `[LJ-1.331]` measured one restructuring of this kind
exhausting 8 GB. **MEASURED here: no heap exhaustion, no wall, no run past 2
seconds.** The reason is P-h and C-55's own cure: the property is a module
parameter, so `predOf` checks at a bound variable and never at a concrete tower
object.

**P-m READS THE CLASS, and it reads it right.** `predOf` is parameterized
content. P-m predicts near 0.01 s per line for that class. **MEASURED: 54 lines
of argument cost less than 0.06 s in total, which is below even that rate.**

**ProbeThird.agda: 1.75 s and 0.93 s.** It imports `L.Reflect`, `FOL.Syntax` and
`FOL.Absoluteness`, which the other three do not. **Its seconds are NOT
comparable to the trio and I do not compare them.**

## 5. THE NEGATIVE CONTROLS, AND ONE OF THEM CHANGED THE ANSWER

**TWO CONTROLS RAN. BOTH MEASURE.**

### 5.1 The empty control, and why it was necessary

`ProbeControl.agda` holds the two delivered arguments copied verbatim under the
generic file's exact imports. It gives the baseline seconds.

**On its own it would have produced a WRONG reading.** Control 0.85 s against
generic 0.86 s reads as "the generic form costs 0.01 s more". **That reading is
false.**

`ProbeEmpty.agda` holds the same imports and **no content at all**. **MEASURED:
0.82 s.** **So 0.82 s is the floor, and the entire content of both files sits
inside the noise above it.** The correct statement is that **neither form has a
measurable check cost**, and only the empty control can say so.

**This is D-1's arithmetic: the control cost one file and 3 seconds of machine
time, and without it the report would have carried a number that means nothing.**

### 5.2 The import control: what Step stops importing

**MEASURED**, by grep over `src/L/Choice/Step.lagda.md`:

| token | occurrences in Step | after the rewrite |
|---|---|---|
| `suc∈or≡` | `:53` import, `:126` only | **the whole `L.Ordinal.Stages` edge goes** |
| `suc-ord` | `:112` only | leaves the `using` list |
| `Lset-out` | `:130` only | leaves the `using` list |
| `𝒟ₒ` | `:116` only | leaves the `using` list |
| `isPropPredOf` | `:129` only | leaves the `using` list |
| `mem-ord` | `:121` and `:556` | **stays**, `:556` still needs it |

**So `L.Choice.Step` drops one import edge and four names. MEASURED.** It adds
three: `Carved`, `predOf` and `carveAt`, all from `L.Choice.Stage`, which it
already imports at `:56`.

**NO MASTER LEAVES EITHER CLOSURE. MEASURED:** `src/L/Choice/Stage.lagda.md:51`
imports `L.Ordinal.Stages` too, so the master stays reachable.

## 6. IS THE FORM GENERIC? A THIRD INSTANCE SAYS YES

**`src/L/Reflect.lagda.md:175` takes the least stage that holds a witness of a
formula, through the SAME `leastOrd` operator.** Its property is
`Wit ψ ρ σ` at `:170`, and **that property has Stage's exact shape: a truncated
existential over a member of `Lset σ`.**

**MEASURED: `predOf` and `carveAt` apply there, unchanged.**
`agents/tasks/LJ-1-340/ProbeThird.agda:72-82` builds "the least stage witnessing
a formula is a successor" in **10 lines**, and the file typechecks.

**That instance crosses a structure boundary.** `Wit`'s witness lives in the L
structure `𝒮ʟ`, at `src/L/Reflect.lagda.md:71`, while the ordinal lives in the V
structure. **The generic form took it with no adapter. MEASURED.**

**NOTHING IN `src/` DEMANDS THAT THIRD INSTANCE TODAY.** It is a capability and
not a saving. **I claim no line for it in section 3.**

## 7. IS STEP'S OWN PROSE RIGHT? HALF RIGHT, AND THE OTHER HALF IS THE 32 LINES

`src/L/Choice/Step.lagda.md:90` says:

> The argument applies verbatim to a single set, and for the same reason.

**THE HALF THAT IS RIGHT. MEASURED.** The split is verbatim, and the carve is
verbatim. `below-case` and `same-case` at `Stage:173-179` and `decideSuc` at
`Step:107-113` are the same two branches. `metAtSuc` at `Stage:192-194` and
`atSuc` at `Step:122-123` are the same substitution. **One `atCarve` and one
`carveAt` cover both, and a third site.**

**THE HALF THAT IS WRONG, AND IT IS THE REASON THE 32 LINES EXIST. MEASURED.**
The two properties sit at different truncation depths, so **the argument does not
apply verbatim.** It applies **after Stage strips one truncation layer**. That
strip is `PT.rec squash₁` at `src/L/Choice/Stage.lagda.md:183`, with the
`atMember` helper at `:199-201`. **Step has no counterpart to either.**

**AND THE PROSE POINTS THE WRONG WAY.** It says Stage's argument transfers down
to Step's case. **MEASURED, from the generic form: Step's application is 4 lines
and Stage's is 7 to 11.** **Step's setting is the SIMPLE one.** Stage's is the
one carrying the extra layer.

**DIRECT REUSE WAS NEVER AVAILABLE, AND THAT IS THE FINDING.** `meet-suc`'s
hypothesis is `⟨ meets u σ ⟩` at `Stage:181`. **Step holds `x ∈ˢ Lset σ` and
`stage x p`, which `L.Stage` builds through its own `leastOrd` call at
`src/L/Stage.lagda.md:177`, not through `μ`. MEASURED.** So Step could not call
`meet-suc` even if it wanted to. **The generic form is what makes the sharing
possible. The prose stated a truth that the delivered interface did not
support.**

## 8. C-57: EVERY SEARCH, WITH HITS READ AND REJECTIONS NAMED

**FIVE SEARCHES RAN. I READ EVERY HIT OF ALL FIVE.** Each ran over `src/` with
`grep -rn --include='*.lagda.md'`.

### Search 1: `IsPredOf`. 10 hits, 10 read

`Step:56`, `Step:117`, `Step:128`, `Stage:169`, `Stage:170`, `Stage:182`,
`Stage:187`, `Stage:200`, `Stage:250`, `Stage:256`. **All ten are in the two
files under test. NO third site. MEASURED.**

### Search 2: `isPropPredOf`. 5 hits, 5 read

`Step:56`, `Step:129`, `Stage:250`, `Stage:251`, `Stage:257`. **Same two files.
MEASURED.**

### Search 3: `Lset-out`. 30 hits, 30 read. THIS SEARCH FOUND THE BRIEF'S FEAR

**REJECTED, with the reason for each:**

- `L/StageCardinal.lagda.md:27`, `:269` (a comment), `:328`. It bounds a
  cardinality. **No minimality premise, so no predecessor.**
- `L/Hierarchy.lagda.md:52`, `:154` and `:161` (both prose), `:209`, `:230`. It
  feeds `lookup`. **No minimality premise.**
- `L/Reflect.lagda.md:51`, `:317`. It bounds an environment. **No predecessor.**
- `L/Constructible.lagda.md:336`, `:338`. **The declaration itself.**
- `L/BoundedSubset.lagda.md:27`, `:1013`. A collapse inclusion.
- `L/Choice/Finite.lagda.md:65`, `:834`, `:988`. Stage zero is empty, and a
  member sits below `ω`. **Neither extracts a predecessor.**
- `L/Axioms/Basic.lagda.md:52`, `:210`. An axiom proof.
- `L/Choice/Stage.lagda.md:48`, `:201` and `L/Choice/Step.lagda.md:50`, `:130`.
  **The two sites under test.**

**NOT REJECTED, AND IT IS THE FIND: `Lset-out′` at
`src/L/Coding/Bound.lagda.md:120-125`.**

```agda
Lset-out′ : (α x : S) → ⟨ x ∈ˢ Lset α ⟩
          → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ α ⟩ × ⟨ x ∈ˢ Lset (sucV δ) ⟩) ∥₁
```

**THAT IS THE CARVE ADAPTER, WRITTEN GENERIC, DELIVERED, AND WITH THREE
CONSUMERS.** MEASURED, the three: `src/L/Coding/Key.lagda.md:44` and `:764`, and
`src/L/Coding/EnvSupply.lagda.md:68`, `:205` and `:912`.

**SO THE BRIEF'S AT-RISK PREMISE IS HALF WRONG, EXACTLY AS THE BRIEF FEARED.**
The brief says「the operation was never written generic」. **MEASURED: one half
of it was, under a name neither the brief nor `[LJ-1.339]` searched for.** The
comment above it at `src/L/Coding/Bound.lagda.md:119` even names the shape:
「`Lset-out` lands in `𝒟ₒ` and `Lset-suc` renames it」. **The successor
extraction is still not generic anywhere. That half of the premise holds.**

**AND THE EDGE IS REFUSED, WITH A NUMBER.** Using `Lset-out′` would cut
`carveAt` from 7 lines to 5. **MEASURED, by an import graph walk from the two
declared roots: the edge `L.Choice.Stage` to `L.Coding.Bound` adds 2 masters to
BOTH trophy closures**, namely `L.Coding.Bound` and `L.Ordinal.StageArith`. AC
goes 73 to 75. GCH goes 48 to 50. **Two lines for two masters at both ends is a
bad trade. Keep `carveAt` local.**

### Search 4: `suc∈or≡`. 13 hits, 13 read

**REJECTED as predecessor extractions, and I name all three:**

- `src/L/Ordinal/Stages.lagda.md:139` and `:169`. The declaration, and
  `Lset-cumul`. **It concludes `β ∈ˢ Lset α`, not a predecessor.**
- `src/L/BoundedSubset.lagda.md:993`, inside `sucV∈πX`. **It concludes
  `sucV δ ∈ˢ C.πX`.**
- `src/L/Choice/Faithful.lagda.md:415`, inside `bornIn`. **It CONSUMES `birth`
  and concludes `x ∈ Lset α`.**

**KEPT AS SHAPE, AND IT IS WORTH ONE LINE.** All three write the same two branch
`Sum.rec` over `suc∈or≡` with the conclusion written out. **So the idiom occurs
at FIVE sites in `src/`, not two. MEASURED.** **Only two of the five conclude
`sucV δ ≡ σ`, and those two are the pair under test.** **I did not price a
generic form over the other three, and I claim none.**

### Search 5: `leastOrd`, `isLeastOrd`, `LeastOrd` outside `L/Stage`. 11 hits, 11 read

`src/L/Reflect.lagda.md:54`, `:175`, `:176`, and eight in
`src/L/Choice/Stage.lagda.md`. **The Reflect rows are NOT rejected. They are the
third instance of section 6, and it typechecks.**

### D-10: the inherited absence, re-run

`[LJ-1.339]:145-147` says nothing in `src/` reads the 14 dead exports.
**RE-RUN today for the six the generic form touches**, through searches 1, 2 and
5. **CONFIRMED for `meets`, `Inhabited`, `μ-meets`, `μ-earliest`, `meet-suc` and
`thePred`: no consumer outside the chapter. MEASURED.**

## 9. THE CLOSURE EFFECT ON BOTH ENDS. The axis is AC against GCH

**NAME THE AXIS (C-46): AC against GCH, fixed at `scripts/measure/ledger.py:50`.**

**MEASURED, by an import graph walk from `src/L/Model.lagda.md` and
`src/L/GCH.lagda.md`, run with no Agda:**

| | masters |
|---|---:|
| AC closure | 73 |
| GCH closure | 48 |
| shared | 43 |

**MY WALKER REPRODUCES `[LJ-1.339]:326-327` EXACTLY**, which cross-checks both
tools.

**BOTH CHAPTERS ARE IN BOTH CLOSURES. MEASURED:** `L.Choice.Stage` and
`L.Choice.Step` each return AC=True and GCH=True. **So the generic form is
shared code at both ends by construction. That is rare, and the brief said so.**

**THE FORM COSTS ZERO NEW IMPORTS. MEASURED**, by reading the import block at
`src/L/Choice/Stage.lagda.md:44-68`. `predOf` and `carveAt` need `isLeastOrd`
(`:53`), `mem-ord` and `suc-ord` (`:50`), `suc∈or≡` (`:51`), `Lset-suc` (`:54`),
`Lset-out` (`:48`), `sucV` (`:65`), `Empty`, `Sum` and `PT` (`:56-58`), and
`IsPredOf` and `isPropPredOf`, which the chapter declares. **Every one is already
there.** **So the form lives in `L.Choice.Stage` at zero closure cost, and no new
master enters either trophy.**

**AND IT RETIRES AN EDGE.** Section 5.2 measures it: `L.Choice.Step` drops
`L.Ordinal.Stages`. **No master leaves either closure**, because
`src/L/Choice/Stage.lagda.md:51` imports it too.

**THE GCH FIGURE UNDERSTATES, AND I MARK IT.** `dev/ledger.toml:204` records that
the GCH closure is read from a STATEMENT whose proof is not wired. **My 48
carries that understatement unchanged. I did not correct it and I could not.**

**THE THIRD INSTANCE SERVES BOTH ENDS. MEASURED:** `L.Reflect` returns AC=True
and GCH=True. **So the 10 lines of section 6 would be shared code if a consumer
ever asked for them. None asks today.**

## 10. THE ABORT CRITERION, ANSWERED ROW BY ROW (D-1)

| the brief's row | outcome |
|---|---|
| **IT WRITES GENERIC AND SAVES** | **TAKEN. 29 line form, 11 and 4 line applications, minus 10 lines, zero seconds.** |
| **IT WRITES GENERIC AND SAVES NOTHING** | **NOT TAKEN.** It saves 10 with nothing assumed |
| **THE TWO USES DIFFER MORE THAN THE PROSE SAYS** | **TAKEN IN PART.** Section 7. They differ by one truncation layer, at `src/L/Choice/Stage.lagda.md:183` and `:199-201` |
| **A WALL** | **NOT TAKEN.** No heap exhaustion, no run past 2 s |

## 11. WHAT I DID NOT SETTLE

1. **Whether `meet-suc` should be retired.** DD13 prices a retirement from the
   rewrite side. **I did not price the rewrite.** The 14 line figure depends on
   it. The 10 line figure does not.
2. **The seconds of `L.Choice.Stage` and `L.Choice.Step` themselves.** I checked
   probe files, never the two chapters. **P-l forbids me from moving my probe
   figure onto them by analogy.** **INFERRED, and only INFERRED: the chapters
   should not get slower, because the content class does not change.**
3. **The other three `suc∈or≡` split sites.** Search 4 names them. **I priced no
   generic form over them and I claim none.**
4. **`ord-suc-inj`, `cycle₂` and `mem-branch`.** They are untouched by this work
   and I measured nothing about them.
5. **The prose rewrite.** A landing needs new English, Chinese and Japanese for
   both chapters. **I wrote none and I costed none.**

## 12. ARCHIVE USED (DD18), ONE LINE READ PER FILE

- **`agents/tasks/LJ-1-339/lj-1.339-report.md`, READ WHOLE.** Line read `:153`:
  「**32 non-blank code lines**, against this chapter's ... **45 non-blank code
  lines**」. **TOOK: the file pair, the four shared lemmas at `:155`, the
  no-consumer measurement at `:145-147`, and the closure figures at `:326-327`,
  which my own walker reproduces exactly. CORRECTED: MEASURED 42 for the exact
  five item parallel and 44 with `IsPredOf` added. Never 45.**
- **`agents/tasks/LJ-1-337/lj-1.337-report.md`, READ `:190-210` and `:515-520`.**
  Line read `:200`:「**RECOMMENDATION: keep the 13-line local `sucV-inj` and pay
  ZERO new masters**」. **TOOK: the method, which is to price an import edge in
  MASTERS before taking it. I applied that method to `Lset-out′` in section 8 and
  the answer came back 2 masters at both ends, so I refused the edge.**
  **`[LJ-1.339]:298-323` corrected that recommendation's basis, and my section 9
  agrees with the correction: the trophy delta, not the local delta, is the
  figure that decides.**
- **`archive/dev/TASKS-archived.md`, SHAPE ONLY, never a claim.** Line read
  `:243` (L3.32-T239):「Make the limit clause carrier-generic, as the successor
  clause already is | GREEN, net **+26** at the first site」. **TOOK, SHAPE ONLY:
  the retired route measured a generic rewrite coming out net PLUS lines at its
  first site. So a generic form is not a saving by nature and has to be counted.
  WHAT WOULD NOT TRANSFER: that clause served ONE site at first and mine serves
  TWO that already exist, and every figure of that dispatch lives in `_build/`,
  which is temporary. I quote no number of it as a comparable.**

## 13. LITERATURE USED (DD18)

**No mathematical literature bears on whether an operation is written generic.**
The question is a code sharing question about this tree. **I read no source and I
cite none.**

## 14. DD4, STATED AND ANSWERED

**DD4: maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker.

**ANSWERED, at a site somebody measured.** 54 lines of argument at two sites
become 29 lines written once plus 15 lines of application. **Both sites are in
BOTH trophy closures, so every one of those 29 lines is shared code by
construction.** **The form costs zero new masters and retires one import edge.**

## 15. PROHIBITIONS, ANSWERED

- **Writes: `agents/tasks/LJ-1-340/` only.** Five files: this report, and
  `ProbeControl.agda`, `ProbeEmpty.agda`, `ProbeGeneric.agda`,
  `ProbeThird.agda`. **Nothing in `src/`, nothing in `dev/`, no other task
  directory, no `.claude/`, no `AGENTS.md`.** Three helper scripts sit in the
  session scratchpad, outside the repository.
- **I MOVED NO CHAPTER.** `[LJ-1.339]:196-199` refuted placement with a count and
  I took that ruling.
- **I LANDED NOTHING.**
- **Every agda run: ONE process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised.**
  The slot count ran before every invocation with the brief's exact command, and
  **it returned 0 every time. MEASURED.**
- **No commit, no push, no `make check`.** No `git checkout`, `stash`, `reset` or
  `clean`.
- `.venv/bin/python scripts/dispatch/rules.py --for build`: run, every statement
  read. I opened the full `dev/LESSONS.md` entries for C-12, C-22, D-10, P-h,
  P-l and P-m.
- `.venv/bin/python scripts/gate/lint-agda.py --check`: **clean, exit 0.**
- `.venv/bin/python scripts/gate/check-probes.py`: **clean. 3194 tracked files,
  no probe outside `agents/tasks/`.**
- **MEASURED: no em dash in this file.**
