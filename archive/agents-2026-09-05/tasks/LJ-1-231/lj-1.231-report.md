# LJ-1.231 report: DD25 review of `[LJ-1.226]`, where 160 became about 700

tier: opus (deepseek-subagent-mode). Adversarial review. The author was pi, so
DD17's invariant holds. No Agda ran. No master, brief or other report was
edited. No commit, no push. Written incrementally (C-22).

Every negative is marked **MEASURED** or **INFERRED**, in those words.

## 0. VERDICT AND THE NUMBER

**UNQUANTIFIED. 83 lines, and 83 is the whole of the evidence.**

Read that as two findings, not one.

**1. "`pairω` is MATERIALLY OVER 160" is UPHELD. MEASURED.** I re-counted the
anchor myself and it is exact. The target's conclusion stands, and it stands on
firmer ground than the target claimed, for a reason the target did not give.

**2. "The total is about 700" is NOT SUPPORTABLE. MEASURED against the report's
own text.** 190 of the inferred lines carry no basis sentence at all. Two more
rows have a stated basis that measurement contradicts. **And the eight rows do
not sum to the total: they sum to 743.** The 700 is one number where the record
carries a band.

**The band the evidence actually carries: not less than about 355, and nothing
on the record bounds row 5 above.** Section 2.6 derives the 355. It is
**INFERRED** from seven measured comparables at seven different sites, so P-l
binds it and it is a hypothesis, not a price. The 700 sits inside the open
interval. **No measurement chooses between 355 and 700.**

**What I would have the orchestrator write into the plan:** row 5 is over 160,
MEASURED; row 5 is unpriced above that, and 700 must not travel as a point
figure.

**One further finding, and the orchestrator caused it.** The file move did more
than falsify half of section 6. It hid `agents/tasks/LJ-1-134/lj-1.134-report.md`
from the author. That report holds the single closest measured comparable in
this repository for the work the 130-line row prices: **27 lines**
(`agents/tasks/LJ-1-134/lj-1.134-report.md:85-86`). Section 5 gives the detail.

## 1. Q1. IS THE ANCHOR REAL? YES, AND THE 36 AND THE 47 ARE EXACT

**MEASURED. The probe is green.** The interface file is at
`_build/2.8.0/agda/agents/tasks/LJ-1-226/ProbeLJ1226A.agdai`. Agda writes an
interface only after a successful check. I did not run Agda. I read the file
system.

**MEASURED. I re-counted every figure in the target's table.** I used the
caliber the target names, which is non-blank lines minus whole-line `--`
comments.

| part | target's figure | my count | agrees |
|---|---:|---:|---|
| header plus L-side imports | 43 | 43 | yes |
| Part 0, the ambient pairing | 76 | 77 | **off by one** |
| Part 1, `addFo` and its clauses | **36** | **36** | yes |
| Part 2, the witness construction | **47** | **47** | yes |
| whole file | 203 | 203 | yes |

**The two load-bearing figures are exact.** Part 0 is one line out, and the
target's five parts sum to 202 against a whole-file 203. The error is in a row
that the target excludes from the charge, so it moves nothing.

**Part 0's exclusion is CORRECT. MEASURED.** Part 0 is
`agents/tasks/LJ-1-156/ProbeLJ1156A.agda:111-158` copied in, and `[LJ-1.156]`
already carried it at 37 lines (`agents/tasks/LJ-1-156/lj-1.156-report.md:245`).
A5 counts each object once (`agents/tasks/LJ-1-176/lj-1.176-report.md:194-197`).
The ambient pairing is the base and not the charge.

**The caliber is NOT the ledger caliber, and here it is the right choice.**
`AGENTS.md` counts non-blank lines inside ` ```agda ` fences. A bare `.agda`
probe has no fences. A probe's `--` comment block becomes markdown prose in a
master, and prose sits outside the fences. So excluding comments projects the
probe into a master correctly. **MEASURED: the same caliber was used by
`[LJ-1.217]` (`agents/tasks/LJ-1-217/lj-1.217-report.md:103-105`) and by
`[LJ-1.134]` (`agents/tasks/LJ-1-134/lj-1.134-report.md:227`), so the figures
compare.**

**One correction to the baseline, and it makes the target's conclusion
stronger.** The 160 was never a price for `pairω`.
`agents/tasks/LJ-1-176/lj-1.176-report.md:227-229` states its own basis: "Row
5's 160 is a CHARGE AT A MEASURED COMPARABLE INSIDE THE SAME BLOCK, and it is
the one number in the table I did not measure." The comparable is row 1, the
composition of two injections (`:211-217`). **MEASURED: no line of `pairω` was
ever counted into the 160.** So the target refuted a figure that P-l already
classed as a hypothesis. The refutation is right. The word "over" is doing less
work than it appears to do, because there was no price to be over.

## 2. Q2. ARE THE FIVE INFERENCES SOUND? NO. THIS IS WHERE THE 700 FAILS

**MEASURED. Three of the eight rows have no basis sentence.** The target's basis
paragraph is `agents/tasks/LJ-1-226/lj-1.226-report.md:119-126`. I read it
whole. It covers exactly three rows: the addition adequacy, the multiplication,
and the carve. **It says nothing about the pairing formula (80 lines,
`:113`), the product set (50 lines, `:114`) or the L instantiation (60 lines,
`:116`).** That is **190 inferred lines with no stated basis.**

### 2.0 The table does not sum to its own total. MEASURED

I added the eight rows at `lj-1.226-report.md:109-116`:

```
36 + 47 + 130 + 220 + 80 + 50 + 120 + 60 = 743
```

**The row at `:117` reads "about 700".** The gap is 43 lines, which is 6
percent. **The measured part is 83, so the INFERRED part of the table is 660 and
not 617.** My own brief carries the 617 at `agents/tasks/LJ-1-231/LJ-1.231.md:16`,
and it got there by subtracting 83 from the rounded total instead of adding the
rows.

**This is small and it matters for one reason.** A total that is rounded DOWN
from its own rows makes the estimate look more conservative than it is. **The
figure the table actually asserts is 743.** Nothing in this report turns on the
43 lines, and every later paragraph is written against the rows and not against
the rounded total.

### 2.1 The 130 for addition adequacy: the basis does not determine the number

**MEASURED. The stated basis admits two readings and the number is neither.**
The row reads "same work again as the witness lemmas, both directions"
(`lj-1.226-report.md:111`). If "the witness lemmas" means Part 2, then both
directions give 94. If it means the whole measured anchor, both directions give
166. The number written is 130. **Neither reading produces it.**

**MEASURED. The stated basis mischaracterises one half of the work.** The probe
itself names the two obligations at `ProbeLJ1226A.agda:246-248`: `add-intro`
takes the ambient equation to the formula, and `add-elim` takes the formula
back. `add-intro` does re-run the witness lemmas. **`add-elim` does not.** It
quantifies over an ARBITRARY graph `F` that satisfies the four clauses, and it
must identify that graph's values with the numerals by single-valuedness. The
witness `addGraph` cannot appear in it. **So one of the two directions has no
comparable in the report at all, and it is the harder one.** That pushes the row
UP, not down.

**MEASURED. A delivered supplier cheapens the other half, and the report never
names it.** `src/L/Axioms/Numerals.lagda.md:207-212` delivers `numeralL-suc`, in
both directions: `z ∈ numeralL (suc n)` if and only if `z ∈ numeralL n` or
`z ≈ numeralL n`. `:203` delivers `numeralL-zero`. **That pair is exactly the
induction over a numeral's members that `closedAt` and `singleAt` need.** C-38
as extended: the hypothesis is discharged because something SUPPLIES it.

**MEASURED, and it is the sharpest fact in this section.** The probe IMPORTS
`numeralL-suc` at `ProbeLJ1226A.agda:149` and uses it ZERO times in the body at
`:175-317`. I counted the occurrences. The author imported the tool for the
adequacy and then priced the adequacy without it.

**MEASURED. The read-back half is cheap and the report over-charges it.** The
generic block of Part 2 measures 27 lines
(`ProbeLJ1226A.agda:254-262` and `:269-296`). Its elimination direction is the
same `subst` along the same equations, because `pair-spec`
(`src/V/Model.lagda.md:91`) and `union-spec` (`:96`) are PATHS between
propositions and not one-way implications. **So the read-back of the witness
device costs about 27 lines by a same-site argument, not 130.**

**Verdict on the 130: UNDERIVED. INFERRED.** One part is over-charged by a
same-site measurement. One part has a delivered supplier that was imported and
ignored. One part has no comparable at all and may exceed 130 by itself. The
sign of the total error is unknown.

### 2.2 The 220 for multiplication: the stated basis is contradicted by measurement, in both directions

**The question the brief asked: is multiplication really "addition with one more
existential layer"? NO. It is not that, and it is also not a second addition.**

**MEASURED. 27 of the addition's 47 witness lines are arithmetic-independent.**
I split Part 2 by whether a definition mentions addition:

| block | lines | mentions addition |
|---|---:|---|
| `numeral∈ωʟ`, `single`, `insert`, `x∈singleV`, `singleMem`, `insertMem`, `insertMono` | **27** | **no** |
| `addGraph`, `addGraphTop`, `addGraphBelow` | **20** | yes |

`single` and `insert` are set operations over `S`
(`ProbeLJ1226A.agda:258-262`). The four membership lemmas are about them and
about nothing else (`:269-296`). **A second graph reuses all 27 lines
verbatim.** So the multiplication row over-charges the witness half by at least
27 lines.

**The over-charge is larger than that. INFERRED, from the code's own shape.**
`addGraphTop` and `addGraphBelow` prove their results using only `singleMem`,
`insertMem`, `insertMono`, `+-zero` and `+-suc` (`:298-317`). A generic version
over any `f : ℕ → S` would carry both, and `addGraph` and `multGraph` would be
instances. That is DD4 applied inside the block.

**MEASURED, and it runs the other way.** Part 1's four clauses are written at
the FIXED type `Formula S 4` (`ProbeLJ1226A.agda:206`, `:210`, `:215`, `:228`).
Only `pairMem` and `pairMemc` are frame-generic (`:190`, `:197`). Multiplication
must embed the whole addition formula at a shifted frame, because its step
clause is `G(suc n) = G(n) + a` and not a single `sucAtL` atom. **So Part 1 needs
a frame-generic rewrite, and the phrase "one level higher" does not cover that
work.** The nearest measured comparable for a multi-case description is 133
lines (`agents/tasks/LJ-1-217/lj-1.217-report.md:112`), against `addFo`'s 36.

**Verdict on the 220: UNDERIVED. INFERRED.** The witness half is over-charged by
a measured 27 lines or more. The description half is under-charged by an
unmeasured rewrite. The two errors have opposite signs and neither is measured.
**The number is not established in either direction.**

### 2.3 The 120 for the carve: a different site, and it is above every measured comparable

**MEASURED. Three carve figures exist in this repository, and 120 exceeds all
three.**

| carve, four conjuncts plus readback | lines | source |
|---|---:|---|
| the inclusion, between two sets | 78 | `agents/tasks/LJ-1-176/lj-1.176-report.md:120` |
| the composition | 99 | `agents/tasks/LJ-1-152/lj-1.152-report.md:186` |
| the shift | 115 | `agents/tasks/LJ-1-217/lj-1.217-report.md:114` |
| `pairω`, as charged | **120** | `agents/tasks/LJ-1-226/lj-1.226-report.md:115` |

P-l binds all three comparables, because each is a different site. The target
cites only the third, and it takes a figure above the top of the range without
saying why.

**MEASURED. `[LJ-1.176]` recorded a reason this row may be SHARED rather than
owned, and the target never saw it.**
`agents/tasks/LJ-1-176/lj-1.176-report.md:271-277` says 78 of row 3's 112 lines
are the `Carve` body, which "rows 1, 4 and 5 do not each rewrite from nothing",
and that "if two of the remaining objects share one carve body the block falls
by about 78 lines". Section 4 of this report says why the target never saw that
paragraph.

### 2.4 The 80, the 50 and the 60: no basis at all

**MEASURED. The basis paragraph does not reach them**
(`lj-1.226-report.md:119-126`). Three observations, each INFERRED:

- **The product set at 50.** The literature the target itself cites gives the
  product outright as `F2(x, y) = x × y`
  (`dev/literature/rudimentary-functions.md:68`). Existence is cheap. 50 lines
  of Agda is an unrelated claim and no comparable supports it.
- **The L instantiation at 60.** The one measured comparable in this repository
  is 44 lines (`agents/tasks/LJ-1-217/lj-1.217-report.md:113`, Part 5, "the only
  site of `hasSeparationL`"). 60 exceeds it with no reason.
- **The pairing formula at 80.** The description comparables in this repository
  span 13 lines to 133 lines (`lj-1.176-report.md:118`,
  `lj-1.217-report.md:112`). An 80 inside a 10x range is a guess.

### 2.5 The robustness argument is one-sided

**MEASURED, by reading `lj-1.226-report.md:128-132`.** The target argues that
even if the inference is "generous by a factor of two, the row is over 300". It
never argues the other direction. **Nothing in the report guards the HIGH side**,
and section 2.1 shows the HIGH side is live, because `add-elim` has no
comparable anywhere in the tree. A hedge that protects only the conclusion the
brief asked for is not a hedge.

### 2.6 The band, derived from the repository's own measured comparables

**INFERRED. P-l binds every row of this table.** I take the CHEAPEST measured
instance of each component kind. This is a low end and not a price.

| component | lines | source and class |
|---|---:|---|
| addition description | 36 | **MEASURED**, `ProbeLJ1226A.agda:188-240` |
| addition witness | 47 | **MEASURED**, `:254-317` |
| addition adequacy, both directions | 27 | INFERRED, `lj-1.134-report.md:85-86` |
| multiplication description | 36 | INFERRED, addition restated at a frame |
| multiplication witness | 20 | INFERRED, the 27 generic lines reused |
| multiplication adequacy | 27 | INFERRED, as addition |
| pairing formula plus adequacy | 40 | INFERRED, 13 plus 27 |
| the product set | 0 | INFERRED, rud `F2` gives it |
| the carve plus readback | 78 | INFERRED, `lj-1.176-report.md:120` |
| L instantiation | 44 | INFERRED, `lj-1.217-report.md:113` |
| **low end** | **355** | **INFERRED, seven sites, P-l** |

**MEASURED: nothing on the record bounds row 5 above.** No source in
`dev/literature/` prices an object-language arithmetic. No probe in this tree
has written one. `add-elim` has no comparable. So the honest statement is a
half-open band: **not less than about 355, upper end open**, with 700 inside it
and unchosen.

**The cheapest next gate, if the orchestrator wants the band narrowed.** The
probe stopped one lemma short. `add-intro` and `add-elim` over the graph that is
already green would convert the whole 130-line row from INFERRED to MEASURED,
and it would settle the `add-elim` question that section 2.1 opens. That is the
widest unmeasured term inside row 5 (DD8).

## 3. Q3. DID THE BRIEF CAUSE THE OUTCOME? PARTLY, AND THE MEASURED HALF SURVIVES

**MEASURED. The brief is asymmetric, and the asymmetry is structural.**

**First, the framing is early and repeated.** `agents/tasks/LJ-1-226/LJ-1.226.md`
is 181 lines. It states the LOW expectation at `:19-20`, again at `:22`, and a
third time at `:30-33`. All three sit inside the first 18 percent of the file.
`:31-33` states the conclusion as a premise: "`pairω` is the single largest
INFERRED item with an explicit warning that it is low."

**Second, and this is the finding: the brief transmitted both LOW warnings and
dropped the HIGH one. MEASURED.** `[LJ-1.176]` gave three reasons its 547 may be
wrong, in one section. Two point low (`:252`, `:265`). One points high
(`:271-277`, the shared carve body worth about 78 lines).
**The brief carries the two low reasons verbatim at `:19-20` and omits the high
one.** A search of `LJ-1.226.md` for "too HIGH", "78" and "shared carve" returns
zero hits.

**Third, the abort criterion has no branch for the outcome it excluded.
MEASURED.** The five branches at `LJ-1.226.md:59-76` are: at or near 160,
materially OVER 160, walls, dissolves, column square free. **There is no branch
for "materially UNDER 160".** The overrun branch also pre-supplies its own
reading and its authority at `:64-66`. No branch offers an equivalent for an
underrun.

**Do the numbers stand independently of that framing? Split the answer.**

- **The 83 stands. MEASURED.** It is a line count of a green file. I re-counted
  it without reference to the brief and got the same figure. Framing cannot
  move it.
- **"Materially over 160" stands. MEASURED, plus one same-site step.** The
  object needs three arithmetic layers plus a carve
  (`lj-1.226-report.md:64-72`). The incomplete first half of layer one measures
  83. The remaining work cannot fall under 77 lines when layer one's description
  alone measures 36.
- **The 700 does NOT stand independently. INFERRED.** Five of its eight rows are
  the author's own inferences, written after three statements that the figure
  was low and with the countervailing warning removed. `[LJ-1.211]` measured
  briefs as the cause of 8 of 10 overturns on record.

**So the classification is UPHELD BUT UNQUANTIFIED, with the cause partly the
brief.** The conclusion is not the brief's product. The magnitude is.

## 4. Q4. IS THERE A CHEAPER SHAPE? THE QUESTION IS LIVE AND THE REPORT NEVER ASKED IT

**MEASURED. Neither consumer names a particular function.**

- `src/L/Ordinal/SquareLaw.lagda.md:685-687` defines
  `sq α = Σ[ f ∈ (⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫) ] (f injective)`. It is an existential
  over injections.
- `src/L/StageCardinal.lagda.md:15-19` takes its pairing as a module PARAMETER
  of the same Σ shape. `src/L/BoundedSubset.lagda.md:1388-1390` passes it
  through unchanged.

**So the obligation is "an injection", not "`Count.pair`".** The consumer never
sees which function it received. **MEASURED, at both sites.**

**MEASURED. The target treats `Count.pair` as the target and never asks whether
another injection is cheaper to describe.** It copies `[LJ-1.156]`'s
`NumeralPresentation` verbatim as Part 0 (`ProbeLJ1226A.agda:80-127`) and then
derives the whole arithmetic requirement from
`Count.pair a b = (a + b) · (a + b) + a` (`src/FOL/Count.lagda.md:29-30`).
The requirement is real GIVEN that choice. The choice is not examined.

**MEASURED. The retired route obtained the pairing at `ω` with NO arithmetic.**
`archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:815` is a section
headed "The base at `ω`". `:831-893` is `module CoreAtω`, and it closes the base
through the order core in about 79 lines. Its prose at `:821-825` says the two
hypotheses about infinite members are vacuous at `ω`. **Zero arithmetic
formulas. Zero `Count.pair`.**

**MEASURED. The current tree keeps the collapse and drops `ω`.**
`src/L/Ordinal/SquareLaw.lagda.md:146` opens the collapse module on `(α : S)
(oα : IsOrd α)` and nothing else. `col` is built at `:384` and its four
properties follow. **`ω` satisfies that hypothesis.** The exclusion of `ω`
happens later, in `Init` (`:692-698`), which demands `ω ∈ α`.

**What this does NOT show, and I will not claim it.** `CoreAtω` is AMBIENT. It
builds `sq ω` in the hierarchy, which is the layer the target correctly books as
"the base, not the charge". It is not an L-internalization, so it is not a price
for row 5. P-l.

**What it does show. INFERRED, and it is a shape and not a number.** The pairing
at `ω` is obtainable by ORDER rather than by ARITHMETIC. The order on the
numerals is membership, and `∈̇` is a delivered atom. A description of the
collapse of the square order would use `∈̇`, `prAtL`, `svAt`, `domAt` and
`injAt`. Every one of those is delivered or sits in a tracked probe. **No
addition, no multiplication, and no finite-graph iteration device.**

**The counter-evidence, and it is real.**
`agents/tasks/archive/L3-32-T85/l3.32-t85-report.md:110` records that a
counting route through `FOL.Count` was ruled against on generality, and that the
order core at `ω` walled once at check time. **So the order route is not a free
win. It is an unpriced alternative, which is a different thing.**

**The verdict on Q4: the report answered a question the brief did not ask, and
skipped the one it did.** `LJ-1.226.md:71-74` offered "THE OBJECT IS NOT NEEDED"
and the object IS needed. It offered no branch for "the object is needed in a
cheaper shape", which is where the evidence points. The target's own ARCHIVE
section found the retired route and drew the narrower conclusion: "nothing
transfers as a number" (`lj-1.226-report.md:220-222`). **That is correct about
numbers and it is silent about shape, and the brief had asked for SHAPE**
(`LJ-1.226.md:131-134`).

## 5. WHICH PARTS OF SECTION 6 SURVIVE THE FILE MOVE

The target's section 6 is `lj-1.226-report.md:170-182`. It makes three claims. I
checked each.

**Claim 1: "`src/ProbeLJ1134A.agda` no longer exists". MEASURED TRUE as a
path.** `ls` returns no such file. The claim is true about the path and false
about the file.

**Claim 2: "the readback device is GONE from the tree". MEASURED FALSE.** The
file is at `agents/tasks/LJ-1-134/ProbeLJ1134A.agda`. `git ls-files` lists it as
TRACKED. It is 207 non-blank non-comment lines, which matches its own report's
total (`agents/tasks/LJ-1-134/lj-1.134-report.md:227`). The word "GONE" is
wrong.

**Claim 3: "a grep for `injAt` / `module Small` over `src/L/` returns nothing".
MEASURED TRUE.** I ran `grep -rn "injAt\|module Small" src/` over all of `src/`
and not only `src/L/`. Zero hits. This agrees with `[LJ-1.227]`'s independent
measurement.

**So the surviving finding is narrower and still real: the readback device is in
no DELIVERED master.** A probe is not a master, and nothing typechecks a probe
after its task closes. The consequence the target drew survives in its second
form only. "Re-delivered" is right. **"Re-derived" is wrong**, because 207 green
lines exist to deliver from.

**Does anything else lean on the false half? YES, and it pushes the 700 UP.**
The 120-line carve row bundles the readback (`:115`). Section 11 says the device
"must be re-delivered first, whichever way the ruling goes" (`:269-270`). Both
sentences are written against a device believed absent. Corrected, both get
CHEAPER. **So the false premise inflated the estimate. INFERRED, and the
direction is certain even though the size is not.**

**The larger cost of the move, and it is not in section 6 at all. MEASURED.**
The author concluded the probe was gone and did not read
`agents/tasks/LJ-1-134/lj-1.134-report.md`. That report holds the closest
measured comparable in this repository for the work the 130-line row prices. At
`:80-86` it records `injAt` with `injAt-out` and `injAt-in`, a NEW
object-language predicate with BOTH adequacy directions, at **27 non-comment
lines**. **The report priced that kind of work at 130 while a measured 27 sat in
a file it believed was deleted.** The two are not the same work, because
`addFo`'s adequacy carries an induction that `injAt`'s does not. But 27 is the
comparable the author should have had, and the move removed it.

## 6. C-42 IN BOTH DIRECTIONS

**DOES THE 700 REACH FURTHER THAN `pairω`? NO, not by the arithmetic cause.
MEASURED, from the target's own text and from the delivered tree.**

The target names the disease correctly at `lj-1.226-report.md:74-80`: rows 1, 3
and 4 have value clauses that are one or two delivered atoms, and `pairω`'s
value clause is a RECURSION. **The column square is a COMPOSITION and not a
recursion.** `agents/tasks/LJ-1-156/ProbeLJ1156A.agda:493-494` gives it as
`pair (x , y) = j (sqκ .fst (α↪κ .fst x , α↪κ .fst y))`, three injections
composed. `[LJ-1.176]` priced it at 99 from `[LJ-1.152]`'s measured
second-composition cost (`lj-1.176-report.md:221-225`).

**So the brief's worry is INFERRED FALSE: row 4 does not inflate for `pairω`'s
reason.** Row 4 shares `pairω`'s OTHER exposures, which are the carve band and
the readback device, and `[LJ-1.176]`'s own shared-carve paragraph
(`:271-277`) would move row 4 DOWN rather than up.

**DOES THE 700 REACH LESS FAR THAN `pairω`? YES, DECISIVELY. MEASURED.** It
prices the internalization of ONE function. Both consumers are Σ-types that name
no function (`SquareLaw.lagda.md:685-687`, `StageCardinal.lagda.md:15-19`).
**The 700 is the price of a witness choice, not the price of row 5.**

## 7. DD4: WHERE DOES `pairω` FALL?

**The content is tower-neutral. I agree with the target, with one narrowing.**

**MEASURED. The target's grep tests a narrower claim than the conclusion it
draws.** `lj-1.226-report.md:150-156` checks for `hasSeparationL`,
`hasReplacementL`, `stage`, `LsetS`, `boundingOrd`, `IsOrd` and L stages. I
re-ran that check over `:175-317` and confirm zero hits for all of them. **But
that grep tests "does this touch L's stage machinery", not "is this
tower-neutral".**

**MEASURED. The probe as written is L-specific.** Over `:175-317` the body names
`numeralL` 16 times, `prʟ` 13 times, `pairʟ` 7 times, `ωʟ` 3 times and `unionʟ`
3 times. The target concedes the point when it says the object "should be
written generic from the first line" (`:161-163`).

**So the halving is AVAILABLE and UNPAID, and the generification is itself
unpriced.** `[LJ-1.217]` measured its own block at 85 percent generic, 252 of
296 lines (`lj-1.217-report.md:183-186`). That is a comparable for what
generification yields elsewhere, and P-l says it is not a price here.

**The statement names no tower**, so if the lines are shared the J tower pays
them once. That halves their weight in a route decision, and it applies to
whatever the true figure is.

## 8. TWO ERRORS IN THE BRIEF I WAS GIVEN

DD25 says a review reports what it finds. I found two false premises in
`agents/tasks/LJ-1-231/LJ-1.231.md`, both attributions.

**1. MEASURED FALSE. `[LJ-1.227]` did not measure the column square at 99 and
did not warn it "may be too low as well".** My brief says so at `:84-85` and
lists it in ARCHIVE at `:140-141`. A search of
`agents/tasks/LJ-1-227/lj-1.227-report.md` returns zero hits for "too low" and
no 99 outside a file path. **Both the 99 and the warning belong to
`[LJ-1.176]`**, at `:205` and `:265-269`.

**2. MEASURED FALSE. `[LJ-1.227]` did not split A5's siblings by tower.** My
brief says so at `:125-128`. The tower table at
`agents/tasks/LJ-1-227/lj-1.227-report.md:241-247` covers A1, A2, A3, A4 and A7.
**A5 and A6 are absent from it.** The DD4 premise I was given does not exist in
the source it names.

**3. MEASURED WRONG BY ARITHMETIC. The brief's "617 are INFERRED"
(`LJ-1.231.md:16`) should be 660.** Section 2.0 gives the addition. The brief
subtracted 83 from the target's rounded total instead of adding the target's
rows.

**A fourth error is inherited, not caused here. MEASURED.**
`agents/tasks/LJ-1-156/ProbeLJ1156A.agda:496-497` is `pair-inj`, not `pair`. The
definition is at `:493-494`. `[LJ-1.176]` made the error at `:224`, my brief
propagated it at `LJ-1.226.md:126` and again at `LJ-1.231.md`, and the target
repeated it at `lj-1.226-report.md:213-214`. The quoted TEXT is correct
everywhere. Only the line reference is wrong.

## 9. WHAT I AGREE WITH, AND A REVIEW THAT AGREES IS A RESULT

- **The 36 and the 47 are exact.** I re-counted both.
- **The probe is green.** The interface file exists.
- **Part 0's exclusion is correct.** A5 counts each object once.
- **"Materially over 160" is right**, and it is more right than the target
  argued, because 160 was never a price.
- **The arithmetic really is absent from this tree.** I re-ran the grep for
  `addAt|plusAt|multAt|timesAt|sumAt|prodAt|arithAt` over `src/`. Zero hits.
  The only arithmetic-shaped delivered atom is `sucAtL`
  (`src/L/Coding/Model.lagda.md:1395`).
- **The literature reading is correct.** `rudimentary-functions.md:68` settles
  the product's existence and says nothing about size. Section 11 confirms it.
- **The tower-neutral CONTENT claim is right**, with section 7's narrowing.
- **The report marks its own total INFERRED and says it did not finish the
  build** (`lj-1.226-report.md:28-32`). It did not overstate its class. **The
  defect is in the derivation, not in the honesty.**

**One claim I mark down without overturning. INFERRED.** "The seconds are not
the problem; the lines are" (`:145-146`). The probe never elaborated the
expensive content. **MEASURED: `hasSeparationL` is imported at
`ProbeLJ1226A.agda:147` and used ZERO times in the body.** No separation and no
carve was elaborated. The 1.69 s covers 43 lines of imports, 77 ambient lines
and 83 charge lines. The seconds claim is INFERRED, not MEASURED, and the
target concedes the carve was never reached (`:142`).

## 10. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-226/lj-1.226-report.md`, read WHOLE.** TAKEN: the eight
  rows at `:107-117`, the basis paragraph at `:119-126`, the robustness
  argument at `:128-132`, section 6 at `:170-182`, and the DD4 grep at
  `:150-156`.
- **`agents/tasks/LJ-1-226/ProbeLJ1226A.agda`, read WHOLE, 317 lines.** TAKEN:
  the fixed-frame clauses at `:206`, `:210`, `:215`, `:228`; the frame-generic
  helpers at `:190`, `:197`; the unused import at `:149`; the adequacy header
  at `:246-248`; the generic and addition-specific split at `:254-296` against
  `:264-267` and `:298-317`. **I read the probe, not the report's account of
  it.**
- **`agents/tasks/LJ-1-176/lj-1.176-report.md`.** TAKEN: the A5 table at
  `:199-207`; row 5's own basis at `:227-229`; the two LOW warnings at `:252`
  and `:265-269`; **the HIGH warning at `:271-277`, which is the Q3 finding**;
  the carve at 78 lines at `:120`; the description at 13 lines at `:118`.
- **`agents/tasks/LJ-1-217/lj-1.217-report.md`.** TAKEN: the per-part table at
  `:107-117`, giving the 133-line description at `:112`, the 115-line carve at
  `:114` and the 44-line instantiation at `:113`; the 85 percent generic figure
  at `:183-186`.
- **`agents/tasks/LJ-1-227/lj-1.227-report.md`.** TAKEN: the tower table at
  `:241-247`. **NOT TAKEN, because it is not there: the 99 and the "too low"
  warning.** Section 8.
- **`agents/tasks/LJ-1-156/lj-1.156-report.md` and `ProbeLJ1156A.agda`.** TAKEN:
  the `CSB` dissolution at `:3-8` and `:38-40`; `NumeralPresentation` at 37
  lines at `:245`; `pairω` at `ProbeLJ1156A.agda:149-150`; **`sqω : SQ.sq ω`
  green at `:522-523`**; the column square at `:493-494`.
- **`agents/tasks/LJ-1-152/lj-1.152-report.md`.** TAKEN: the 99-line carve at
  `:186`; the 2,500 to 1 ratio at `:32-35`, which is a SECONDS ratio and not a
  lines ratio; the refusal to multiply at `:231-241`. **WHAT WOULD NOT
  TRANSFER: the 2,500 to 1, because it prices seconds and row 5's problem is
  lines.**
- **`agents/tasks/LJ-1-134/ProbeLJ1134A.agda` and `lj-1.134-report.md`.**
  TAKEN: the file is tracked and 207 lines; `injAt` at `:61-65`; `injAt-in` at
  `:90-93`; `module Extract` at `:99-101`; `module Small` at `:299-304`;
  **the 27-line measured comparable at `lj-1.134-report.md:85-86`**. Section 5.
- **`archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md`.** TAKEN,
  **SHAPE ONLY**: "The base at `ω`" at `:815`, `module CoreAtω` at `:831-893`,
  and the vacuity prose at `:821-825`. **WHAT WOULD NOT TRANSFER: every line
  count and every second**, because the retired tree is not this tree, and
  because `CoreAtω` is ambient where row 5 is an internalization. P-l.
- **`agents/tasks/archive/L3-32-T85/l3.32-t85-report.md:110`.** TAKEN: the
  counting route was ruled against on generality, and the order core at `ω`
  walled once. **This is the counter-evidence to my own Q4 finding and I record
  it beside the finding.**
- **Delivered masters read for the consumer question:**
  `src/L/Ordinal/SquareLaw.lagda.md:146`, `:384`, `:685-687`, `:692-698`;
  `src/L/StageCardinal.lagda.md:15-19`; `src/L/BoundedSubset.lagda.md:1388-1397`;
  `src/L/Axioms/Numerals.lagda.md:203`, `:207-212`; `src/V/Model.lagda.md:91`,
  `:96`; `src/FOL/Count.lagda.md:29-30`.

## 11. LITERATURE USED (DD18)

- **`dev/literature/rudimentary-functions.md:68`. TAKEN, and the target read it
  correctly.** The line is `F2(x, y) = x × y`, one item of a verbatim 16-item
  basis list from Schindler and Zeman. **It settles the PRODUCT's EXISTENCE and
  it settles NOTHING about size.** It carries no line count, no page count and
  no effort figure. **MEASURED ZERO HITS in that whole file for "Gödel
  pairing", "pairing function" and any arithmetic on numerals**; its one use of
  the word "arithmetic" at `:19` is a paper title.
- **`dev/literature/devlin-II5.md:387-389`. TAKEN, with a caution.** It says the
  per-tower content is exactly two objects, the level-hood certificate and the
  definable well-order. `pairω` is neither, so the target's DD4 reading is
  sound. **The caution: that table classifies the CONDENSATION steps 5.1 to
  5.6, not A5's object list.** Using it to place `pairω` transfers across
  taxonomies. It is a reasonable reading and it is not a measurement.
- **Does any source price an object-language arithmetic? NO. MEASURED ZERO HITS
  across all of `dev/literature/`.** The only itemised size list in the corpus
  is Paulson's Isabelle development at
  `dev/literature/formalizations.md:93-97`, and none of its five items is an
  arithmetic. **WHY NOT USED: it prices whole chapters of a different system in
  tokens, so it cannot bound a row of this tree.**
- **`dev/literature/j-hierarchy.md:147-149`. READ, NOT USED as a price.** It
  records that an ordinal closed under the Gödel pairing has order type equal to
  itself. **WHY NOT USED: it is the order-type route's mathematics and it
  carries no size**, so it supports Q4's shape and prices nothing.

## 12. THE NEGATIVES, EACH CLASSIFIED

- **MEASURED. The anchor is real and the 36 and the 47 are exact.** I recounted
  both. The interface file exists.
- **MEASURED. Part 0's figure is one line out**, 77 against 76, in a row that is
  excluded from the charge.
- **MEASURED. 190 inferred lines carry no basis sentence.** The basis
  paragraph at `lj-1.226-report.md:119-126` reaches three rows of eight.
- **MEASURED. The eight rows sum to 743 and the total is written "about 700".**
  The inferred part of the table is 660, not 617.
- **MEASURED. The 130's stated basis admits 94 or 166 and not 130.**
- **MEASURED. `add-elim` is not the witness lemmas mirrored.** It quantifies
  over an arbitrary graph. It has no comparable in the report or in the tree.
- **MEASURED. `numeralL-suc` is delivered, both directions, and the probe
  imports it and uses it zero times.**
- **MEASURED. 27 of the addition's 47 witness lines are
  arithmetic-independent**, so the 220 over-charges the witness half.
- **MEASURED. Part 1's clauses are fixed-frame**, so multiplication needs a
  rewrite that "one level higher" does not cover. The 220 is wrong in both
  directions and measured in neither.
- **MEASURED. The 120 exceeds all three measured carve figures**, which are 78,
  99 and 115.
- **MEASURED. The brief dropped `[LJ-1.176]`'s "may be too HIGH" paragraph** and
  carried both LOW warnings.
- **MEASURED. The brief's abort criterion has no branch for "under 160".**
- **MEASURED. Neither consumer names a particular pairing function.** Both are
  Σ-types over injections.
- **MEASURED. The retired route closed the base at `ω` with no arithmetic**, in
  about 79 ambient lines.
- **MEASURED. "The readback device is GONE" is FALSE.** The file is tracked at
  `agents/tasks/LJ-1-134/ProbeLJ1134A.agda`, 207 lines.
- **MEASURED. "`injAt` and `module Small` are in no master under `src/`" is
  TRUE.** Zero hits over all of `src/`.
- **MEASURED. The file move cost the report a 27-line comparable** that sat in
  the report of the probe it believed was deleted.
- **MEASURED. Row 4 does not inflate for `pairω`'s reason.** It is a
  composition, not a recursion.
- **MEASURED. My own brief misattributes the 99, the "too low" warning and the
  A5 tower split to `[LJ-1.227]`.** All three belong elsewhere or do not exist.
- **INFERRED. The low end of the band is about 355**, from seven measured
  comparables at seven sites. P-l binds it.
- **MEASURED. Nothing on the record bounds row 5 above.**
- **NOT MEASURED. Whether the order-type shape is cheaper in L.** I did not
  price it and I will not guess it.
- **NOT MEASURED. The seconds of any adequacy proof or any carve at this site.**
  The probe reached neither.

## 13. WORKING TREE, AS THIS REPORT DESCRIBES IT

One new file, and nothing else changed:

| file | state |
|---|---|
| `agents/tasks/LJ-1-231/lj-1.231-report.md` | this file |

No Agda ran. No master, brief or other report was edited. No file was created
under `src/`. No commit, no push, no `git checkout .`, no stash, no reset, no
clean. No `make check`. I did not touch `agents/tasks/LJ-1-229/` or
`agents/tasks/LJ-1-230/`.

**Checks run:** `scripts/lint-prose.py --check` on this report.
