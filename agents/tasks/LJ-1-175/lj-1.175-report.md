# LJ-1.175 report: sum Route A-prime to ONE total

tier: opus (version `override`). Recon only. No Agda ran. No master, brief or
report was edited. No commit, no push.

Every claim is marked **MEASURED** (read at the cited line, or a machine result
somebody else recorded) or **INFERRED** (my composition or judgement).

## 0. VERDICT: **BLOCKED, AND NAMED. THE BLOCKER IS A5.**

**Route A-prime has no total, because block A5 has no live line price, and
every figure ever written for A5 is superseded or refused.**

**The partial sum is 705 lines over six blocks** (`[LJ-1.136]`,
`agents/tasks/LJ-1-136/lj-1.136-report.md:92`). That figure is live. A5 adds an
unknown to it.

**A second result, and the brief's third abort branch also fires. THE SEVEN
BLOCKS DO NOT PARTITION.** Five overlaps are MEASURED in the reports' own text.
Two of the six priced blocks draw their line basis from steps of the same probe
whose WHOLE file is A5's original basis. One block, A6, states its price as a
number PLUS an open charge that belongs to A5. **So even after A5 is priced,
adding the seven cells is not the total.** Section 3.

**What dissolved yesterday was a COUNT, not a price.** `[LJ-1.156]` measured
that A5 carries ZERO `hasReplacementL`
(`agents/tasks/LJ-1-156/lj-1.156-report.md:286-288`). That is a real result and
it removes A5's largest risk. **It is not a line figure**, and `[LJ-1.156]`
says so itself: its probe is the AMBIENT chain and "it does not build a single
L-element" (`:640-643`).

## 1. THE BLOCK TABLE

Caliber: non-blank lines inside ` ```agda ` fences for masters, and non-blank
non-comment lines for `.agda` probe files. `scripts/ledger.py` cannot count a
probe and says so at `scripts/ledger.py:13-15`.

| block | live lines | seconds | basis, at `file:line` | superseded by |
|---|---:|---|---|---|
| **A1** `⟨ isL x ⟩` replaces "assume V = L" | **40** | none | READING of three delivered sites. `agents/tasks/LJ-1-136/lj-1.136-report.md:84` | nothing |
| **A2** injection as an L element, read back | **170** | 2.51 s upper bound for the 207-line probe | `[LJ-1.134]` MEASURED 78 lines for the core, plus reading for two unpriced pieces. `agents/tasks/LJ-1-134/lj-1.134-report.md:229-233`, `:30-34`; carried at `lj-1.136-report.md:85` | nothing |
| **A3** the `<_L`-least injection | **45** | inside A2's 2.51 s | `[LJ-1.134]` Part B MEASURED at 22 lines. `agents/tasks/LJ-1-134/lj-1.134-report.md:224`, `:235-239`; carried at `lj-1.136-report.md:86` | nothing |
| **A4** internal least cardinal, internal `IsCardinal` | **190** | see section 4 | READING. `[LJ-1.107]`'s ambient `LeastCard` is 38 lines at 91.98 s, `agents/tasks/LJ-1-107/lj-1.107-report.md:52`; carried at `lj-1.136-report.md:87` | its SECONDS basis is superseded by `[LJ-1.159]` |
| **A5** the square-law chain over L-injections | **NO LIVE PRICE** | see section 4 | every figure superseded or refused. Section 2 | `[LJ-1.136]`, then `[LJ-1.152]`, `[LJ-1.154]`, `[LJ-1.156]` |
| **A6** `absorbs` as a theorem | **150 PLUS an open charge** | 2.83 s ambient | `[LJ-1.107]` measured `ShiftAbs`+`Shiftω` at 103 lines and 2.83 s, `agents/tasks/LJ-1-107/lj-1.107-report.md:53`; carried at `lj-1.136-report.md:89` | the open charge is A5's, and A5 is unpriced |
| **A7** the internal GCH statement | **110** | none | READING. `ChoiceStatement` is 13 in-fence lines at `src/L/Choice/Transversal.lagda.md:372-384`; carried at `lj-1.136-report.md:90` | nothing |

**The sum of the six priced cells is 705.** MEASURED as arithmetic:
40+170+45+190+150+110 = 705, and `[LJ-1.136]` states the same figure at
`agents/tasks/LJ-1-136/lj-1.136-report.md:92`.

**The sum of the cells that are ONE unqualified number is 555**, which is A1,
A2, A3, A4 and A7. A6's cell is a number plus an open charge, so it is not one
number.

### 1.1 How much of the 705 rests on an elaboration in this setting

**MEASURED: 100 lines of the 705, which is 14 percent.** Only A2 and A3 carry a
measured core, and both come from one probe run: 78 lines and 22 lines
(`agents/tasks/LJ-1-134/lj-1.134-report.md:219-227`).

**The other 605 lines rest on READING delivered comparables**, and
`[LJ-1.136]:297-305` states that method openly per block. Under DD8 the basis
word for those five blocks is **comparable**, not **probe**.

**P-l applies to all 605.** A figure anchored on a comparable is a hypothesis,
not a price. I do not convert any of them, and I do not discount them either.
They are the best figures on disk.

## 2. WHY A5 HAS NO LIVE PRICE. MEASURED, by exhaustive search

**The search, so the negative is MEASURED and not INFERRED.** I ran
`grep -rn "A5" agents/tasks/*/lj-*.md` and filtered for a line figure, over all
88 live task directories. **I also ran `grep -rn "\bA5\b"
agents/tasks/archive/` over all 496 archived task directories, and it returns
ZERO hits**, because the seven-block split postdates the archive. `agents/`
holds only `agents/tasks/`, so those two searches cover the corpus.

**The search returns exactly two line figures for A5.** Both are dead.

| A5 figure | source | why it is not live |
|---|---|---|
| **300 to 450** | `agents/tasks/LJ-1-131/lj-1.131-report.md:371` | **SUPERSEDED.** `[LJ-1.136]` measured the stated basis FALSE: the qualifier "455 closed unconditionally" is refuted at `agents/tasks/LJ-1-107/ProbeLJ1107A.agda:630`, where the injection is a MODULE PARAMETER. `agents/tasks/LJ-1-136/lj-1.136-report.md:32-53` |
| **about 590 (INFERRED)** | `agents/tasks/LJ-1-136/lj-1.136-report.md:88`, `:1112-1119` | **BOTH FACTORS REFUTED.** It is 98 lines times six write directions. `[LJ-1.152]` refuted the COUNT: composition carves and is not a replacement, 2.50 s. `[LJ-1.154]` refuted the UNIT: the identity graph carves at 1.73 s against 254.22 s, at the exact file the 98 came from. `agents/tasks/LJ-1-154/lj-1.154-report.md:277-282` |

**And three later tasks each REFUSED to write a replacement figure, in those
words.**

- `[LJ-1.152]`: refused to multiply 2.50 by five
  (`agents/tasks/LJ-1-154/lj-1.154-report.md:296-297` records the refusal).
- `[LJ-1.154]`: "**A5's seconds are UNPRICED. I will not multiply 1.73 by
  five.**" (`agents/tasks/LJ-1-154/lj-1.154-report.md:307`). Its section title
  is "A5 RE-PRICED, and it is UNPRICED rather than priced low" (`:268`).
- `[LJ-1.156]`: "**I will NOT add the L-side seconds to that figure by
  multiplication**" (`agents/tasks/LJ-1-156/lj-1.156-report.md:294-297`).

**All three refusals cite P-l.** They are correct refusals. I do not overturn
them, and I will not manufacture the number they declined to write.

### 2.1 What `[LJ-1.156]` DID settle, stated exactly

**A5 carries ZERO `hasReplacementL`, MEASURED at the chain level**
(`agents/tasks/LJ-1-156/lj-1.156-report.md:13-15`, `:286-288`). The chain
elaborates `--safe`, exit 0, with no `CSB`, no `≃` and no
`Cubical.Foundations.Equiv` import (`:432-436`).

**That is a COUNT, and the report says so: "That is a count, not an estimate"**
(`:287`). A count of replacements is not a count of lines.

**What `[LJ-1.156]` explicitly did NOT do.** Its own section 14 lists it:
"`ProbeLJ1156A.agda` is the AMBIENT chain. ... **It does not build a single
L-element**" (`:640-642`). **A5 is the chain over L-injections. The L-side of
A5 remains unmeasured**, and `[LJ-1.156]` hands it back to `[LJ-1.152]` and
`[LJ-1.154]`, which both refused to price it.

### 2.2 The four objects nobody has measured

`[LJ-1.156]:270-282` and `[LJ-1.154]:288-296` carry the same six-object table.
Two rows are MEASURED. **Four rows are INFERRED and both reports say so.**

| built object | class |
|---|---|
| composition of two injections | **MEASURED**, carves, 2.50 s, `[LJ-1.152]` |
| the identity graph | **MEASURED**, carves, 1.73 s, `[LJ-1.154]` |
| `ShiftAbs` / `Shiftω` | **INFERRED** that it carves |
| the inclusion `j` | **INFERRED** that it carves |
| `pairω`, the pairing on ω | **INFERRED** that it carves |
| the column square `pair` | **INFERRED** that it carves |

**None of the six has a LINE price for its L-side form.** `[LJ-1.154]`
measured 176 lines for the whole identity-graph file, of which 77 are the
generic `Carve` and 17 are the L instantiation
(`agents/tasks/LJ-1-154/lj-1.154-report.md:185-193`). **Turning that into a
per-object line charge is exactly the analogy P-l forbids**, and it is why I
report a blocker instead of a total.

## 3. THE BLOCKS DO NOT PARTITION. FIVE OVERLAPS, ALL MEASURED

The brief's third abort branch fires. Each row below is read from the reports'
own words, not composed by me.

| # | overlap | evidence |
|---|---|---|
| 1 | **A6's price NAMES A5.** A6 is "150 plus A5's per-construction charge" | `agents/tasks/LJ-1-136/lj-1.136-report.md:89`, and `:304`: "the block then inherits one instance of A5's open per-construction charge" |
| 2 | **A5's own object list CONTAINS A6's object.** Row 3 of A5's six built objects is `ShiftAbs` / `Shiftω`, which is A6's whole content | `agents/tasks/LJ-1-136/lj-1.136-report.md:211` against `:89` |
| 3 | **A4's extra content IS A2's content.** "The internal form's extra content is A2's predicate under a `⋁`, which A2 measures" | `agents/tasks/LJ-1-136/lj-1.136-report.md:302`, and `:87`: "it needs A2's predicate inside the least-of" |
| 4 | **A4's and A6's line bases are STEPS of the probe whose WHOLE is A5's basis.** `LeastCard` is 38 lines as step 2; `ShiftAbs`+`Shiftω` is 103 lines as step 3; the whole probe is 582 lines, and 582 is A5's stated basis | `agents/tasks/LJ-1-107/lj-1.107-report.md:52`, `:53`, `:57` against `agents/tasks/LJ-1-131/lj-1.131-report.md:371` |
| 5 | **A 300-line item sits UNDIVIDED across A4 and A5.** "That is why A-prime costs about 300 lines more than A, and the figure is in block A4 and A5" | `agents/tasks/LJ-1-131/lj-1.131-report.md:464-465` |

**AND THE BLOCK A5 CHANGED CONTENT BETWEEN TASKS. MEASURED.**
`[LJ-1.131]:371` defines A5 as the ambient chain **restated** over
L-injections, priced against 582 ambient lines. `[LJ-1.136]:203-215` redefines
A5 as **six objects BUILT into L**, priced against 98 lines per write
direction. **`[LJ-1.136]` says the first definition is wrong: "no master holds
the chain to restate"** (`:222-223`).

**So the label A5 covers two different bodies of work in two reports, and the
sum inherits whichever one the reader assumes.** That is the finding the brief
said was worth more than a number, and I agree with the brief.

**One consequence the orchestrator should note. The 705 is a sum of cells that
were written by one author in one table** (`[LJ-1.136]`). It is internally
consistent as arithmetic. **It is not a partition of the work**, so it is a
lower bound on A1 to A7 minus A5 only if the overlaps are net-positive, and
nobody has measured that.

## 4. THE SECONDS, AND THE BAR MOVED UNDER THEM

**A5's seconds are the best-measured thing about A5, and they are ambient, not
L-side.**

| what | seconds | lines | s per line | source |
|---|---:|---:|---:|---|
| the ambient chain, as written | **133.00** | 393 | 0.3393 | `agents/tasks/LJ-1-156/lj-1.156-report.md:187-189` |
| `LeastCardInj` alone, inside it | **100.64** | 44 | 2.26 | `agents/tasks/LJ-1-156/lj-1.156-report.md:208`, `:330` |
| **the ambient chain, CURED** | **46.15** | 405 | **0.1140** | `agents/tasks/LJ-1-159/lj-1.159-report.md:348`, `:372-375` |
| the identity graph, by separation | 1.73 | 176 | 0.0098 | `agents/tasks/LJ-1-154/lj-1.154-report.md:161` |
| composition of two injections | 2.50 | n/a | n/a | `agents/tasks/LJ-1-152/lj-1.152-report.md:134`, `:171`, three kept runs |

**`[LJ-1.159]` cured 86.85 s for 13 lines**, and it is a consumer-checked
result: Parts 3 to 7 of the chain are byte for byte identical and the file is
`--safe`, exit 0 (`agents/tasks/LJ-1-159/lj-1.159-report.md:340-350`). **The
module saving and the chain saving agree inside 2.2 percent** (`:359-362`).

### 4.1 A STALE BAR, and it is a `[LJ-1.168]`-class trap

**MEASURED: `[LJ-1.136]`'s seconds verdict is quoted against a bar the ledger
has since replaced.**

`[LJ-1.136]:1081` cites `ac_baseline_module_rate = 0.014367` at
`dev/ledger.toml:2685` and reports A-prime at "168x to 181x" that bar.
**`dev/ledger.toml:2730` now reads `ac_baseline_module_rate = 0.009143` over
17,197 lines**, re-measured 2026-08-13 on the cured tree, and the ledger's own
comment says the figure fell 22.7 percent (`dev/ledger.toml:2712-2727`).

**So any ratio carried forward from `[LJ-1.136]` understates the gap.** It does
not change that report's conclusion, and `[LJ-1.136]` itself predicted this
("the conclusion does not change and the number does", `:1096-1098`).

**And TWO bars are in live use across these reports, differing by 1.16 times.**
`[LJ-1.136]` uses the module rate; `[LJ-1.156]:302` and `[LJ-1.159]:375` use
DD24's ratio bar of **0.007913** (`dev/PLAN.md:138`). **Both are live figures
with different denominators.** Against 0.009143 the cured chain is **12.5
times** the bar; against 0.007913 it is 14.4 times. **Nobody has ruled which
bar prices a NEW module in this route**, and the two answers differ enough to
matter.

## 5. THE GENERIC COLUMN (DD4)

**The brief asked how much of Route A-prime re-instantiates at the J tower.
MEASURED: the column exists for A5's parts alone. It does not exist for any
other block.**

| block | generic lines | of | source |
|---|---:|---:|---|
| **A5**, the ambient chain | **393 of 393**, generic in the ORDINAL, NOT in the carrier | 393 | `agents/tasks/LJ-1-156/lj-1.156-report.md:472-491` |
| **A5**, the carve device | **90 of 176** carry no L axiom and no L stage | 176 | `agents/tasks/LJ-1-154/lj-1.154-report.md:334-350` |
| **A5**, `LeastCardAt` after the cure | generic in the ambient ordinal, and **8.4 times CHEAPER** than the fixed form | 97 | `agents/tasks/LJ-1-159/lj-1.159-report.md:318-327` |
| A1, A2, A3, A4, A6, A7 | **NO FIGURE EXISTS** | | section 5.2 |

### 5.1 The three DD4 results that are real

1. **`[LJ-1.156]` MEASURED by one grep that no line of the chain names
   `hasSeparationL`, `hasReplacementL`, `Lset`, `LsetS`, `stage` or
   `boundingOrd`** (`:481-483`). The whole chain runs on V-side ordinal
   vocabulary. **The J tower re-instantiates it IF its ordinals present the
   same way**, and the report marks that condition rather than hiding it
   (`:485-487`).
2. **`[LJ-1.154]` MEASURED that genericity is FREE here.** `ProbeLJ1154D.agda`
   names `hasSeparationL` inside `Carve` instead of taking it as a parameter,
   and costs 1.60 s against 1.67 to 1.81 s. **The gap is inside the 12.8
   percent between-series band** (`:360-364`).
3. **`[LJ-1.159]` MEASURED that genericity is CHEAPER, by 8.4 times.** Taking
   the ambient ordinal as a parameter is both the DD4 move and the seconds
   cure. "**Genericity and speed are the same edit here**" (`:325`). **That is
   the strongest DD4 evidence in this cluster.**

**The honest residue, and all three reports name it identically.** The code is
generic in the ORDINAL and not in the CARRIER. It sits over `𝒮ᵥ` or `𝒮ʟ`. A
full two-tower form takes the structure as a module parameter, as `FOL.ZFModel`
already does (`agents/tasks/LJ-1-156/lj-1.156-report.md:487-491`,
`agents/tasks/LJ-1-154/lj-1.154-report.md:352-358`). **No task has measured
that refactor.**

### 5.2 The negative, and it is MEASURED

**MEASURED: no report gives a generic or re-instantiation figure for A1, A2,
A3, A4, A6 or A7.**

**The search.** I ran `grep -rn "re-instantiate\|reinstantiate\|
re-instantiates" agents/tasks/*/lj-*.md` over all 88 live task directories.
**It returns 24 hits outside this report. None of them prices an A-prime block
except A5's parts.** The other hits belong to `[LJ-1.166]`, `[LJ-1.168]`,
`[LJ-1.171]` and `[LJ-1.173]`, which are the condensation and satisfaction
side, not Route A-prime. **The same search over `agents/tasks/archive/` returns
no hit that names an A-prime block.**

**So the DD4 column covers the one block that has no line price, and covers
none of the six that do.** That is the exact inverse of what the route needs.

## 6. THE GAPS, NAMED ONE BY ONE

**A gap is a block with no price, or a block priced only by analogy. Both are
listed. Every entry says what would close it.**

| gap | what it needs |
|---|---|
| **G1. A5's line price.** The blocker | **A PROBE.** Price the L-side of the chain, or price the four INFERRED carvings. `[LJ-1.156]:636-638` names them: `ShiftAbs`/`Shiftω`, the inclusion `j`, `pairω`, the column square. Each still needs its own one-place description |
| **G2. A6's open charge.** A6 is not one number | **A RULING or a probe.** The charge is one instance of A5's per-construction cost. It closes when G1 closes, or when the orchestrator rules that A5's object list owns `ShiftAbs` and A6 owns none of it |
| **G3. The partition.** Five measured overlaps, section 3 | **A RULING.** The seven-block split needs one owner who says what each block contains. Two reports define A5 differently, and neither is wrong on its own terms |
| **G4. A1, A4, A7 have no measured core.** 340 of the 705 lines rest on reading alone | **A PROBE each, or acceptance.** Under DD8 their basis word is **comparable**. P-l says a comparable is a hypothesis. `[LJ-1.136]:297-305` argues each is readable, and that argument is sound; it is still not a measurement |
| **G5. A2's two unpriced pieces.** The range formula and `ranAt` adequacy | **A PROBE.** Named unpriced at `agents/tasks/LJ-1-134/lj-1.134-report.md:259-261`, and `[LJ-1.136]` covers them by reading inside the 170 |
| **G6. Which seconds bar prices a new module.** Section 4.1 | **A RULING.** 0.009143 or 0.007913. The two answers differ by 1.16 times |
| **G7. The carrier-generic refactor.** DD4's remaining half | **A PROBE.** Take the structure as a module parameter. Three reports name it and none measured it |
| **G8. `levelIn` and `cover`, the condensation hard part** | **Route-neutral and excluded from every A-prime figure.** `agents/tasks/LJ-1-131/lj-1.131-report.md:400-407`. **It is NOT in the 705 and it was never meant to be** |

**G8 is the one that would silently corrupt a total.** `[LJ-1.131]` excluded it
deliberately, because both routes owe it in full and it does not separate them.
**A reader who takes 705 as "what A-prime costs" adds a chapter that the 705
never contained.**

## 7. WHAT `[LJ-1.8]` STILL NEEDS

**`dev/PLAN.md:50` states the trophy row's blocker: "Route A-prime still has no
TOTAL". This task does not clear it.**

**The trophy row does NOT unblock, and one probe is not enough to unblock it.**

1. **G1, the A5 probe.** This is the arithmetic blocker. Without it there is no
   sum.
2. **G3, the partition ruling.** This is the bigger one, and it is CHEAPER.
   **It costs a ruling, not a probe.** Without it, a priced A5 still does not
   add to a total, because A6's cell names A5, A4's cell names A2, and a
   300-line item sits across A4 and A5 undivided.
3. **G8 must stay excluded, in writing.** `levelIn` and `cover` are outside
   every figure here.

**INFERRED, and I mark it as mine: G3 should go first.** It is a ruling over
text already on disk, it needs no machine, and it decides what the A5 probe
must measure. **A probe sent before the ruling measures a block whose contents
two reports define differently.**

**What the total would look like once both close.** 705 plus A5, minus whatever
the partition ruling removes from the overlaps, and the DD4 column is known for
one block of the seven. **I state that shape and no number**, because DD8 wants
one best-effort figure with a basis, and A5 has no basis to give one.

## 8. THE NEGATIVES, EACH CLASSIFIED

- **MEASURED. A5 has no live line figure.** The search is
  `grep -rn "A5" agents/tasks/*/lj-*.md` filtered for line figures, over all 88
  task directories. It returns two figures and both are refuted, section 2.
- **MEASURED. No task after `[LJ-1.136]` wrote an A5 line price.** Same search.
  `[LJ-1.152]`, `[LJ-1.154]` and `[LJ-1.156]` each refused in writing.
- **MEASURED. No generic figure exists for six of the seven blocks.** The
  search is `grep -rn "re-instantiate..."` over all task reports, section 5.2.
- **MEASURED. `[LJ-1.136]`'s seconds bar is stale.** `dev/ledger.toml:2730`
  carries 0.009143 where `[LJ-1.136]:1081` cites 0.014367.
- **MEASURED. The blocks do not partition.** Five overlaps, each quoted from
  the reports' own text, section 3.
- **MEASURED. `[LJ-1.156]`'s probe builds no L-element.** Its own section 14
  states it (`:640-642`), and its section 8 gives the grep (`:450-452`).
- **MEASURED FALSE. A5's last unknown dissolved.** The brief says so at
  `agents/tasks/LJ-1-175/LJ-1.175.md:11`. **A5's REPLACEMENT COUNT dissolved.**
  Its line price and the L-side of its chain did not, and `[LJ-1.156]:611-646`
  lists five things it left open.
- **INFERRED, and it is mine. G3 should be ruled before G1 is probed.**
  Section 7.
- **INFERRED. The 705 is a lower bound on the six blocks.** The overlaps could
  be net-positive or net-negative and nobody measured them.
- **NOT MEASURED IN EITHER DIRECTION. Whether the four INFERRED carvings
  carve.** Inherited from `[LJ-1.154]:288-296` unchanged. **I transferred no
  measured cure to them by analogy.**

## 9. ARCHIVE USED (DD18)

**`agents/tasks/` corpus** (the live record, read as the brief's SCOPE
directs):

- **`agents/tasks/LJ-1-156/lj-1.156-report.md`, read WHOLE.** TAKEN: the zero
  replacement count at `:286-288`; the seconds table at `:184-189` and `:208`;
  the line table at `:242-252`; the six-object table at `:270-278`; the DD4
  grep at `:481-483`; **and the five open items at `:611-646`, which is the
  evidence that A5 is not priced.**
- **`agents/tasks/LJ-1-136/lj-1.136-report.md`, read WHOLE.** TAKEN: the
  re-priced table at `:82-94`; the 705 at `:92`; the method table at `:297-305`;
  the six built objects at `:205-215`; the two comparables at `:249-278`; the
  probe results at `:1005-1139`. **REFUSED: the 0.014367 bar at `:1081`, which
  the ledger has replaced.**
- **`agents/tasks/LJ-1-131/lj-1.131-report.md`.** TAKEN: the seven-block split
  at `:365-374`; the reuse-at-zero stack at `:351-357`; the exclusion of
  `levelIn`/`cover` at `:400-407`; **the 300-line item across A4 and A5 at
  `:464-465`**. **REFUSED: the 760-to-1,320 total, superseded.**
- **`agents/tasks/LJ-1-134/lj-1.134-report.md`.** TAKEN: the per-part table at
  `:219-227`; A2's 78-line core at `:229-233`; A3's 22 lines at `:235-239`; the
  2.51 s upper bound at `:30-34`; the two unpriced pieces at `:259-261`.
- **`agents/tasks/LJ-1-154/lj-1.154-report.md`.** TAKEN: the 1.73 s against
  254.22 s at `:155-165`; the line table at `:185-193`; **the DD4 table and the
  90 re-instantiating lines at `:334-350`**; the refusal to multiply at `:307`.
- **`agents/tasks/LJ-1-152/lj-1.152-report.md`.** TAKEN: the 2.50 s
  composition at `:134` and `:171`, three kept runs; the ratio of at least
  2,500 to 1 at `:173`; the verdict row at `:203`.
- **`agents/tasks/LJ-1-159/lj-1.159-report.md`.** **NOT in the brief's archive
  list, and it is the newest task that moves an A-prime figure.** TAKEN: the
  cure at `:20-33`; the consumer check at `:340-362`; the price table at
  `:370-375`; the DD4 answer at `:318-327`; the residue at `:397-431`.
- **`agents/tasks/LJ-1-107/lj-1.107-report.md`.** TAKEN: the per-step table at
  `:49-57`, which is the shared basis of A4, A5 and A6 and the evidence for
  overlap 4.

**`archive/dev/` (the retired route):**

- **`archive/dev/TASKS-archived.md:123`**, `[L3.32-T88]`, "Measure SquareLaw's
  856 s". **SHAPE TAKEN, not a claim.** The full report is at
  `agents/tasks/archive/L3-32-T88/l3.32-t88-report.md:7-22`: four
  near-duplicate definitions carried 88 percent of the time, all at
  `⟪ sucV (γp p) ⟫`. **That is the same defect `[LJ-1.159]` found at the same
  site**, and it says the cost at this site concentrates in a few definitions
  that name `sucV` in a type. **WHAT WOULD NOT TRANSFER: the 856 s itself.** It
  was measured on the retired route's tree, and P-l forbids carrying it.
- **`archive/dev/TASKS-archived.md:262`**, `[L3.32-T257]`, the GCH wing priced
  at 25,485 to 28,258. **SHAPE TAKEN: its method is a row-by-row table with
  UNCHANGED rows carried forward and a declared weak point**
  (`agents/tasks/archive/L3-32-T257/l3.32-t257-routes.md:91-222`). **WHAT WOULD
  NOT TRANSFER: every figure.** Those rows price the retired rud route's wing,
  which has different blocks. `dev/PLAN.md:236` already treats that figure as a
  benchmark with a declared weak point worth a fifth of its band.
- **`archive/dev/STATUS-archived.md:115-116`.** Read. **Nothing bears on the
  block prices.** The GCH rows there are planning rows.
- **`archive/` (retired code): NOT read.** This task compares figures in
  reports. No archived module bears on whether a figure is superseded. **I
  record the omission rather than claim a survey.**

## 10. LITERATURE USED (DD18)

**Nothing in the literature prices a formalization.** `dev/literature/` holds
the mathematics of the route, not its line cost, and no source in it states a
line or seconds figure for any block. **The brief says this in one line and the
brief is right.**

## 11. WORKING TREE, AS MY REPORT DESCRIBES IT

**One file added: `agents/tasks/LJ-1-175/lj-1.175-report.md`, this file.**

No master edited. No brief edited. No other report edited. No probe written and
none needed. **No Agda process ran at any point in this task**, as the brief
required.
