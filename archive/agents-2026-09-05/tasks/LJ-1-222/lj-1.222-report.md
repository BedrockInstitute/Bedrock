# LJ-1.222 report: adversarial check of the 695 before the ledger write

tier: opus (deepseek-subagent-mode). The switch's ADVERSARIAL row. The target
was written by pi, so DD17's invariant holds: the critic is not the author.

**STATUS: COMPLETE. THE 695 FALLS. NO ABORT FIRED.**

I did not run Agda. I did not run `make check`. I edited no master, no brief,
no ledger and no other agent's report. I did not commit and did not push. I ran
no `git checkout`, `git stash`, `git reset` or `git clean`. Written
incrementally (C-22). Every negative is marked **MEASURED** or **INFERRED**.

## 0. THE NUMBER

**`lines_removable = 83`.**

**The 523 does not stand.** The supersession reading fails on the record, on
the source, on a measured law and on the literature. The block is unconsumed
for the reason `[LJ-1.146]` measured for the whole wing: the trophy is
unwritten. It belongs on the side where `[LJ-1.218]` itself put 1,105 lines of
`*Agree`.

**Class A also falls by 99 lines**, on a rule the target does not cite: D-27.

| class | reported | this review | why |
|---|---:|---:|---|
| A, dead names | 163 | **64** | minus 92 (`module Inj`) and minus 7 (`Mostowski`), both fail D-27 |
| B, DD4 duplication | 4 | **4** | I found no defect |
| C, abandoned artifact | 5 | **5** | I found no defect, with one noted tension |
| D, erase-transfer chain | 523 | **0** | REFUTED, section 1 and section 2 |
| re-classified D to A | 0 | **10** | `ride-only`/`ride-defines`, a pure alias, section 3 |
| **total** | **695** | **83** | |

**The orchestrator can recompute under any subset of my rulings.**

| accept | figure |
|---|---:|
| all three findings | **83** |
| the class D refutation and D-27, not the `ride-*` move | 73 |
| the class D refutation and the `ride-*` move, not D-27 | 182 |
| the class D refutation only | **172**, the brief's own second outcome |
| none of them | 695 |

**What I did NOT audit.** Ten of the remaining Class A rows, 64 lines, I did
not test against D-27. **MEASURED FALSE that 64 is an audited figure.** It is
163 minus the two rows I refuted. C-42: a refutation measures the site it
names, never its extent.

## 1. Does the record support supersession? NO.

**MEASURED. Not one record before `[LJ-1.218]` says the chain was abandoned,
superseded, retired or replaced. The one record that names its fate says
REPAIRED.**

### 1.1 The plan rows say the opposite of what the target reads in them

`dev/PLAN.md:553` records `[LJ-1.37]` as DEFECTIVE: "Landed 1,723 lines and
passed every MECHANICAL check. The rows are false of the satisfaction table."
`dev/PLAN.md:555` records `[LJ-1.38-R]` upholding that: "the rows are FALSE of
the satisfaction table. 968 of 2,141 lines re-open."

**`dev/PLAN.md:557` is the row the target does not quote.** `[LJ-1.40]` is
titled "REPAIR: re-index the rows TRUE, close the agreement" and its verdict
cell reads **"REPAIRED, agreement PARTIAL"**.

`agents/tasks/archive/LJ-1-40/lj-1.40-report.md:8-11` says it at the source:
"REPAIRED, WITH THE AGREEMENT PARTIALLY CLOSED. The rows are re-indexed, the
defective shapes and leaves are corrected, and the master is green."
`:53-54` adds: "They are re-indexed and their certificates check, but the
agreement does not consume them yet."

**A row saying a build was DEFECTIVE is not a row saying its route was
ABANDONED, and the brief said so before I started.** The record shows the
sequence built, refuted, REPAIRED. It does not show a route change.

### 1.2 The target's own cited evidence does not say what it reports

`agents/tasks/LJ-1-218/lj-1.218-report.md:170-172` cites `dev/PLAN.md:562-563`
for "Two spellings per leaf" and reads the two spellings as Row against Agree.

**MEASURED FALSE.** `agents/tasks/archive/LJ-1-44/lj-1.44-report.md:10-13`
defines the two spellings as the story's bounded formula and the machine's.
`agents/tasks/archive/LJ-1-45/lj-1.45-report.md:16` says "All twelve row
agreements plus block 1 stay CLOSED". Neither task touched the `*Row` family.

### 1.3 A later record calls the chain the delivered, prescribed exit

`agents/tasks/archive/LJ-1-50/lj-1.50-review.md` section 2 is headed **"THE
`EraseTransfer` EXIT: BUILT"**. It applies "the delivered template
`EraseTransfer`" and states that this is "the shape of the delivered
`RowTransfer` ... which already applies the same template to the twelve rows
and **is green in the tree**".

It then recommends **growing** the family: "It is the template `L.Condensation`
is missing, and I recommend the connector build place it beside
`EraseTransfer`."

**INFERRED: a record that names a block as the rulebook's own exit, and asks
for a sibling beside it, is the opposite of an abandonment record.** It is
dated after `[LJ-1.45]`.

`agents/tasks/LJ-1-211/lj-1.211-report.md:115-118` repeats it: "P-u prescribes
composing the absoluteness through the unplaced form, which is
`EraseTransfer`".

### 1.4 The chain is the machine-checked form of a measured law

**This is the finding that decides section 1.** `dev/LESSONS.md:2926-2934`
states P-u: "certify the formula BEFORE you place it, then compose the
absoluteness through the unplaced form". `dev/LESSONS.md:2957-2959` gives the
route out: "a formula with NO constants reaches the parameter-free axis through
the delivered `erase` with no placement anywhere".

`src/L/Condensation.lagda.md:275-280` is that law, written as code, and it
cites the law by name: "Any formula at the class carrier with zero constants
and a Delta-0 witness reaches the parameter-free axis through the delivered
erase ... The transfer is then two syntactic congs around one abs₀ at the
ORIGINAL clause: **certify before you place (P-u)**."

**The alternative is a measured wall, not a preference.**
`dev/LESSONS.md:2943-2948` records that the placed witness EXHAUSTS 8 GB in
55 s, in two formulations, and that the composed route through the unplaced
form checks in 25.6 s.

**INFERRED: a block that implements a measured law's prescribed cure is not
surplus. It is the cheap form of the only route the project has priced.**

### 1.5 What the record does support

**MEASURED, and it is the target's true finding:** from `[LJ-1.40]` on, the
effort went into a second and disjoint family, the `*Agree` modules, which
`[LJ-1.43]` completed (`dev/PLAN.md:561`, "The twelve-row table is complete and
machine-checked"). The `*Row` family sits at
`src/L/Condensation.lagda.md:1814-2230` and the `*Agree` family at `:2774-5330`.
`[LJ-1.218]:159-161` measured zero name overlap and I did not find one either.

**That is a fork in attention, not a supersession.** Section 2 shows the two
families prove theorems that are orthogonal, so neither can retire the other.

## 2. Does the future trophy need this content? YES.

**This is the decisive section. The two routes are not rivals. They are the two
halves of one bridge, and the trophy needs both.**

### 2.1 The two theorems, at `file:line`, in both blocks

| block | statement | carrier |
|---|---|---|
| agreement | `out : ⟨ γ ⊨ topClauseAt C T B ⟩ → ⟨ γ ⊨ φB ⟩`, `src/L/Condensation.lagda.md:3697` and `back` `:3710` | **`⊨` on both sides.** ONE carrier |
| erase transfer | `σL-transfer : ⟨ γ ⊨ σL ⟩ ≡ ⟨ map fst γ ⊨ᵛ σL ⟩`, `src/L/Condensation.lagda.md:298` | **`⊨` to `⊨ᵛ`.** TWO carriers |

**MEASURED.** The agreement route relates the machine formula to the bounded
formula at the SAME carrier. The erase transfer moves one formula from the
class carrier to the tower. **An agreement between two formulas at a carrier
that is not the tower proves nothing about the tower.**

`[LJ-1.218]:177-179` states this correctly and then draws the wrong conclusion
from it: "The agreement route and the erase-transfer rows prove DIFFERENT
theorems (agreement out/back versus σL decode)". **A different theorem cannot
supersede; it can only fail to supply.** The target treats "different" as
evidence for removal, and it is evidence against removal.

### 2.2 Remove the 523 and the chapter has no carrier transfer at all

**MEASURED.** `src/L/Condensation.lagda.md` contains eight occurrences of
`⊨ᵛ`: `:298`, `:302`, `:304`, `:374`, `:377`, `:410`, `:1800`, `:1802`.
**All eight lie inside the 523.**

**MEASURED.** The two delivered absoluteness theorems have exactly one consumer
each in the chapter, and both consumers are inside the 523:
`AbsL.abs₀` at `src/L/Condensation.lagda.md:301`, and `AbsL.σ₁-up` at `:411`.
The theorems are `src/FOL/Absoluteness.lagda.md:122` and `:182`.

**INFERRED: delete the 523 and `src/L/Condensation.lagda.md` never once
crosses from the class carrier to the tower, and never once uses the
absoluteness theorems the chapter imports.** For a condensation chapter that
is not a saving. It is a hole.

### 2.3 The trophy is unwritten, so C-35 fires here for the wing's one reason

**MEASURED.** The chapter's last module is `KValue`
(`src/L/Condensation.lagda.md:7222`), which supplies one `KFacts` value. There
is no condensation theorem and no assembly. `[LJ-1.146]:31-35` measured the
cause: "C-35 fires over the whole wing, from `TwelveAgree` at the top down to
`theorem` at the bottom, and the cause is one thing: the trophy at the bottom
is not written."

**`[LJ-1.146]:23-25` gives the test the target failed to apply here:** "A
supply chain with no consumer is the signature of an unbuilt assembly, not of
dead code."

**INFERRED: the erase-transfer chain is supply, not surplus.** `[LJ-1.218]`
applied that rule to the agreement half of the bridge, keeping 1,105 lines out
of the figure (its section 3), and did not apply it to the transfer half. Both
halves are unconsumed for the same one reason.

### 2.4 The literature answers the brief's question directly

**The brief asked: if the trophy needs a σL decode anywhere, the 523 are owed.**
`dev/literature/devlin-II5.md:224-228` lists what Devlin's condensation proof
needs, and items 3 and 4 are the two transfers this chain implements:

> 3. Σ₀ absoluteness for the matrix: 1.9.15 moves L_α's (or M's) satisfaction
>    ... Σ₀ and absolute for transitive sets.
> 4. Transfer along elementarity and the collapse: the Σ₁ statement

`:102-103` states the same chain: "for each ordinal γ of the collapse, the Σ₁
statement ... is transferred from L_α to X".

**Δ₀ absoluteness of the matrix is `abs₀`, used once, at `:301`. The Σ₁
transfer is `σ₁-up`, used once, at `:411`. Both uses are inside the 523.**

## 3. Is the line count right? THE 523 IS ARITHMETICALLY EXACT AND ITS ENUMERATION IS SHORT

### 3.1 The eight ranges reproduce 523

**MEASURED** at the ledger caliber, non-blank lines inside ` ```agda ` fences,
comments counted. My own counter also reproduces the file total of 6,676 that
`agents/tasks/LJ-1-218/lj-1.218-report.md:21` quotes, so the caliber agrees.

| range | span | counted |
|---|---:|---:|
| `:266-270` | 5 | 4 |
| `:284-314` | 31 | 23 |
| `:315-360` | 46 | 43 |
| `:408-411` | 4 | 4 |
| `:418-428` | 11 | 10 |
| `:1791-1803` | 13 | 13 |
| `:1805-1813` | 9 | 9 |
| `:1814-2230` | 417 | 417 |
| **sum** | | **523** |

### 3.2 The 523 UNDERSTATES its own block by 38 lines

**MEASURED.** `module ClauseDecode` runs from
`src/L/Condensation.lagda.md:315` to `:405`. The report's range stops at
`:360`. Lines `:361-405` hold the rest of the module: the template
instantiation `module E = EraseTransfer` at `:362-363`, the five re-exports
`σL`, `σL≡`, `σL-eq`, `σL-transfer`, `σL-up` at `:365-378`, `σL-out` at
`:381-391` and `σL-in` at `:394-405`. That is **38 non-blank in-fence lines**.

**The row's own label claims those lines.** It reads "`module ClauseDecode`,
the clause decode and its `σL-out`/`σL-in`"
(`agents/tasks/LJ-1-218/lj-1.218-report.md:146`). The label names them and the
range excludes them.

### 3.3 Three further blocks are stranded by the same cut and are not counted

**MEASURED by occurrence scan over all in-fence code of `src/`.**

| block | site | consumers |
|---|---|---|
| `module Clause` | `src/L/Condensation.lagda.md:117-262` | every `Clause.` use is at `:267`, `:270` and `:321-403`, all inside the chain head. Two comment mentions at `:4121-4122` |
| the five decode modules | `:788` `UnFullDecode`, `:828` `BinFullDecode`, `:868` `UnBareDecode`, `:896` `UnEnvDecode`, `:931` `BinEnvDecode` | consumed ONLY by the eleven `*Row` modules. `UnBareDecode` has 2 occurrences, `UnEnvDecode` 2, `UnFullDecode` 3, `BinEnvDecode` 3, `BinFullDecode` 6 |
| the eleven row certificates | `botCertAt` `:1841-1844` through `exInCertAt` `:2226-2229` | uses=4 each, which are their own two declarations |

**Why this matters even though I refute the removal.** A figure that claims to
name every line of a block, and misses the module tail plus the modules the
block alone consumes, was not built by following the dependency edges. **It was
built by listing the names the scanner flagged.** The scanner is
`agents/tasks/LJ-1-218/deadnames.py`, which I read: it counts word occurrences
of DECLARED names per master (`:100-106`) and never walks an edge. **INFERRED:
the method cannot find a stranded module, only a stranded name.**

**So the correct statement of the block, had the supersession held, is not 523.
It is at least 561, and probably about 900 with `module Clause` and the decode
modules.** I do not put that number in the ledger, because section 1 and
section 2 refute the removal.

### 3.4 The 4 lines of class B and the 5 of class C

**I found no defect in class B.** `_↪_` at
`src/L/BoundedSubset.lagda.md:1043-1044` against
`src/L/StageCardinal.lagda.md:221-222`, and `comp-inj` at `:1364-1366` against
`:500-502`. The import edge exists at `src/L/BoundedSubset.lagda.md:882`.

**Class C, one tension I record and do not act on.** `consed`
(`src/L/Condensation.lagda.md:7271-7275`) is the block's FIRST-CONSUMER test,
and its own comment says so: "this is the test: `KFactsCons` is the tree's own
consumer and it accepts the record at its own indices" (`:7274-7275`).
Removing it removes the only evidence in the tree that the record is
inhabitable at a consumer's indices, which is C-35's own cure. **I leave the 5
lines in the figure and flag the tension for the owner.**

## 4. CLASS A FAILS D-27 AT TWO ROWS, 99 LINES

**D-27 is `dev/LESSONS.md:1720`: "No code consumer" identifies a dead HELPER,
never a dead RESULT.** `[LJ-1.218]` cites no rule for its Class A method, and
Class A is a no-consumer sweep, which is exactly D-27's subject.

**D-27 exists because this failed before, and it was measured.**
`dev/LESSONS.md:1746-1748`: "a re-scan deleted 68 lines on the no-consumer
criterion, correctly by that criterion, and 51 of them were reverted."
`dev/PLAN.md:522` carries the same record.

### 4.1 `module Inj`, 92 lines, was ALREADY ruled kept under D-27

**MEASURED.** `dev/PLAN.md:544`, the `[LJ-1.13]` row, reads: "isExt at :31,
InjExt at :220. **Trivial `Inj` kept per D-27**."

**`[LJ-1.218]` reverses a recorded ruling without citing it.**

**And the subsumption that would justify the reversal has no witness in the
tree. MEASURED.** `module Inj` takes `isTrans X`
(`src/V/Collapse.lagda.md:118`); `module InjExt` takes `isExt X` (`:220`).
There is no term of type `isTrans X → isExt X` anywhere in
`src/V/Collapse.lagda.md`. Both consumers take `isExt` as a module parameter
and pass it straight through (`src/L/BoundedSubset.lagda.md:321,323` and
`:1058,1061`), so neither ever held transitivity to convert.

`[LJ-1.218]:238` marks the subsumption **INFERRED** in its own table. **A
92-line removal resting on an unwitnessed inference, against a recorded ruling,
does not go in the ledger.**

The chapter anticipates transitivity-carrying consumers:
`src/V/Collapse.lagda.md:22-24` says `isTrans` is "definitionally the same
predicate as the constructible chapter's `isTransV`, so a consumer's
transitivity witness passes through unchanged".

### 4.2 `Mostowski`/`mostowski`, 7 lines, is the chapter's stated result

**D-27 class 1.** The chapter is titled "# The Mostowski collapse"
(`src/V/Collapse.lagda.md:1`). The block at `:304-312` is, in the target's own
words, "the bundled statement of the collapse"
(`agents/tasks/LJ-1-218/lj-1.218-report.md:99`). The source comment agrees:
"the Mostowski statement for the carrier: transitive range, injectivity, and
membership preserved both ways" (`src/V/Collapse.lagda.md:304-305`).

**INFERRED: deleting the term named `Mostowski` from the chapter titled "The
Mostowski collapse" is D-27's exact failure shape.**

### 4.3 The rows I did NOT re-audit, and one that survives cleanly

**I did not test the other ten Class A rows against D-27.** 64 lines. **The
risk is live and I name it rather than absorb it.**

**One row I did test and it survives.** The Hull least-witness family, 36 lines
at `src/L/Hull.lagda.md:359-410`. The book's recap advertises the result: "the
definable hull of a set as the set of least witnesses"
(`src/Everything.lagda.md:920-924`). **But the result stays advertised AND
stays proved**, because the live `TermAlgebra.search` path delivers it, and the
supersession here has an OWNER RULING behind it: DD27
(`dev/PLAN.md:277`), with `dev/PLAN.md:576` recording "Piece one retired".

**That contrast is the whole review in one line. `[LJ-1.218]`'s Hull row has a
ruling behind its supersession. Its Class D row has none, and uses the same
word.**

## 5. THE `ride-*` PAIR MOVES FROM D TO A, 10 LINES

**MEASURED: `ride-only` and `ride-defines`
(`src/L/Condensation.lagda.md:418-428`) are pure aliases with zero readers.**
`ride-only` shows 2 occurrences, `ride-defines` 2, which are their own
declarations and bodies. The bodies are
`ride-only {n} w b γ = Lset-only w b γ` (`:422`) and
`ride-defines {n} w b γ = Lset-defines w b γ` (`:428`).

**The types are identical to the delivered ones.** `Lset-only` sits at
`src/L/Hierarchy.lagda.md:333-335`, inside
`module _ {n : ℕ} (w b : Fin n) (γ : S ^ n) where`, at the same carrier `S`
with the same telescope. **The alias adds nothing.**

**So they are P-v's defect (`dev/LESSONS.md:3055`), a second spelling, not
supply.** The content exists elsewhere, is delivered, and its result stays
advertised by `src/Everything.lagda.md:623`. **D-27 passes.** They meet the
target's own Class A criterion: a dead spelling with a live sibling.

**One tension I record.** If the assembly is written, it will want these legs
at the class carrier. It can call `Lset-only` directly through the existing
import at `src/L/Condensation.lagda.md:50`. **The alias buys nothing the import
does not.**

## 6. THE 1.70x SERIES, AND THE BUSIER MACHINE

### 6.1 The verdict on the reading: RIGHT CONCLUSION, INVALID REASON

`agents/tasks/LJ-1-218/lj-1.218-report.md:75-79` says the 7 s fall "is 3.6 pc,
inside the between-series band, and today's machine was busier ... so the fall
is not a finding."

**The conclusion is correct.** The instrument declares its own noise band in
the log the run produced: "noise band: at least +-12.8%, MEASURED [LJ-1.148]"
(`agents/tasks/LJ-1-218/runs/wing-ratio-n2.log`, header). A 3.6 percent move
sits well inside 12.8 percent. **That reason alone settles it.**

**The second reason is invalid, and the brief is right to challenge it.** If a
busier machine should produce MORE seconds, then observing FEWER seconds on a
busier machine makes the fall harder to explain, not easier. **The clause cuts
against the conclusion it is offered to support.**

**The "upper bound" claim rests on a premise these two points refute.**
`:79` says "Both are upper bounds on a quiet machine". That needs seconds to
rise with load. Here the LOWER-load series produced the HIGHER figure, so the
two data points contradict the monotonicity the claim assumes.

### 6.2 The explanation the report had in hand and did not state

**MEASURED, and it is in a report `[LJ-1.218]` says it read WHOLE.**
`agents/tasks/LJ-1-185/lj-1.185-report.md:529`: "the machine was quiet
throughout | **MEASURED FALSE.** A sibling, `[LJ-1.184]`, ran Agda from 09:29;
at 09:32 it ran **TWO agda processes at once, RSS 6.9 GB and 3.9 GB**."
`:444`: "A sibling ran Agda beside this series and the number is an UPPER
BOUND."

**So the direction is fully explained.** Load average counts runnable
processes. For Agda the operative competitor is another Agda, because of memory
bandwidth and resident size. `[LJ-1.185]` ran against two sibling Agda
processes at 10.8 GB combined. `[LJ-1.218]` ran against Warp, WebKit,
GF-Trader and Bitcoin-Qt, which raise the load average and do not compete for
the same resource.

**INFERRED: the 7 s is decontamination, not noise.** The figures are consistent
and the 185.41 s is the better founded of the two.

**What this does NOT license.** The 60.0 s gap is still an upper bound, because
load 5.5 to 7.0 is still not a quiet machine. **The report's recommendation 3
stands and I endorse it** (`agents/tasks/LJ-1-218/lj-1.218-report.md:330-332`).

**I did not re-run the ratio.** DO NOT RUN AGDA was the brief's rule and I kept
it. Every figure in this section is read from the target's log and from
`[LJ-1.185]`.

## 7. DD4

**Maximize the code the two proofs share, and write it generic. One rule, two
ends, no metric and no checker.**

**The brief asked whether the 523 are the project's best DD4 shape written on
the wrong route. MEASURED: they are the project's best DD4 shape, and the route
is not wrong.**

`src/L/Condensation.lagda.md:274-283` is the template's own header, and it
states DD4 without being asked to: "Both towers instantiate this module with
their own formulas; **nothing here mentions L's Def syntax**." The module is
parameterized by the formula at `:284`, exactly as the brief said.

**The structure is already the two-tower split, written down.** `:274` labels
`EraseTransfer` TEMPLATE. `:309-314` labels `ClauseDecode` PER-TOWER (Def).
`:413-418` labels `ride-*` DELIVERED, NEITHER TEMPLATE NOR PER-TOWER. **Three
labels, one boundary, drawn where DD4 wants it.**

**An independent reviewer reached the same reading and measured it.**
`agents/tasks/archive/LJ-1-50/lj-1.50-review.md` states of its Σ₁ sibling:
"That module is DD4 content: it mentions no L syntax, so the J tower
instantiates it exactly as the L tower does." It measured the abstract-formula
form at **2.83 s** against **129 s** for the same mathematics written at the
concrete statement, and concluded "129 s becomes unmeasurable, by stating the
transfer at the abstract formula".

**So the erase-transfer layer is the one place in the wing where the
class-generic lesson of `[LJ-1.210]` DID reach a wing master.**
`agents/tasks/LJ-1-218/lj-1.218-report.md:218-223` says the lesson "does not
reach the wing masters" and then names this layer as the exception in the same
sentence, before classifying it dead. **The exception is the finding.** Of the
523 lines, 23 are the generic template (`:284-314`) and 500 are its per-tower
instantiations. **Retiring the 23 would delete the only delivered two-tower
seam in the chapter, and it is measured 45x cheaper than the concrete
spelling.**

## 8. EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| the eight ranges sum to 523 at the ledger caliber | **MEASURED.** My counter, and it reproduces the 6,676 file total |
| the erase-transfer chain has zero application points | **MEASURED.** I re-derived it: the eleven `*CertAt` pairs show uses=4, `ClauseDecode` `CertTransfer` `RowDecode` show 1 each |
| the chain was superseded, abandoned or replaced | **MEASURED FALSE.** No record says it. `dev/PLAN.md:557` says REPAIRED, and `agents/tasks/archive/LJ-1-40/lj-1.40-report.md:8-11` says it at the source |
| the agreement route supplies what the chain supplies | **MEASURED FALSE.** The agreement is one-carrier (`:3697`, `:3710`); the transfer is two-carrier (`:298`) |
| all eight `⊨ᵛ` in the chapter lie inside the 523 | **MEASURED.** `:298`, `:302`, `:304`, `:374`, `:377`, `:410`, `:1800`, `:1802` |
| `abs₀` and `σ₁-up` have any consumer in the chapter outside the 523 | **MEASURED FALSE.** One each, at `:301` and `:411` |
| the trophy needs a Δ₀ and a Σ₁ transfer | **MEASURED** from the literature, `dev/literature/devlin-II5.md:224-228` and `:102-103` |
| the 523 names every line of its block | **MEASURED FALSE.** `module ClauseDecode` `:361-405` is 38 counted lines and is excluded, though the row label claims it |
| `module Clause` and the five decode modules have a consumer outside the chain | **MEASURED FALSE.** All `Clause.` uses are at `:267,:270,:321-403`; each decode module is used only by `*Row` modules |
| `module Inj` is superseded by `InjExt` | **INFERRED in the target and unwitnessed here. MEASURED:** no `isTrans X → isExt X` term exists in `src/V/Collapse.lagda.md`, and `dev/PLAN.md:544` records `Inj` kept per D-27 |
| `ride-only`/`ride-defines` are pure aliases with zero readers | **MEASURED.** Bodies at `:422` and `:428`; the delivered originals at `src/L/Hierarchy.lagda.md:333-335` |
| the 3.6 pc ratio fall is a finding | **MEASURED FALSE.** The instrument's declared band is at least +-12.8 pc |
| a busier machine explains fewer seconds | **MEASURED FALSE** as stated. The real cause is two sibling Agda processes at 10.8 GB during `[LJ-1.185]`, `agents/tasks/LJ-1-185/lj-1.185-report.md:529` |
| I audited all thirteen Class A rows | **MEASURED FALSE.** I tested three: `Inj`, `Mostowski` and the Hull family. Ten rows, 64 lines, are unaudited |
| I ran Agda, `make check`, a commit or a push | **MEASURED FALSE.** None of these |
| I edited a master, a brief, the ledger or another report | **MEASURED FALSE.** I wrote this file only |

## 9. WHAT I RECOMMEND, offered and not taken

1. **Write 83 to `dev/ledger.toml` `lines_removable`**, with this code beside
   `[LJ-1.218]`'s. If the owner declines the `ride-*` move, write 73. If the
   owner declines D-27, write 172.
2. **Do not retire the erase-transfer chain.** It is supply for an unwritten
   assembly, and it carries the chapter's only carrier transfer.
   `dev/LESSONS.md` P-u prices the alternative at an 8 GB wall.
3. **Book the chain as OWED work, not as removable lines.** DD5 measure 3
   should carry it on the remaining side, because the trophy needs it.
4. **Audit the ten Class A rows against D-27 before any of the 64 lines is
   quoted.** One dispatch, cheap, and D-27's own record shows the reversion
   rate on this criterion was 51 of 68.
5. **Record the counting defect against the method, not the agent.**
   `deadnames.py` finds a stranded NAME and cannot find a stranded MODULE. A
   removability sweep needs an edge walk.

## 10. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-218/lj-1.218-report.md`, read WHOLE.** **TOOK:** the
  eight ranges (`:144-151`), the four classes, section 3's kept list, and the
  ratio figures. **Its own honesty note at `:177-183` is what my section 2
  turns against the conclusion.**
- **`agents/tasks/LJ-1-218/deadnames.py`, read as source, not as an account.**
  **TOOK:** the method, `:100-106`, which counts word occurrences of declared
  names and walks no edge. That is why section 3.3 exists.
- **`agents/tasks/LJ-1-218/runs/wing-ratio-n2.log`, read whole.** **TOOK:** the
  instrument's declared noise band of at least +-12.8 pc, the per-master rows,
  and the aggregate 0.0155 over 11,926 lines.
- **`agents/tasks/LJ-1-146/lj-1.146-report.md:0-35`.** **TOOK:** the wing-wide
  C-35 finding and the supply-chain test at `:23-25`, which is the rule I apply
  in section 2.3. **I did not re-open it.**
- **`agents/tasks/LJ-1-185/lj-1.185-report.md`, read at `:444`, `:529`,
  `:549-554`.** **TOOK:** the two sibling Agda processes at 6.9 GB and 3.9 GB,
  which is the explanation section 6.2 supplies.
- **`agents/tasks/archive/LJ-1-50/lj-1.50-review.md`, read at section 2 and at
  `:160-190`.** **TOOK:** "THE `EraseTransfer` EXIT: BUILT", the 2.83 s against
  129 s measurement, the DD4 sentence, and the recommendation to grow the
  family.
- **`agents/tasks/archive/LJ-1-40/lj-1.40-report.md:8-11,:53-54`.** **TOOK:**
  REPAIRED and re-indexed, at the source.
- **`agents/tasks/archive/LJ-1-44/lj-1.44-report.md:10-13` and
  `agents/tasks/archive/LJ-1-45/lj-1.45-report.md:16`.** **TOOK:** the true
  referent of "two spellings", which refutes the target's reading of
  `dev/PLAN.md:562-563`.
- **`agents/tasks/LJ-1-211/lj-1.211-report.md:115-118`.** **TOOK:** P-u names
  `EraseTransfer` as the exit.
- **`dev/PLAN.md:552-563`, read whole and at the source**, plus `:277` (DD27),
  `:522` (the `[LJ-0.4m]` reversion) and `:544` (`Inj` kept per D-27).
- **`dev/LESSONS.md:1720-1772` (D-27), `:2926-2963` (P-u), `:3055` (P-v),
  `:3411-3434`.** **TOOK:** the rules that decide sections 1.4, 4 and 5.
- **`archive/dev/TASKS-archived.md` and `archive/dev/JOURNAL-archived.md`:
  SURVEYED, NOT USED as a claim.** **TOOK SHAPE only:** the retired route has
  a `σL`, but it is the LEVEL STORY and not a table row, and it holds no `Row`,
  `EraseTransfer`, `RowTransfer` or `ClauseDecode`. **What does NOT transfer:**
  any archived line count, and any archived reading of `σL`, because the name
  denotes a different object there.
- **`dev/JOURNAL.md`: MEASURED EMPTY for this question.** Zero entries match
  `LJ-1.3[6-9]` or `LJ-1.4[0-5]`. **The brief pointed me at JOURNAL for the
  `[LJ-1.37]`-to-`[LJ-1.45]` record and the record is not there.** It is in
  `dev/PLAN.md:552-563` and in `agents/tasks/archive/LJ-1-3x/`.

## 11. LITERATURE USED (DD18)

**I DISAGREE with `agents/tasks/LJ-1-218/lj-1.218-report.md:264`, "Nothing in
the literature governs removability."** The literature does not govern
removability as such. **But this brief asked a different question, and the
literature answers it.**

- **`dev/literature/devlin-II5.md:224-228`, USED and load-bearing.** Items 3
  and 4 of what Devlin's condensation proof needs are Σ₀ absoluteness of the
  matrix and the Σ₁ transfer along elementarity and the collapse. **Those are
  `abs₀` and `σ₁-up`, and their only two uses in the chapter are inside the
  523.** This is the evidence for section 2.4.
- **`dev/literature/devlin-II5.md:102-115`, USED.** The (c) to (q) chain
  transfers a Σ₁ statement from L_α to X. **TOOK:** that the transfer is a step
  of the proof, not an optional spelling.
- **`dev/literature/devlin-II5.md:174-194`: READ, NOT USED.** It prices
  level-hood at Σ₁ strength. **WHY NOT:** it bears on `LevelHood`, which
  `[LJ-1.218]` already keeps out of the figure, and not on the erase transfer.
- **`dev/literature/devlin-II5.md:154-166`: READ, NOT USED.** The GCH
  derivation from 5.5. **WHY NOT:** `[LJ-1.146]` already settled that route and
  the brief forbids re-opening it.

## 12. CHECKERS

| checker | result |
|---|---|
| `scripts/lint-prose.py --check` on this report | see below |
| `make check` | NOT RUN, by the brief |
| agda | NOT RUN, by the brief. Two siblings hold both slots (C-12) |

## 13. ONE DEFECT IN THE TOOLING, reported and not acted on

**MEASURED: `dev/LESSONS.md` holds exactly ONE P-l, at `:2323`, and it reads
"A statement may be ABOUT a concrete stage without dragging that stage's
PRESENTATION into its type".** `.venv/bin/python scripts/rules.py --for review`
returns that law, correctly.

**`AGENTS.md:134` cites P-l for a different law:** "A measured cure does not
transfer by analogy. Re-measure it at its own site." The brief's MANDATORY
RULES list repeats that citation.

**So the defect is a MIS-CITATION in `AGENTS.md`, not a duplicate ID and not a
tool fault.** The re-measure law is real and I obeyed it, but it is not P-l.
**`scripts/check-rule-ids.py` cannot catch this: the code RESOLVES, so the
checker is satisfied, and only a reader notices that the resolved text is a
different law.** That is the same gap `dev/PLAN.md:763` records for DD27
uniqueness. **AGENTS.md is DD19-guarded, so I propose no edit; the orchestrator
should take the ruling.**
