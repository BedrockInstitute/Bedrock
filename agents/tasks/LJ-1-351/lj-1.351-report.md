# LJ-1.351 report: `graphWitK` is FALSE, and its premise is a term

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. Probe, lands
nothing. Written incrementally (C-22). Every negative is MEASURED or INFERRED,
in those words.

## 0. LEAD

**FALSE. MEASURED.** `agents/tasks/LJ-1-351/Refute351.agda`, **exit 0 in
12.38 s** against a **0.90 s** floor. The tie at
`src/L/Condensation.lagda.md:7288-7297` is refuted, and **all five premise
conjuncts are inhabited by a closed term**, `Refute351.agda:364-370`.

**THE PREMISE IS NOT A DODGE. IT IS CORRECT MATHEMATICS.** The countermodel is a
**one-entry satisfaction table**: the code set holds ONE code, the code of the
constant `bot`; the table gives that code the value `empty`, which is the TRUE
value of `bot`. Eight closure clauses and eleven of the twelve clauses are
vacuous because tag 7 is not their tag. **The twelfth, `botClauseAt` at tag 7,
is satisfied by a real term** (`Refute351.agda:299-308`), not by a refusal.

**THE BRIEF'S PREMISE AT RISK IS MEASURED FALSE, AND BY A TERM.**
**`arityNumAtL` does NOT close `d` and `e`.** `Refute351.agda:424-428` builds
`⟨ γ⁺ ⊨ arityNumAtL (suc zero) ⟩` at a SECOND countermodel, and
`Refute351.agda:414-419` refutes the tie at that same countermodel. The
delivered bound HOLDS there and the tie is still FALSE. **The bound that closed
`[LJ-1.350]`'s tie leaves this one open**, because it bounds the arity component
and this tie's defect is not in the arity component alone.

**THE CONTROL IS ONE ARGUMENT APART, AND IT MEASURES.** `module Point` takes the
code's arity and payload. At `(numeralL 0 , numeralL 0)` the premise is
inhabited AND the first conclusion HOLDS (`Refute351.agda:455-457`). At
`(K , numeralL 0)` and at `(numeralL 0 , K)` the premise is inhabited AND the
first conclusion is REFUTED. **So the premise class is NOT empty and the
refutation measures the SITE, not the statement** (C-42).

**COST.** Eleven agda invocations, longest 12.38 s. **No wall. No heap
exhaustion. The cap was never raised.** Nothing landed in `src/`.

## 1. THE ANSWER TABLE

| claim | verdict | basis |
|---|---|---|
| `graphWitK` is false | **MEASURED FALSE (the tie is refuted)** | `Refute351.agda:408-412`, exit 0 |
| the premise is inhabited | **YES, MEASURED, as a closed term** | `Refute351.agda:364-370` |
| the tie is VACUOUS instead of false | **MEASURED FALSE** | the premise term above, section 3 |
| `arityNumAtL` closes `d` and `e` | **MEASURED FALSE** | `Refute351.agda:414-428`, section 4 |
| `arityNumAtL` closes the FIRST countermodel | **YES, INFERRED** | it bounds the arity; I built no term for the exclusion |
| the countermodel needs a fake code | **MEASURED FALSE** | tag 7 is a real code, and its clause is satisfied by a term |
| the twelve clauses are all vacuous | **MEASURED FALSE** | `botClauseAt` at tag 7 is NOT vacuous, `Refute351.agda:299-308` |
| `closedAt` speaks at tag 7 | **MEASURED FALSE** | `src/L/Coding/Model.lagda.md:2181-2188`, eight tags, none is 7 |
| the conclusion holds at a good argument | **YES, MEASURED** | `Refute351.agda:455-461` |
| the countermodel needs a hand-made `KFacts` | **MEASURED FALSE** | `Refute351.agda:476-504` runs on `KValue.facts` |
| the countermodel needs a carrier member | **MEASURED FALSE** | no extra hypothesis, unlike `[LJ-1.350]`'s `#1∈γ` |
| the shape occurs at more than one statement | **MEASURED FALSE** | section 7, one statement, two sites |
| anything landed in `src/` | **MEASURED FALSE** | section 10 |
| a run hit a wall | **MEASURED FALSE** | longest 12.38 s, section 9 |

## 2. THE TIE, RE-DERIVED TODAY (C-44)

**`graphWitK` is the OUTER name of `SatGraphAgree`'s own `witK` parameter.**

| what | where, today |
|---|---|
| the outer telescope, `graphWitK` | `src/L/Condensation.lagda.md:7288-7297` |
| the module parameter it feeds, `witK` | `src/L/Condensation.lagda.md:7009-7018` |
| the wiring line | `src/L/Condensation.lagda.md:7319-7321` |
| `module SatGraphAgree` | `src/L/Condensation.lagda.md:6961` |
| the OTHER `witK`, already refuted by `[LJ-1.348]` | `src/L/Condensation.lagda.md:7233-7235` |

**The two statements at `:7009-7018` and `:7288-7297` are the SAME statement.**
MEASURED, by reading both.

The environment is `(f ∷ e ∷ d ∷ γ)`. Index 0 is `f`, index 1 is `e`, index 2
is `d`, and index `3 + i` is `γ [ i ]`. The five conjuncts are:

1. `var zero ≐ var (6 + w)`. The carrier slot pins `f`.
2. `closedAt (suc (suc zero))`. The code set `d` is closed.
3. `domAt (suc zero) (suc (suc zero))`. `d` IS the domain of the table `e`.
4. `appAt (suc zero) 4 3`. The table holds the pair of the two free slots.
5. `twelveAt (suc (suc zero)) (suc zero) zero`. The twelve clauses at `d`, `e`
   and `f`.

The conclusion is a TRIPLE: `d ∈ K`, `e ∈ K` and `f ∈ K` (`:7295-7297`).

**MY STATEMENT IS A VERBATIM TRANSCRIPTION**, `Refute351.agda:373-391`. I write
`w K : Fin n` and `γ⁺ : S ^ (3 + n)`; the chapter writes `w K : Fin (5 + m)`
and `γ : S ^ (8 + m)`. **The two agree at `n = 5 + m`, and my statement
quantifies over every `n`, so it is the more general one.** At the delivered
record `n` is 14 and the chapter's `m` is 9, which is a legal instantiation
shape. MEASURED, by reading `KValue.Kenv` at `src/L/Condensation.lagda.md:7389`
and the two telescopes.

## 3. THE PREMISE, INHABITED, AS A TERM

**`Refute351.agda:364-370`.** The term is `premise = pin , (closed , (dom ,
(app , twelve)))`, and every component is built, never assumed.

### 3.1 The countermodel is a correct one-entry table

- **The code**: `cS = prʟ arg (prʟ (numeralL 7) payS)`, `Refute351.agda:196`.
  This is the code of the constant `bot`, at arity `arg` and payload `payS`.
- **The code set**: `dS = sglS cS`, `Refute351.agda:206`.
- **The table**: `eS = sglS (prʟ cS (numeralL 0))`, `Refute351.agda:212`. The
  value at the code is `numeralL 0`, which is the EMPTY set.
- **The two free slots**: the code and that value, `Refute351.agda:219`.

**THE CHAPTER PREDICTS THIS SHAPE.** `src/L/Coding/Graph.lagda.md:71-72` reads
「a table with one entry at a compound code satisfies all twelve, so closedness
and totality are not decoration」. **This probe measures that closedness and
totality are not enough either.**

### 3.2 Conjunct 2, `closedAt`, and why it is vacuous

**`closedAt` speaks at EIGHT tags and none of them is 7.**
`src/L/Coding/Model.lagda.md:2181-2188` reads the eight clauses at tags 2, 3, 4,
5, 8, 9, 10 and 11. **MEASURED, by reading all eight lines.** So a code set whose
only member is a tag-7 code satisfies `closedAt` with no content at all.

The term is `Refute351.agda:250-273`, **22 non-comment lines**. It uses the
chapter's own `binSameClosed-in`, `unSameClosed-in`, `unSuccClosed-in` and
`binSuccClosed-in` (`src/L/Coding/Model.lagda.md:2231-2285`).

### 3.3 Conjunct 5, the twelve, and the ONE clause that is not vacuous

The term is `Refute351.agda:310-357`, **47 non-comment lines**. Eleven clauses
die on the same refusal. **The twelfth does not.**

**`botClauseAt C T = unClauseAt C T 7 (emptyAt zero)`**,
`src/L/Coding/Model.lagda.md:1281-1282`. It demands that the value at a tag-7
code is EMPTY. **The countermodel's value IS empty**, so the clause is
discharged by a real term at `Refute351.agda:299-308`. The term reads the entry
back with `pr-inj`, gets `fst yc ≡ # 0`, and closes `emptyAt` with the library's
`∅-empty`.

**SO THIS IS NOT A VACUOUS-PREMISE REFUTATION.** One of the twelve clauses has
real content at the countermodel, and the countermodel satisfies it.

### 3.4 The one shared refusal

`Refute351.agda:241-248`, **eight lines, used NINETEEN times**. A member of the
code set is the tag-7 code (`pair-only`), so the shape equation gives
`# 7 ≡ # k`, so `#-inj` gives `7 ≡ k`, and `7 ≡ k` is false for the other
eleven tags. **C-58 is honoured: no pattern match of mine splits a numeral
index.** The order helpers at `Refute351.agda:118-123` use the library's `_<_`
and `¬m<m`.

## 4. DOES THE DELIVERED BOUND CLOSE `d` AND `e`? NO. MEASURED

**THE BRIEF NAMED THIS AS ITS PREMISE MOST LIKELY TO BE WRONG. IT IS WRONG.**

`arityNumAtL` (`src/L/Coding/CodeSet.lagda.md:185-188`) says the code is a pair
whose FIRST component lies in omega. **It bounds the ARITY component and
nothing else.**

**MEASUREMENT, BY TWO TERMS AT ONE POINT.**

- `Refute351.agda:405` builds a second countermodel whose arity is
  `numeralL 0`, a genuine numeral, and whose PAYLOAD is the bound `K`.
- `Refute351.agda:424-428` produces `⟨ γ⁺ ⊨ arityNumAtL (suc zero) ⟩` for that
  code, through the delivered `arityNumAtL-in`
  (`src/L/Coding/CodeSet.lagda.md:201-207`).
- `Refute351.agda:414-419` refutes the tie at that same countermodel.

**So the delivered bound holds and the tie is still false. MEASURED.**

**WHY THE SITES DIFFER, AND P-l IS THE REASON.** `[LJ-1.350]`'s tie concluded
`∥ Σ[ n ] (fst ar ≡ # n) ∥₁`, an ARITY conjunct, so an arity bound closed it.
**`graphWitK` has NO arity conjunct.** Its three conclusions are memberships in
`K` (`src/L/Condensation.lagda.md:7295-7297`). MEASURED, by reading the
telescope. `arityNumAtL-out` concludes an EQUATION
(`src/L/Coding/CodeSet.lagda.md:189-192`), never a membership in a slot, so no
composition of it yields `∈ K`.

**WHAT WOULD BE NEEDED INSTEAD.** A bound on the code's PAYLOAD, or a
membership premise on `d` itself. **I did NOT survey whether the tree has
either.** INFERRED, from the two definitions I read, that `closedAt` and
`twelveAt` do not give one.

**ONE HONEST LIMIT.** `arityNumAtL` WOULD exclude my FIRST countermodel, whose
arity is `K` and not a numeral. **INFERRED, not MEASURED: I built no term for
that exclusion**, because the second countermodel already settles the question.

## 5. WHAT THE 120 BECOMES

**`[LJ-1.348]` priced the countermodel at about 120 lines and one to three
runs.** The measured figures:

| what | measured |
|---|---:|
| the whole probe, file lines | **505** |
| the whole probe, non-blank non-comment lines | **270** |
| `module Point`, the premise and the tie, non-comment | **153** |
| the twelve, non-comment | **47** |
| `closedAt`, non-comment | **22** |
| `domAt` plus `appAt` plus the entry readers, non-comment | **21** |
| agda invocations on the countermodel | **10**, of which 7 were red on scaffolding |

**THE PRICE FOR THE LINE COUNT WAS CLOSE AND THE PRICE FOR THE RUNS WAS NOT.**
The 153 lines of `module Point` are the countermodel that `[LJ-1.348]` priced;
about 120 was a good estimate. **The run count was 10 and not 1 to 3**, and
every red was a scoping or a unification failure in the frame, never the
mathematics. **MEASURED.**

**THE 270 BUYS MORE THAN THE 120 ASKED FOR:** two countermodels, one positive
control, and the `arityNumAtL` term. The extra is section 4 and section 6.

**WHAT COLLAPSES THE COST.** `module Point` is generic in the arity and the
payload, so ONE block of 153 lines serves all three points.
`Refute351.agda:177-183` gives two generic descent lemmas, `prFst` and `prSnd`,
which serve both refutation chains.

## 6. THE NEGATIVE CONTROL, AND NON-VACUITY

**THE STANDARD THIS WEEK: THE CONJUNCT HOLDS AT ONE ARGUMENT AND FAILS AT
ANOTHER, ONE ARGUMENT APART, IN ONE FILE.** `module Point` takes exactly two
arguments, and all three instances are in `Refute351.agda`.

| instance | arity | payload | premise | first conclusion |
|---|---|---|---|---|
| `Good` (`:439`) | `numeralL 0` | `numeralL 0` | **inhabited** | **HOLDS**, `:455-457` |
| `Bad1` (`:400`) | **`K`** | `numeralL 0` | **inhabited** | **REFUTED**, `:408-412` |
| `Bad2` (`:405`) | `numeralL 0` | **`K`** | **inhabited** | **REFUTED**, `:414-419` |

**`Good` and `Bad1` differ in ONE argument. `Good` and `Bad2` differ in ONE
argument.** The premise term is the SAME code for all three, because
`module Point` never looks at what the arity or the payload is.

**NON-VACUITY, FOUR LAYERS.**

1. **The premise is a closed term at all three points.** `Refute351.agda:370`.
   Nothing is assumed.
2. **The conclusion HOLDS at the good point.** `Refute351.agda:455-461` proves
   `d ∈ K` and `e ∈ K` there, from `pairK` and the chapter's own `sgltK`
   (`src/L/Condensation.lagda.md:6227-6234`). **A tie that nothing satisfies
   would not do this.**
3. **One of the twelve clauses has real content and is satisfied.** Section 3.3.
4. **THE REFUTATION RUNS ON THE DELIVERED RECORD.** `module Wire`
   (`Refute351.agda:476-504`) opens `KValue`
   (`src/L/Condensation.lagda.md:7380`) at its own frame parameters, takes its
   `facts` record, and produces `live-false` and `live-false-num`. **The five
   closure facts arrive from the chapter and nothing here restates one. This is
   not a parameters-green** (C-45). **AND NO EXTRA HYPOTHESIS IS NEEDED**,
   unlike `[LJ-1.350]`'s `#1∈γ`, because the countermodel never asks the carrier
   for a member.

**I ADDED NO EXPECTED-RED FILE.** The repository's two expected-red probes,
`agents/tasks/LJ-1-344/Supply344.agda` and
`agents/tasks/LJ-1-350/MustFail350.agda`, stay the only ones. **I did not open
either.**

## 7. THE SWEEP (C-42)

**A refutation measures ONE site, so I counted the shape.**

`grep "∧̇ twelveAt" src/` gives **5 hits**, MEASURED:

| site | what it is |
|---|---|
| `src/L/Condensation.lagda.md:7015` | the tie, as `SatGraphAgree`'s `witK` |
| `src/L/Condensation.lagda.md:7294` | the tie, as the outer `graphWitK` |
| `src/L/Condensation.lagda.md:7069` | `body-out`, a CONSUMER, not a tie |
| `src/L/Condensation.lagda.md:7151` | `body-back`, a CONSUMER, not a tie |
| `src/L/Coding/Graph.lagda.md:111` | `satGraphOn`, the definition |

**THE COUNT IS ONE STATEMENT AT TWO SITES.** MEASURED, by reading all five.
`body-out` and `body-back` take the pin premise and give it back in the other
reading; `body-back` TAKES `dK` and `eK` as arguments
(`src/L/Condensation.lagda.md:7154`), which is exactly what this tie was there
to supply. **So the refutation does not extend to a family. It kills one
statement, and that statement has one consumer.**

## 8. DD4, WITH THE AXIS NAMED (C-46)

**THE AXIS IS AC-AGAINST-GCH, fixed at `scripts/measure/ledger.py:50`.**

**EVERY TERM I WROTE IS CLASS-FREE.** MEASURED, by reading the whole file:
`pairS`, `sglS`, `sglK`, `prFst`, `prSnd`, `bad`, `lo`, `hi`, `closed`, `dom`,
`app`, `botC`, `twelve`, `pin`, `premise` and the three points name only `fst`,
`∈`, `lookup`, `pr`, `pr-inj`, `#-inj`, `prʟ`, `numeralL`, `⁅_,_⁆`, `#_`, `∅`,
`arityNumAtL` and five `KFacts` fields. **Not one mentions AC, GCH, a
well-ordering or a cardinal.**

**WHAT THIS TASK CHANGES ON THE SHARED SIDE.** Nothing lands, so no line is
shared or unshared. **What it removes is a FALSE PARAMETER from the shared
side.** `graphWitK` sits in `LeafAgree`'s telescope, which both towers use.
**A repair funded on the belief that this tie is true would have been assumed at
both ends and would have been unsound at both.**

**AND THE PROBE ITSELF IS WRITTEN GENERIC.** `module Refute` takes `w K : Fin n`
and `γ : S ^ n`; `module Point` takes two set arguments. **So the same block
refutes at any frame and at any point**, which is why three points cost one
block.

## 9. SECONDS, LOAD, RUNS

One agda process at a time, always `GHCRTS="-A64m -I0 -M8g"`, **cap NEVER
raised**. `ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l` run before
every invocation: **0 every time, eleven counts, eleven invocations.**

**FLOOR (C-53).** `agents/tasks/LJ-1-351/Floor351.agda`, an empty module:
**0.90 s** first run, **0.65 s** second.

| run | exit | seconds |
|---|---:|---:|
| `Floor351.agda` (first) | 0 | **0.90** |
| `Refute351.agda` (parse, paren count) | 1 | 0.77 |
| `Refute351.agda` (scope, `_+_`) | 1 | 2.61 |
| `Refute351.agda` (scope, `∃[_∶_]`) | 1 | 2.82 |
| `Refute351.agda` (scope, `∃[_∶_]` again) | 1 | 2.71 |
| `Refute351.agda` (`Lift ⊥` against `⊥`) | 1 | 3.07 |
| `Refute351.agda` (unsolved metas, the `rel` slot) | 1 | 12.12 |
| `Refute351.agda` (**first green**) | **0** | **12.24** |
| `Refute351.agda` (**green, with section 4 added**) | **0** | **12.38** |
| `Refute351.agda` (confirm) | **0** | **2.57** |
| `Floor351.agda` (second) | 0 | **0.65** |

**NO INVOCATION CAME NEAR THE 30-MINUTE WALL; the longest was 12.38 s. NO heap
exhaustion. Nothing was interrupted. The cap was never raised.**

**MY FLOOR DISAGREES WITH EVERY SIBLING'S.** `[LJ-1.350]` measured 0.72 s and
`[LJ-1.348]` measured 0.07 s. **MEASURED: no seconds figure of mine is
comparable with any other task's, and I offer none as such.**

**A CACHE WARNING, inherited from four siblings.** My file loads
`L.Condensation`, `L.Coding.Model`, `L.Coding.Graph` and `L.Coding.CodeSet` from
their committed interfaces. **No figure here is a cold check of the chapter, and
none is offered as one.** The 12.38 s against the 2.57 s confirm run is the cost
of elaborating my own 505 lines twice over, not of the chapter.

**THE ONE THING THAT COST TIME WAS THE FRAME, NOT THE MATHEMATICS.** Five of the
seven red runs were scoping. The sixth was the `rel` slot: `binClause-in` takes
the clause relation as an explicit argument, and Agda cannot solve it from the
expected type, because `binClauseAt` reduces before the unifier can invert it.
**The cure is to name the relation**, and three of the twelve relations
(`impRel`, `negRel`, `topRel`) are PRIVATE
(`src/L/Coding/Model.lagda.md:1244`), so those three clauses must go through
`impClause-in`, `negClause-in` and `topClause-in`. MEASURED.

## 10. PROHIBITIONS, ANSWERED

I wrote only inside `agents/tasks/LJ-1-351/`: this report, `Floor351.agda` and
`Refute351.agda`. **`src/` holds no probe of mine and I opened no file under
`src/` for writing.** I READ `src/L/Condensation.lagda.md`,
`src/L/Coding/Model.lagda.md`, `src/L/Coding/Graph.lagda.md`,
`src/L/Coding/CodeSet.lagda.md`, `src/L/Axioms/Basic.lagda.md`,
`src/L/Axioms/Numerals.lagda.md`, `src/L/Constructible.lagda.md`,
`src/V/Coding.lagda.md`, `src/V/Hierarchy.lagda.md`, `src/V/Model.lagda.md`,
`src/FOL/ZFStructure.lagda.md` and `src/FOL/Absoluteness.lagda.md`.

**I READ and IMPORTED `agents/tasks/LJ-1-347/Elim347.agda`**, which is
committed, and edited that directory NOT AT ALL. **I did not open
`agents/tasks/LJ-1-344/Supply344.agda` or
`agents/tasks/LJ-1-350/MustFail350.agda`, both EXPECTED RED, and I repaired
neither.** I did not import `agents/tasks/LJ-1-350/Refute350.agda`, because it
is untracked and a live sibling could move it.

**I did not re-write the four public pair lines.** `Z.pair∈pr` and `Z.b∈pair`
come from `ChainZ` at `src/L/Condensation.lagda.md:2820-2844`, and `sgltK` comes
from `KTies` at `:6227-6234`.

I did not open `src/Everything.lagda.md`, `dev/`, `AGENTS.md` or `.claude/` for
writing. No commit, no push, no `git checkout`, `stash`, `reset` or `clean`.
**No `make check`.** No em dash in any language.
`.venv/bin/python scripts/gate/lint-prose.py --check` and
`.venv/bin/python scripts/gate/lint-agda.py --check` both exit 0.
`.venv/bin/python scripts/dispatch/rules.py --for probe` was run and every
statement was read.

## 11. WHAT I DID NOT SETTLE

- **The REPAIR.** I priced no cure. `[LJ-1.348]` section 5.2 names the field
  that closes the THIRD conclusion, `f ∈ K`, and that field is still the right
  answer for that conclusion. **The first two conclusions need something else
  and I did not find it.**
- **Whether a payload bound exists in the tree.** Section 4. Not surveyed.
- **Whether `arityNumAtL` excludes the FIRST countermodel.** INFERRED yes, no
  term built.
- **`e ∈ K` and `f ∈ K` as separate verdicts.** I refuted the FIRST conclusion
  only. **The tie fails as a whole, so the other two are not needed for the
  verdict**, but I measured neither separately.
- **The consumer's fate.** `body-back` at `src/L/Condensation.lagda.md:7151`
  takes `dK` and `eK` as arguments. **I did not trace who supplies them once
  this tie goes.**
- **The chapter's green with anything landed.** Nothing landed and I ran no
  chapter check.
- **Whether the same countermodel refutes at a frame the chapter really uses
  downstream.** `module Wire` uses `KValue`, which is the chapter's only
  `KFacts` value. **I did not instantiate `SatGraphAgree` itself**, because its
  other fourteen parameters are unavailable.

## 12. ARCHIVE USED (DD18)

One line read per archived file, as the brief orders.

- **`agents/tasks/LJ-1-349/lj-1.349-report.md`, read WHOLE.** **Line read:**
  section 7, 「the `graphWitK` premise (`src/L/Condensation.lagda.md:7288-7296`)
  asks for FIVE things, and the target inhabited only the second」. **TOOK the
  ruling entire and answered it:** all five are now inhabited, and the term is
  `Refute351.agda:364-370`. **TOOK its non-vacuity standard**, which is that a
  refutation is only a refutation where its premise is inhabited, and met it
  four ways in section 6. **CONFIRMED its warning** that `twelveAt` is a
  twelve-clause predicate: eleven clauses are vacuous at tag 7 and the twelfth
  is not, so its worry was well placed and the twelfth is what this probe had to
  build.
- **`agents/tasks/LJ-1-348/lj-1.348-report.md`, sections 1, 2 and 5 read
  WHOLE.** **Line read:** section 5.3, 「`d` carries `closedAt` (`:7290`) and NO
  shapedness at all ... Nothing bounds `d` or `e` above」. **TOOK that reading
  and CONFIRMED it by a term.** **CORRECTED its price:** 「about 120 lines and
  one to three runs」 is right on the lines (153 measured for the countermodel
  block) and MEASURED FALSE on the runs (10). **TOOK its field finding
  unchanged:** the field at `src/L/Axioms/Basic.lagda.md:156-158` still closes
  the third conclusion and I did not re-price it.
- **`agents/tasks/LJ-1-350/lj-1.350-report.md`, sections 2, 3 and 4 read
  WHOLE.** **Line read:** section 3.1, 「It says the code is a pair whose FIRST
  component is in omega」. **TOOK the reading and REJECTED the transfer**, which
  is what P-l orders: that tie's failing conjunct was an arity conjunct, and
  this tie has none. **The rejection is MEASURED by a term**, section 4.
  **TOOK its file layout, its frame and its `KValue` wiring**, which is why this
  probe reached green at all.
- **`archive/dev/TASKS-archived.md`, read the header at `:1-9`.** **TOOK SHAPE
  ONLY:** 「The 264 rows below record every dispatch made on the retired
  route」, a dispatch index kept for which approaches were measured. **REJECTED
  every figure:** that route has a different carrier and no `KFacts` record, so
  no count and no seconds figure from it prices anything here.

## 13. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md`, read `:246-256`.**

**THE ONE LINE THE BRIEF ASKS FOR: a tie concluding a TRIPLE has NO counterpart
in Devlin's text, and it is wholly a port artefact.** `:246-251` says 2.2 to 2.4
write `D(v, u) = "v = Def(u)"` as Σ₁ and then 「bind every unbounded quantifier
by the concrete set `K(u)`」, and `:250-251` calls 「the Σ₀ matrix `C(w, v, u)`
with `w = K(u)`」 the bounded satisfaction substrate.

**THE DECISIVE WORD IS `w = K(u)`.** Devlin FIXES the carrier, and the code set
and the satisfaction table are components of that fixed set BY CONSTRUCTION. **He
never concludes that a code set is in the bound; he builds it there.** Our tie
sets the code set `d` and the table `e` free as the hypothesis's OWN bound
variables, which the chapter's own comment at
`src/L/Condensation.lagda.md:6977-6984` states in English, and then tries to
recover three memberships from closure predicates alone. **This probe measures
that the recovery is impossible.**

**WHY NOT the rest of the digest.** `:240-245` is the `[LJ-1.12]` Δ₀ question,
settled and not about this tie. `:258` onward is Step D, the definable
well-order, which this tie does not reach. **The cardinality halves are another
step, and C-46 forbids using Devlin's tower axis as DD4's.**
