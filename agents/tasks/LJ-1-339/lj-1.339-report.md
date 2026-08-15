# LJ-1.339 report: the name index of `src/L/Choice/Stage.lagda.md`

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. Recon. It lands
nothing. Written incrementally (C-22).

## THE NUMBER: 10

**TEN of the chapter's 21 top-level exports fail the natural search.** The test
is C-52's own test. Take the concept the term states. Write the search with the
token the REST OF THE TREE uses for that concept. Run it over all of `src/`.
The term fails if the search does not return its declaration line.

**The chapter has 21 top-level exports and 140 non-blank code lines.** MEASURED,
by reading `src/L/Choice/Stage.lagda.md:35-336` whole.

**AND THE BRIEF'S PREMISE IS HALF WRONG, in a way neither option covers.**
The root cause is naming for 9 of the 10. **It is TRIAGE for `ord-suc-inj`, the
one that started this task.** `[LJ-1.335]` ran a search that RETURNED the
declaration, and the report called the term absent anyway. Section 4 gives the
line and the rank.

## 1. THE NAME INDEX. Every top-level export, in file order

**Consumed outside the chapter: 5 of 21. MEASURED**, from the five `using`
lists that import this module. A `using` list is exhaustive, so an export absent
from all five has no consumer by construction.

| # | export | line | what it gives | consumed outside |
|---|---|---:|---|---|
| 1 | `meets` | 95 | `u` has a member in `Lset σ`, as an `Ω` | no |
| 2 | `Inhabited` | 98 | `u` has a member, truncated | no |
| 3 | `meetsSome` | 101 | some ordinal stage meets an inhabited `u` | no |
| 4 | `theEarliestMeet` | 123 | the `LeastOrd` record for `meets u` | no |
| 5 | `μ` | 127 | the earliest stage that meets `u`, sealed | no |
| 6 | `μ-ord` | 132 | `μ u` is an ordinal | no |
| 7 | `μ-meets` | 135 | `μ u` meets `u` | no |
| 8 | `μ-earliest` | 138 | no smaller ordinal meets `u` | no |
| 9 | `IsPredOf` | 169 | `δ` is an ordinal and `sucV δ ≡ σ` | **yes**, Step:56 |
| 10 | `meet-suc` | 181 | the least meeting stage has a predecessor, truncated | no |
| 11 | `ord-suc-inj` | 239 | `sucV` is injective on ordinals | **yes**, Faithful:53 |
| 12 | `isPropPredOf` | 250 | `Σ δ, IsPredOf σ δ` is a proposition | **yes**, Step:56 |
| 13 | `thePred` | 255 | the predecessor of `μ u`, as data | no |
| 14 | `defStage` | 261 | the stage `u` is first defined over, sealed | no |
| 15 | `defStage-ord` | 266 | `defStage u` is an ordinal | no |
| 16 | `defStage-suc` | 270 | `sucV (defStage u) ≡ μ u` | no |
| 17 | `Lset-μ` | 286 | `Lset (μ u) ≡ 𝒟ₒ (Lset (defStage u))` | no |
| 18 | `stage-below` | 318 | a member of `a` lies in `Lset (stage a p)` | no |
| 19 | `stage-below₂` | 323 | the same, two levels down | no |
| 20 | `stageBound` | 328 | an ordinal above `ω` and above `stage a p` | **yes**, Cardinal:23, Order:53 |
| 21 | `bound-below₂` | 332 | two levels down lands in `Lset` of that bound | **yes**, Transversal:61 |

**The five importers, MEASURED**, at `file:line`:

- `src/L/Cardinal.lagda.md:23` takes `stageBound`;
- `src/L/Choice/Order.lagda.md:53` takes `stageBound`;
- `src/L/Choice/Transversal.lagda.md:61` takes `bound-below₂`;
- `src/L/Choice/Faithful.lagda.md:53` takes `ord-suc-inj`;
- `src/L/Choice/Step.lagda.md:56` takes `IsPredOf` and `isPropPredOf`.

**SIXTEEN EXPORTS HAVE NO CONSUMER OUTSIDE THE CHAPTER. MEASURED.** Section 3
says why fourteen of them are dead, and it is not a naming problem.

## 2. THE TEN THAT FAIL A NATURAL SEARCH

Each row names the concept, the search, and the measured result. Every search
ran over the whole of `src/` with `grep -rn --include='*.lagda.md'`.

| # | export | the search a reasonable agent runs | result |
|---|---|---|---|
| 1 | `ord-suc-inj` | `sucV-inj`, because the tree writes `<op>-inj` | **0 hits. MEASURED** |
| 2 | `IsPredOf` | `IsSuc\|isSucc\|IsSucc` | **0 hits. MEASURED** |
| 3 | `isPropPredOf` | `isPropIsSuc\|isPropSuc` | **0 hits. MEASURED** |
| 4 | `thePred` | the same successor tokens | **0 hits. MEASURED** |
| 5 | `Inhabited` | `nonempty\|NonEmpty`, the tree's own word | **26 hits, none this. MEASURED** |
| 6 | `defStage` | `birth`, the tree's other name for it | **0 hits in this file. MEASURED** |
| 7 | `defStage-ord` | `birth-ord` | **0 hits in this file. MEASURED** |
| 8 | `defStage-suc` | `birth-suc` | **0 hits in this file. MEASURED** |
| 9 | `stage-below` | `Lset-trans`, the tree's name for the idiom | **0 hits in this file. MEASURED** |
| 10 | `stage-below₂` | `Lset-trans` | **0 hits in this file. MEASURED** |

### 2.1 Rows 1 to 4: the successor family has no conventional token

**`IsSuc`, `isSucc` and `IsSucc` return ZERO lines in all of `src/`. MEASURED.**
So does `IsLimit`, `isLimit`, `limit-or` and `suc-or-lim`. The tree has no word
for successor-hood at all. This chapter's word is `Pred`, with a capital `P`,
inside `IsPredOf`, `isPropPredOf` and `thePred`.

**THE CAPITAL LETTER IS LOAD-BEARING.** `[LJ-1.335]:281` ran `pred\b`, which is
case sensitive. It cannot match `Pred`. **`ord-suc-inj` is the same shape of
miss:** the tree writes `<operation>-inj` at 15 sites, the operation is `sucV`,
and the delivered name drops the `V` and adds an `ord-` prefix.

**The 15 declared names ending in `-inj`, MEASURED, at top level in `src/`:**
`code-inj`, `pr-inj`, `pair-inj`, `prʟ-inj`, `pairω-inj`, `tcode-inj`,
`mkTag-inj`, `numeralL-inj`, `numeralω-inj`, `fin-inj`, `shape-count-inj`,
`finite-stage-inj`, `numeral-into-ω-inj`, `no-inj-finite-ω` and `ord-suc-inj`.

**THIRTEEN of the 15 open with the operation and close with `-inj`.**
`no-inj-finite-ω` is a negation and follows a different pattern. **`ord-suc-inj`
is the only injectivity lemma in `src/` that puts a qualifier before its
operation, and it also drops the `V` from `sucV`.** Two departures in one name,
and either one alone defeats the search.

### 2.2 Rows 6, 7 and 8: TWO DELIVERED NAMES FOR ONE CONCEPT

**`defStage u` and `birth x` are the same construction.** Both take the earliest
stage of a thing, prove that stage is a successor, and extract the predecessor.
`defStage` does it for a cell at `:255-272`. `birth` does it for a set at
`src/L/Choice/Step.lagda.md:128-142`.

**THE CHAPTER THAT REBUILT IT SAYS SO ITSELF**, at
`src/L/Choice/Step.lagda.md:90`:

> The argument applies verbatim to a single set, and for the same reason.

**So a search for either name misses the other. MEASURED:** `birth` returns 0
lines inside `src/L/Choice/Stage.lagda.md`, and `defStage` returns 0 code lines
inside `src/L/Choice/Step.lagda.md`. The two prose mentions at Step `:148` and
`:163` are the only link, and they are prose.

### 2.3 Rows 9 and 10: the wrapper hides the idiom

**`stage-below` is `layer-trans (Lset-layer ...)` with the stage filled in.**
The tree writes that idiom inline at **19 sites in 12 files. MEASURED.** It also
names it once, as `Lset-trans′` at `src/L/Coding/Bound.lagda.md:127-128`. **So
the concept has a delivered name, and it is not `stage-below`.**

### 2.4 The eleven that PASS, and why

`meets`, `meetsSome`, `theEarliestMeet`, `μ`, `μ-ord`, `μ-meets`, `μ-earliest`,
`meet-suc`, `Lset-μ`, `stageBound` and `bound-below₂` all pass.

**`meets` reaches 18 lines of the chapter and `earliest` reaches 7. MEASURED.**
`theEarliestMeet` sits in the same `theEarliest` grep as `L.Stage`'s `stage`
block, so an agent that finds one finds both. `stageBound` and `bound-below₂`
answer to `[Bb]ound`, which reaches 11 lines of the chapter.

**`μ` is a single Greek letter, and it still passes.** MEASURED: `μ` occurs in
exactly TWO files of `src/`, this chapter and the catalog. A token search for
`μ` is therefore useless, but nobody needs one: `leastOrd`, `meets` and
`earliest` all land inside the block, two lines above the seal.

## 3. THE DD4 FINDING THE SEARCH TEST DID NOT PREDICT

**FOURTEEN of the 16 unconsumed exports are the `μ` and `defStage` apparatus.**
Numbers 1 to 8, 10, and 13 to 17 of section 1. **Nothing in `src/` reads any of
them. MEASURED.**

**AND `L.Choice.Step` REBUILT THE HALF IT NEEDED.** It imports only `IsPredOf`
and `isPropPredOf`, which are the propositional half. It then writes
`decideSuc`, `atCarve`, `theCarve` and the `birth` seal at `:106-142`, **32
non-blank code lines**, against this chapter's `below-case`, `same-case`,
`meet-suc`, `thePred` and the `defStage` seal, **45 non-blank code lines**.

**Both call `suc∈or≡`, `Lset-suc`, `mem-ord` and `Lset-out`. Both close on
`isPropPredOf`.** The only difference is the property and the minimality
witness. **So the operation was never written generic, and the second site paid
32 lines to say the same thing.** That is DD4's own failure mode, at a chapter
this leg has now visited three times.

**THE HALF THAT DID WORK, and it is worth saying.** `theEarliestMeet` and
`theEarliest` (`src/L/Stage.lagda.md:176`) ARE two instances of one generic
operator, `leastOrd`. **That operator carried its second instance at one line**,
which is what the chapter's own prose at `:79-81` claims. **So the project
already knows how to do this. The successor extraction is where it stopped.**

## 4. THE ROOT CAUSE. Not naming, and not placement, for the one that matters

**`[LJ-1.335]` ran THREE searches at `:279-282`, and `[LJ-1.337]` diagnosed only
the FOURTH, at `:298`.** The fourth is `isPropInit|sucV-inj|sucV-injective`.
**MEASURED: it returns 0 lines, and `[LJ-1.337]`'s reading of it is correct.**

**THE SECOND SEARCH RETURNED THE DECLARATION.** `[LJ-1.335]:281` ran

```
grep -rn "≡ sucV\|pred\b\|predecessor" src/
```

**MEASURED, re-run today: 59 lines. Line 55 of that output is**

```
src/L/Choice/Stage.lagda.md:239:ord-suc-inj : (δ δ' : S) → IsOrd δ → sucV δ ≡ sucV δ' → δ ≡ δ'
```

**The pattern `≡ sucV` matches the middle of `sucV δ ≡ sucV δ'`.** Three more
lines of the same chapter came back with it, at `:212`, `:215` and `:216`, and
one of them reads「So being the predecessor of a given ordinal is a
proposition」. **That sentence describes `isPropPredOf`, the second find.**

**`[LJ-1.335]:282` then wrote「Every hit is a different subject」and named three
of the 59.** So the record shows a search that hit, an output that was not read
to the end, and a MEASURED ABSENT written on top of it.

### 4.1 Naming or placement, with the count the brief asked for

**PLACEMENT IS NOT THE ROOT CAUSE, and one measurement settles it.** Every
failed search in section 2 is a `grep -rn` over the whole of `src/`. **A
whole-tree grep is directory blind.** No directory could have saved any of
them, and no move would have changed one result.

**THE COUNT, since the brief asks for it: 3 of 21 exports are pure ordinal
arithmetic, at 24 of the chapter's 140 code lines.** They are `IsPredOf`
(`:169-170`), `ord-suc-inj` (`:239-248`) and `isPropPredOf` (`:250-253`), plus
the two private helpers `cycle₂` and `mem-branch` at `:230-237`. **MEASURED:
none of the five names `Lset`, `isL`, `meets`, `stage` or any tower object.**
The other 18 exports all do.

**So the chapter is 17 percent ordinal arithmetic by export count and 17 percent
by line count.** That is a real misfiling, and it costs a reader who BROWSES.
**It cost this leg nothing, because this leg grepped.**

**A MOVE IS NOT WARRANTED ON THIS EVIDENCE, and I say what would change that.**
Twenty-four lines is a small move with a real cost: `L.Choice.Stage` would then
import its own ordinal facts back, and `check-rule-ids` and the catalog both
carry the chapter's description. **What would warrant it: a THIRD consumer of
`ord-suc-inj` outside `L/Choice/`.** Today there is one, at
`src/L/Choice/Faithful.lagda.md:53`.

### 4.2 THE CURE THAT WOULD HAVE WORKED, and it is cheap

**A name index is not the cure. A CONSUMER index is.** Nine of the ten failing
searches would have succeeded against a generated table of every top-level
export with its type. **The tenth, `ord-suc-inj`, needed no tool at all: its
declaration was on the searcher's own screen.**

## 5. THE ABSENT-CLAIMS OF THIS LEG, EACH TESTED AGAINST THIS CHAPTER

| claim | source | verdict against this chapter |
|---|---|---|
| `sucV` injectivity is absent | `[LJ-1.335]:297-301` | **REFUTED.** `ord-suc-inj`, `:239`. Re-confirmed; `[LJ-1.337]` machine-checked it |
| the propositionality it buys is absent | `[LJ-1.335]:297-302` | **REFUTED.** `isPropPredOf`, `:250` |
| `isProp (Init δ)` is absent | `[LJ-1.335]:299`, `[LJ-1.337]:37` | **CONFIRMED.** MEASURED: `Init` occurs 0 times in the chapter |
| a successor-or-limit dichotomy is absent | `[LJ-1.335]:278`, `[LJ-1.332]:383-385` | **CONFIRMED.** MEASURED: `IsLimit`, `isLimit`, `IsSucc`, `isSucc`, `Split` and `⊎` all occur 0 times in the chapter |
| successor monotonicity on ordinals is absent | `[LJ-1.332]:125-128`, marked INFERRED there | **NOT IN THIS CHAPTER. MEASURED.** See 5.1 |
| the canonical decomposition of `ω + ω` is absent | `[LJ-1.332]:125-128` | **CONFIRMED for this chapter. MEASURED:** the chapter names no ordinal sum |
| `Init` against `IsCardinal` is unmeasured | `[LJ-1.330]:339-343` | **NOT IN THIS CHAPTER. MEASURED:** neither name occurs |

**The chapter holds NEITHER form of the dichotomy.** `meet-suc` at `:181` is
close enough to mislead and it is not the same statement. It says the least
stage MEETING a given cell has a predecessor, and it returns a TRUNCATION. **It
is a fact about one cell, not a classification of ordinals.** `[LJ-1.337]`'s
reading is correct and I add nothing to it.

### 5.1 One free find, outside my scope, offered with its caveat

**`[LJ-1.332]:125-128` said successor monotonicity was needed and NOT built, and
it marked that INFERRED.** D-10 says price the truth of a residue, so I ran the
search.

**`suc∈or≡` is delivered at `src/L/Ordinal/Stages.lagda.md:137`:**

```agda
suc∈or≡ : (β α : S) → IsOrd β → IsOrd α → ⟨ β ∈ˢ α ⟩
        → ⟨ sucV β ∈ˢ α ⟩ ⊎ (sucV β ≡ α)
```

**It has FIVE consumers today. MEASURED:** `src/L/BoundedSubset.lagda.md:878`,
`src/L/Choice/Step.lagda.md:53`, `src/L/Choice/Stage.lagda.md:51`,
`src/L/Choice/Faithful.lagda.md:50`, and the chapter itself.

**THE CAVEAT, and it is a real one.** This is the disjunctive form, not
`β ∈ α → sucV β ∈ sucV α`. **I did not typecheck any application of it to the
`ω + ω` question, and I claim no such application.** What I claim is narrow:
**the residue「successor monotonicity is not built」was never searched with the
token the tree uses, and the tree's token is `suc∈or≡`.**

## 6. DD4, STATED AND ANSWERED, WITH THE AXIS (C-46)

**DD4: maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker. **The axis is AC against GCH**, fixed at
`scripts/measure/ledger.py:50` and declared at `dev/ledger.toml:170` and `:218`.

**THE CHAPTER IS IN BOTH TROPHY CLOSURES. MEASURED**, by an import-graph walk
from the two declared roots, `src/L/Model.lagda.md` and `src/L/GCH.lagda.md`,
run with no Agda.

**HOW MANY EXPORTS THE GCH SIDE USES TODAY: THREE.**

| export | consumer | that consumer's side |
|---|---|---|
| `stageBound` | `src/L/Cardinal.lagda.md:23` | **GCH only** |
| `IsPredOf` | `src/L/Choice/Step.lagda.md:56` | **BOTH** |
| `isPropPredOf` | `src/L/Choice/Step.lagda.md:56` | **BOTH** |
| `ord-suc-inj` | `src/L/Choice/Faithful.lagda.md:53` | AC only |
| `bound-below₂` | `src/L/Choice/Transversal.lagda.md:61` | AC only |

**So 3 of 21 exports reach the GCH trophy, and 2 more reach only the AC one.**
`src/L/Cardinal.lagda.md` is in the GCH closure and NOT the AC one. MEASURED.
**That single edge is the DD4 success nobody counted: an AC-machinery chapter
supplying the GCH descent's cardinal chapter.**

**HOW MANY MORE COULD: at least THREE, and I name them.** `ord-suc-inj`,
`IsPredOf` and `isPropPredOf` are the pure ordinal facts of section 4.1.
**`[LJ-1.337]` already re-derived two of them inside a GCH-side probe**, at
`agents/tasks/LJ-1-337/ProbeLJ1337A.agda`, PARTS 1 and 2, **24 lines**. **So the
demand is measured and it is live.**

### 6.1 A CORRECTION to a live recommendation, MEASURED

**`[LJ-1.337]:200-204` recommends keeping a 13-line duplicate `sucV-inj` to
「pay ZERO new masters」.** Its basis is at `:196-198`: the closure of
`L.Ordinal.SquareLaw` grows from 26 masters to 30 with the new import edge.

**MEASURED: that is a LOCAL closure figure, and the trophy figure is ZERO.**

| question | measured |
|---|---|
| `L.Ordinal.SquareLaw` closure today | 26 masters |
| with an edge to `L.Choice.Stage` | 30 masters |
| **GCH trophy closure today** | **48 masters** |
| **GCH trophy closure with that edge** | **48 masters** |

**All four entering masters are ALREADY in both trophy closures. MEASURED:**
`L.Choice.Stage`, `L.Ordinal.Stages`, `L.Rank` and `L.Stage` each return
`AC=True GCH=True`. **So the edge adds no file to either trophy and no line to
the DD4 report.**

**THE HONEST HALF, and I mark it INFERRED.** The four masters would become new
PREREQUISITES for `L.Ordinal.SquareLaw`'s own check, which could change the
build order and the incremental check cost. **I measured no second of that, and
P-l forbids me from pricing it by analogy.** The orchestrator now chooses
between 13 duplicated lines and an edge that costs zero masters and an unknown
number of seconds.

**The standing DD4 report, quoted from the tool and not from a paragraph:**
AC closure 73 masters and 17,197 lines; GCH closure 48 masters and 8,889 lines;
shared 43 masters and 7,596 lines, at 41.1 percent of the union.

## 7. WHAT I DID NOT SETTLE

1. **Whether the 14 dead exports should be retired.** DD13 prices a retirement
   from the rewrite side, and I did not price the rewrite. **I measured only
   that nothing reads them.**
2. **Whether `defStage` and `birth` should become one generic operation.** I
   measured the duplication at 32 lines against 45. **I did not write the
   generic form and I do not know its line count.**
3. **The check cost of anything.** I ran no Agda. **Every figure here is a line
   count, a grep count or a graph walk.**
4. **The other chapters.** C-42 binds: I swept ONE chapter, as the brief
   ordered. **The `<op>-inj` convention holds at 14 of 15 sites, so I claim no
   count of similar misses elsewhere.**
5. **Whether `suc∈or≡` closes `[LJ-1.332]`'s ordinal gap.** Section 5.1 states
   the caveat. **I typechecked nothing.**

## 8. ARCHIVE USED (DD18), ONE LINE READ PER FILE

- **`agents/tasks/LJ-1-337/lj-1.337-report.md`, READ WHOLE.** Line read `:518`:
  「The two false negatives I found were both in `src/L/Choice/Stage.lagda.md`,
  which suggests that chapter is worth one sweep」. **TOOK: the target, and both
  finds, which section 5 re-confirms. CORRECTED: its diagnosis at `:39-42` names
  the filter at `[LJ-1.335]:298` and is right about that filter; the filter at
  `[LJ-1.335]:281` returned the declaration, and section 4 measures it.**
- **`agents/tasks/LJ-1-335/lj-1.335-report.md`, READ `:270-330`.** Line read
  `:282`:「Every hit is a different subject」. **TOOK: the three filters
  verbatim, and I re-ran all three. REFUTED: the second returns 59 lines, and
  line 55 is the declaration the report called absent.**
- **`agents/tasks/LJ-1-330/lj-1.330-report.md`, READ for its absent-claims.**
  Line read `:339-343`:「Whether `Init` is equivalent to `IsCardinal`. I did not
  measure the gap」. **TOOK: the claim, and section 5 tests it against this
  chapter. It is not here.**
- **`agents/tasks/LJ-1-332/lj-1.332-report.md`, READ for its absent-claims.**
  Line read `:125-128`:「that `+ω ω` is a LIMIT and that it fails `Init`. I
  built neither. The first needs successor monotonicity on ordinals」. **TOOK:
  the residue, and section 5.1 prices its truth with `suc∈or≡`.**
- **`archive/dev/TASKS-archived.md`, SHAPE ONLY, never a claim.** Line read
  `:60` (L3.32-T25):「Bridge's successor hypothesis, gated | SPLIT」. **TOOK,
  SHAPE ONLY: the retired route also scattered its successor facts, and its
  dispatch came back SPLIT. WHAT WOULD NOT TRANSFER: that route's ordinal
  chapter is `L/Rud/OrdArith`, a name the live tree does not have, and every
  figure of that dispatch lives in `_build/`, which is temporary. I quote
  none.**

## 9. LITERATURE USED (DD18)

**No mathematical literature bears on where a delivered lemma is named.** The
question is a naming and a search question about this tree. **I read no source
and I cite none.**

## 10. PROHIBITIONS, ANSWERED

- **Writes: `agents/tasks/LJ-1-339/` only.** One file, this report. **Nothing in
  `src/`, nothing in `dev/`, no other task directory, no `.claude/`, no
  `AGENTS.md`.** One helper script sits in the session scratchpad, outside the
  repository.
- **I MOVED NOTHING and I LANDED NOTHING.** `git status` shows one new file.
- **I RAN NO AGDA.** The brief allows it to confirm a type, and no answer here
  needed one. **So I counted no slots, because I started no process.**
- **No commit, no push, no `make check`.** No `git checkout`, `stash`, `reset`
  or `clean`.
- **I read the four sibling task directories and changed no line of any.**
- `.venv/bin/python scripts/dispatch/rules.py --for recon`: run, every statement
  read. I opened the full `dev/LESSONS.md` entries for D-10, C-42, C-44, C-52,
  C-46 and D-1.
- `.venv/bin/python scripts/gate/lint-prose.py --check` on this report: reported
  in section 11.
- **MEASURED: no em dash in this file.**

## 11. THE ABORT CRITERION, ANSWERED ROW BY ROW (D-1)

| the brief's row | outcome |
|---|---|
| **THE CHAPTER HOLDS MORE THAT THE TREE MISSES** | **TAKEN. TEN exports fail the natural search, and section 2 gives each failing search.** Nine are new |
| **THE TWO WERE ALL OF IT** | **NOT TAKEN** |
| **THE ROOT CAUSE IS PLACEMENT** | **NOT TAKEN, and MEASURED false for the one that matters.** Every failed search was a whole-tree grep, which is directory blind. **The count the row asks for: 3 of 21 exports and 24 of 140 lines are pure ordinal arithmetic** |
| **A WALL** | **NOT TAKEN** |

**AND A ROW THE BRIEF DID NOT HAVE: THE ROOT CAUSE IS TRIAGE.** For
`ord-suc-inj`, the search hit and the reader stopped at line 3 of 59.
