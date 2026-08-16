# LJ-1.352 report: DD25 adversarial review of `[LJ-1.347]`'s conjunct refutation

tier: pi (in-harness-subagent-mode), the switch's ADVERSARIAL row (`herdr` /
`pi` / `glm-5.3`). Written incrementally (C-22). Every negative is MEASURED or
INFERRED, in those words. `src/` untouched; nothing landed, nothing repaired.

## 0. VERDICT

**SPLIT.**

**UPHELD, and re-measured: the conjunct is FALSE, the `m = 0` clause settles,
and the wall is the case split.** `Residue347.agda` re-run, exit 0 in 2.02 s.
`Control347.agda` re-run, exit 0 in 1.52 s. `ControlR347.agda` re-run, exit 42
at `:36.35-36`, the same named line. `Ctl347B.agda` exit 0 in 0.73 s against
`Split347.agda` HEAP EXHAUSTED at 382.95 s under the same 8 GB cap, two files
that differ by the two dispatcher lines. C-58 stands.

**OVERTURNED, by a term I built: the repair reading of section 6.**
`agents/tasks/LJ-1-352/Repair352.agda`, **exit 0 in 2.35 s**, refutes the tie
WITH THE REPAIR'S OWN HYPOTHESIS IN THE TELESCOPE. `[LJ-1.347]` said 「A
container that is shaped cannot be my `⁅ c , c ⁆`」. **MEASURED FALSE: it can.**
My countermodel rotates the tag from 0 to 3, whose relation `noneB` is `⊤̇`
(`src/L/Coding/Shape.lagda.md:175-176`), and `shaped-wS` proves the container
shaped by a closed term while the arity stays the non-numeral singleton. The
live sibling `[LJ-1.350]` reached the same verdict at another site and in a
stronger form (`agents/tasks/LJ-1-350/Refute350.agda`, per-member `ShapeWit`).
**Two refutations, two sites, two tags, one reading dead.**

**CORRECTED, upward: the extent sweep missed two third-shape producer sites.**
`src/L/Condensation/TwelveAgree.lagda.md:161-167` and `:168-173` carry
`TFacts.codesK` and `TFacts.codesK-un` as RECORD FIELDS with the container
`lookup (suc (suc zero)) γ'` and no hypothesis on it. Same directory, same
shape, never named and never disclaimed. The downstream count is SIX, not four.

**THE WORD `[LJ-1.350]` NEEDS: it is not repairing something true, so it is not
stopped by the abort criterion. But its price input is wrong twice: the cure
`[LJ-1.347]` priced is not a cure, and the sweep that priced it is two sites
short.**

| claim under test | verdict | basis |
|---|---|---|
| the conjunct is false, at the delivered record | **YES, MEASURED** | re-run, section 1 |
| the refutation is non-vacuous, three layers | **YES, MEASURED** | section 2 |
| the one-argument-apart control discriminates | **YES, MEASURED** | re-runs, section 3 |
| the count is 24 + 8 producers, 20 consumers, in the chapter | **YES, MEASURED** | my own grep and telescope reads, section 4 |
| the 24 form a chain, not 24 statements | **YES, MEASURED** | all six links read, section 4 |
| the sweep covered the family | **NO. MEASURED: 2 sites missed** | `TFacts`, section 4 |
| `[LJ-1.344]`'s SIX is measured false by it | **YES, MEASURED** | 32 producer declarations by token grep |
| the wall is the pattern-match split | **YES, MEASURED** | re-run, section 5 |
| C-58 is soundly measured | **YES** | the two-line pair reproduces, section 5 |
| shapedness is the missing bound | **NO. MEASURED FALSE** | my `Repair352.agda`, section 6 |
| `[LJ-1.347]`'s repair reading survives `[LJ-1.348]` | **NO. MEASURED FALSE** | section 6 |
| the 「no uniform supplier」 qualifier belongs | **ALREADY THERE, in its own words** | section 2 |
| the about-280-insertions price | **DEAD BASIS, and two sites short** | section 6 |

## 1. THE REFUTATION, RE-RUN AND REBUILT

**RE-RUN.** `agents/tasks/LJ-1-347/Residue347.agda`, exit 0 in 2.02 s, floor
0.80 s cold and 0.05 s warm on this machine. The tie text it refutes is the
delivered text: I read `src/L/Condensation.lagda.md:7239-7245` myself, and the
transcription is exact, including the premise `⟨ fst w' ∈ fst (lookup (suc (suc
(suc K))) γ) ⟩` and the conclusion quadruple. The chapter has not moved since
`[LJ-1.347]` landed: the last commit touching `src/` is `[LJ-1.346]`'s.

**REBUILT, at a different tag.** My `Repair352.agda` imports nothing from any
task directory. It rebuilds the numeral lemma through the library eliminator,
the singleton closure, the countermodel and the wire at `KValue`. Its
countermodel runs at `k := 3` and refutes the tie twice over: once as
delivered, once with the repair hypothesis added (section 6). So the falsity
does not rest on the target's file, its tag choice, or its route.

**ONE PRECISION ON THE INDEX FORM.** `Residue347.Refute` states the tie at a
generic `K : Fin n` rather than at the chapter's `lookup (suc (suc (suc K))) γ`
with `γ : S ^ (8 + n)`. The chapter's form is an instance of the generic one,
so the refutation covers it. `[LJ-1.348]` transcribed both forms verbatim; the
target refutes the generic form and instantiates it at the delivered record.
Adequate, and I say so rather than pretend it is verbatim.

## 2. NON-VACUITY, RE-CHECKED AGAINST `[LJ-1.349]`'s STANDARD

Three layers, all re-read in the file and all live in the exit-0 re-run:

1. **The other conclusions hold at the witnesses.** `other-conjuncts` at
   `Residue347.agda:171-172` is `⟨ fst arS ∈ bnd ⟩ × ⟨ fst u ∈ bnd ⟩ × ⟨ fst u
   ∈ bnd ⟩`, a closed term. Only the arity conjunct dies.
2. **Every premise is a closed term.** `wS∈K`, `cS∈wS` and `codeEq` are built,
   never assumed. I read each one.
3. **It runs on the delivered record.** `Wire` opens `KValue` at its own seven
   parameters and takes the five closure fields from `KV.facts`. The ONE added
   hypothesis is `#1∈γ`, stated at `Residue347.agda` PART 2 with its reason:
   without a non-empty carrier the tie is vacuously true there.

**THE `[LJ-1.349]` QUESTION: is the witness in the intended class?** For
`witK`, `[LJ-1.349]` closed the last escape with a term `intended : ⟨ env ⊨
hasWitnessAt A x ⟩`, because `witK`'s countermodel needed an environment
condition, the read slot holding a shape. **Here the condition is weaker and
the escape is smaller.** `Refute` is generic in `n`, `A`, `K`, `γ` and the five
fields: at EVERY frame where the `KFacts` fields hold and the carrier has a
member, the countermodel runs and the tie is empty. `LeafAgree` has zero
consumers in `src/` (re-measured today by `[LJ-1.349]` section 3, ten hits all
read), so a module parameter must hold at every admissible instantiation or
nothing can use it, and one admissible instantiation kills it. **The target
meets the standard in substance, and meets it more strongly than `witK` did:
its qualifier is the non-empty carrier, and it states that qualifier itself.**
My probe adds the fourth layer the target did not have: `shaped-wS` puts the
witness inside the REPAIRED premise class too (section 6).

**THE SPLIT WORDING THE BRIEF ASKS FOR.** `[LJ-1.349]` added 「no uniform
supplier」 to its sibling's 「MEASURED FALSE」. The same qualifier belongs here
and the target already carries it: its section 4, layer 3, says the tie would be
true at an empty-carrier record. The headline word FALSE is correct for the
statement as written, a module parameter over all instantiations.

## 3. THE ONE-ARGUMENT-APART CONTROL, VERIFIED

`Control347.agda` re-run, **exit 0 in 1.52 s**. One file holds both halves:
`numeral-arity-holds` proves the tie's own last conjunct at the arity element
`numeralL 1`, and `singleton-arity-fails` refutes it at `⁅ # 1 , # 1 ⁆` at
every index.

**THE RED HALF DISCRIMINATES AT THE NAMED LINE.** `ControlR347.agda` re-run,
**exit 42 in 0.83 s**, refused at `ControlR347.agda:36.35-36` with `q` of type
`fst (numeralL 1) ≡ # m` offered where `⁅ # 1 , # 1 ⁆ ≡ # m` is wanted. The
refutation turns on the choice of the arity element and cannot be pointed at a
real numeral. MEASURED.

**TWO PRECISIONS, and neither breaks the control.** First, the target cites
its own file at `:38` and `:42`; the terms sit at `:40` and `:45`. Citation
drift inside its own probe directory, immaterial to the substance. Second, the
positive half exhibits the CONJUNCT at a numeral arity, not a full tie
instance with every premise built. The full instance is the same substitution
the countermodel already makes, with `ar := numeralL 1`, and every conclusion
holds there. The control measures what it claims: the site, not the statement
(C-42).

## 4. THE COUNT AND THE CHAIN, RE-DERIVED

**I re-derived the count by a token sweep the target did not run, then read
the telescopes.** `grep -n "Σ\[ n ∈ ℕ \]" src/L/Condensation.lagda.md` returns
56 tokens. Four are body uses of the ties inside proof terms (`:5887`,
`:5957`, `:6437`, `:6483`, each a local `ks` ascription).
The other 52 are declarations: **32 in `×` position (producers) and 20 in `→`
position (consumers).** That matches the target exactly.

- **Producers, sub-family A, bare `C : S` container: 4.** `BinFormAgree`
  `compK` at `:5834-5839` and `UnFormAgree` `unCompK` at `:5922-5926`, read
  whole: `C : S` is a bare parameter, and no parameter of either module
  constrains it. `ShapesAgree` `compK` `:6268-6273` and `unCompK`
  `:6274-6278`, read whole: same.
- **Producers, sub-family B, `lookup C γ` container: 20.** I read `BotAgree`
  `:2782-2785`, `TopAgree` `:3674-3677`, `ClauseAgree` `:4154-4157`,
  `MemAgree` `:4422-4426`, `ClosedAgree` `:6554-6562`, `ShapedAgree`
  `:6655-6663`, `BinFrameAgree` `:6400-6404`, `UnFrameAgree` `:6448-6451`
  whole, and the remaining eight by grep line and telescope shape
  (`PropAgree :3296`, `AndAgree :3548`, `OrAgree :3603`, `NegAgree :3750`,
  `ForallAgree :3863`, `ExistAgree :3975`, `AllInAgree :5026`, `ExInAgree`
  `:5155`, `ImpAgree :5283`, `EqAgree :5384`). **The container is an index
  into a bare `C` or `γ` parameter in every one I read. Not one hypothesis
  speaks about it.** MEASURED at the ten I read whole, INFERRED for the rest
  from the identical telescope shape.
- **Second shape, container bounded in `K`: 8.** `WitnessAgree` `:6694-6704`
  and `SatGraphAgree` `:6985-6997` read whole: the premise `⟨ fst d ∈ K ⟩`
  bounds the container (`lookup 2 (f ∷ e ∷ d ∷ γ)` is `d`). `LeafAgree`
  `wCodesK :7239-7245`, `wUnCodesK :7246-7251`, `gCodesK :7262-7269`,
  `gUnCodesK :7270-7276`, read whole in section 1.
- **Consumers: 20.** `envK` and `envInK` in ten modules, each TAKING
  `∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁` as a premise: `TopAgree :3682/:3688`,
  `NegAgree :3765/:3771`, `ForallAgree :3878/:3884`, `ExistAgree
  `:3990/:3996`, `ClauseAgree :4172/:4178`, `MemAgree :4435/:4440`,
  `AllInAgree :5049/:5054`, `ExInAgree :5178/:5184`, `ImpAgree
  `:5300/:5306`, `EqAgree :5393/:5398`. I read four of the pairs whole.
  They are the demand, and a deletion repair must answer them.

**So `[LJ-1.344]`'s SIX is MEASURED FALSE by a count I reproduce independently:
32 producer declarations in the chapter.**

**THE CHAIN IS REAL. I read every link.** `LeafAgree:7307` opens `WitnessAgree`
passing `wCodesK wUnCodesK wEntryK`. `WitnessAgree` `:6722` opens
`ClosedAgree` and `:6728` opens `ShapedAgree`, both fed `(codesK w wK)`.
`ShapedAgree` `:6667` and `:6675` open `ShapesAgree {n} (lookup C γ) ... (c ∷
γ) ... codesK unCodesK`, which is where sub-family B meets sub-family A.
`ShapesAgree` `:6289` onward opens `BinFormAgree` and `UnFormAgree` at every
tag, fed `compK j` and `unCompK j`. `ClosedAgree` `:6575` onward opens
`BinFrameAgree` and `UnFrameAgree`, fed `codesK j`. **The ties are threaded,
not independent, and a repair at the top must thread the same way.** The
14 per-connective modules are a second family, instantiated outside the
chapter: I read `LowerAgree:255`, `:262`, `:269` feeding `MemAgree`,
`EqAgree`, `AndAgree` from the record's own `codesK` field.

**AND THE SWEEP MISSED TWO SITES, MEASURED.** `grep -rn "× ∥ Σ\[ n ∈ ℕ \]"
src/` outside the chapter returns `src/L/Condensation/TwelveAgree.lagda.md:167`
and `:172`: `TFacts.codesK` and `TFacts.codesK-un`, RECORD FIELDS at
`TwelveAgree.lagda.md:161-167` and `:168-173`, container `fst c ∈ fst (lookup
(suc (suc zero)) γ')`, an index into the bare record parameter `γ'`, with no
hypothesis on it. **Same third shape.** `TFacts` is consumed by `AbstractFrame`
at `TwelveAgree.lagda.md:342` and has no producer in `src/`, so the field is a
false statement waiting for its first value. **C-42's own precedent is this
case:** the `[LJ-1.172]`/`[LJ-1.173]` sweep found the same disease in three
records, and `TwelveAgree` was the record that made that cure atomic. **The
target swept one file, named two chapters, and never named the third record in
its own directory.** The downstream count is SIX producer sites in THREE
records, not four in two. INFERRED that the countermodel refutes the `TFacts`
fields (identical telescope shape; I built no term at them). MEASURED that they
carry the shape.

**A precision on the method number.** The target says it read 106 parameter
blocks. I count 100 module declarations with parameters in the chapter,
excluding 137 instantiations. The site counts do not rest on either number.

## 5. C-58's TWO DECISIVE CONTROLS, RE-RUN

The brief orders the two that differ by two lines. I diffed them first:
`Ctl347B.agda` and `Split347.agda` differ in comments, module name, and
exactly the dispatcher

```agda
sgl1-not-numeral zero    = zero-clause
sgl1-not-numeral (suc m) = suc-clause m
```

**THE PAIR REPRODUCES.**

| run | exit | seconds |
|---|---|---:|
| `Ctl347B.agda` (no split) | 0 | **0.73** |
| `Split347.agda` (plus the dispatcher) | **HEAP EXHAUSTED** | **382.95** |
| `Elim347.agda` (same split, library eliminator) | 0 | **0.69** |
| `Zero347.agda` (zero clause alone) | 0 | 0.62 |

The heap banner under `GHCRTS="-A64m -I0 -M8g"` is the exhaustion itself:
`Current maximum heap size is 8589934592 bytes (8192 MB)`. The cap was never
raised. The target measured 373.93 s on its machine; I measure 382.95 s on
mine. A factor of about 500 against the no-split control, on a floor of 0.05 s
warm and 0.80 s cold. **The wall is the split. The law is soundly measured,
and its 「do this first」 instruction is the right one.**

**ONE LIMIT I CONFIRM RATHER THAN WIDEN.** C-58 is measured at one index type
(`ℕ`) and one value type (`V`). The target says so; the law text says so. My
rebuild of `sgl1-not-numeral` through `ℕB.elim` checked green first try, which
is the law's practical test passing under a second hand.

## 6. THE SHAPEDNESS CONTRADICTION, SETTLED AGAINST THE TARGET

**THE TARGET'S WORDS, at its section 6:** 「For this conjunct the missing bound
is shapedness ... A container that is shaped cannot be my `⁅ c , c ⁆`, because
`shapedAt` forces every member to be a shape.」

**THE FIRST HALF IS TRUE AND THE CONCLUSION IS FALSE, WHICH IS `[LJ-1.344]`'s
ERROR AGAIN.** `shapedAt` does force every member to be a shape. A shape can
carry the non-numeral singleton in its FREE ARITY SLOT, at any of the twelve
tags, and at tags 2, 3, 4, 5, 8 and 9 the relation is `⊤̇`, so the payload is
free too. `[LJ-1.348]` measured this column by column and `[LJ-1.349]` upheld
it. `[LJ-1.347]` section 6 repeats the refuted inference in a new place.

**I MEASURED IT AT THIS TIE.** `agents/tasks/LJ-1-352/Repair352.agda`,
**exit 0 in 2.35 s**, floor 0.80 s cold:

- **The tie under test** is `wCodesK` with the repair's own hypothesis added:
  `⟨ (w' ∷ γ) ⊨ shapedAt zero (suc A) ⟩`, the same shapedness `witK` carries,
  at the same index form. Everything else as delivered.
- **The countermodel** is the target's rotated one tag: arity `arS :=
  sglS (numeralL 1)`, whose set is `⁅ # 1 , # 1 ⁆`; code `cS := prʟ arS (prʟ
  (numeralL 3) (prʟ u u))`, exactly the tie's pair shape at `k := 3` and
  `a := b := u`; container `wS := sglS cS`.
- **`shaped-wS`** proves the repair's hypothesis by a closed term: every
  member of `wS` is `cS`, and `cS` inhabits the fourth disjunct `BinWit 3
  noneB` of `ShapeWit`, with relation witness `tt*` because `noneB` is `⊤̇`.
- **`wCodesK+-false`** derives `Empty.⊥` from a supplier of the repaired tie,
  and `Wire` runs it at the chapter's own `KValue` record with the one
  hypothesis `#1∈γ`. `numK3` is taken from the same record.
- **The other three conclusions still hold** (`other-conjuncts`), so the
  repaired tie dies at the arity conjunct alone, as before.

**SO THE REPAIR READING IS MEASURED FALSE, TWICE OVER.** My file refutes the
delivered tie at `k := 3` (a supplier of the weaker statement is refuted a
fortiori), and refutes the repaired tie at the same witnesses. **The live
sibling `[LJ-1.350]` refutes the shapedness repair at `ShapesAgree`'s `compK`
in a stronger per-member form** (`agents/tasks/LJ-1-350/Refute350.agda` header,
read; its report is IN PROGRESS and I cite only its file's own statement).
**`[LJ-1.350]'s repair line is sound in direction: it must not be stopped.**
The real bound is the one `[LJ-1.350]` names, `arityNumAtL`
(`src/L/Coding/CodeSet.lagda.md:185-188`), which says the arity component is a
numeral as a formula, and which the tree's own prose already invokes at
`src/L/Condensation/TwelveAgree.lagda.md:302-305`.

**WHAT THIS DOES TO THE PRICE.** The about-280-insertions figure is priced
against a cure that cures nothing; its basis is dead, not merely unmeasured
(P-l). The count it prices is also two sites short (section 4). **A re-price
belongs to `[LJ-1.350]`'s return, not to this review: I priced nothing and
built no repair.**

## 7. SECONDS, LOAD, RUNS (C-53, C-12)

One agda process at a time, always `GHCRTS="-A64m -I0 -M8g"`, cap NEVER
raised. Slot count (`ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`)
run before EVERY invocation, all eleven counts returned 0. A sibling task
(`LJ-1.350`) is live in the tree; no invocation of mine overlapped another
process.

**FLOOR.** `agents/tasks/LJ-1-352/Floor352.agda`, an empty module: **0.80 s
cold, 0.05 s warm.** The target measured 0.48 s and `[LJ-1.348]` measured
0.07 s: the machine keeps changing between tasks, so **no figure of mine is
comparable with the target's, and I offer none as such.** Within this task,
all figures are one machine.

| run | exit | seconds |
|---|---|---:|
| `Floor352.agda` (cold) | 0 | 0.80 |
| `Floor352.agda` (warm) | 0 | 0.05 |
| `Residue347.agda` (re-run) | **0** | **2.02** |
| `Control347.agda` (re-run) | **0** | **1.52** |
| `ControlR347.agda` (re-run, EXPECTED RED) | **42** | **0.83** |
| `Zero347.agda` (re-run) | 0 | 0.62 |
| `Ctl347B.agda` (re-run) | 0 | 0.73 |
| `Elim347.agda` (re-run) | 0 | 0.69 |
| `Repair352.agda` (mine, scope slip, `pr`) | 42 | 1.74 |
| `Repair352.agda` (mine) | **0** | **2.35** |
| `Split347.agda` (re-run) | **HEAP EXHAUSTED** | **382.95** |

**ONE WALL, REPORTED AS A WALL.** `Split347.agda` died at 382.95 s with the
RTS heap banner under the cap. The cap was never raised. No invocation was
interrupted. The seconds deltas below 1 s are under my cold floor and I do not
read them as differences; the beyond-argument deltas are 0.73 s against an
exhausted heap, and green against green at two different tags.

**THE CACHE TRAP, honoured.** Every file loads the chapter from its committed
interface. No figure here is a cold check of the chapter, and none is offered
as one.

## 8. DD4, WITH THE AXIS NAMED (C-46)

**THE AXIS IS AC-AGAINST-GCH, fixed at `scripts/measure/ledger.py:50`.**

**MY PROBE IS CLASS-FREE, MEASURED by reading its names**: `fst`, `∈`,
`lookup`, `pr`, `prʟ`, `numeralL`, `⁅_,_⁆`, `#_`, `∅`, `shapedAt`,
`shaped-in`, `ShapeWit`, `BinWit` and five `KFacts` fields. **Not one mentions
AC, GCH, a well-ordering or a cardinal.** The target's files pass the same
reading, and I confirm its claim.

**SO THE FALSITY HOLDS AT BOTH CARRIERS BY ONE FILE, and now TWO files.** The
tie is a `KFacts`-consumer parameter, generic at both carriers, and a refutation
at one admissible instantiation kills the universal statement at both ends. My
probe is a second, independent one, at a second tag, with the repair
hypothesis in scope. What this review ADDS to the shared side is the cheaper
half: the repaired-and-refuted pair in one file, which any future tower work
can copy to test a proposed bound before threading it down 30 sites.

## 9. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md:246-249`, read.** **The one line the brief
asks for: a 24-site chain of unbounded conjuncts has NO counterpart in
Devlin's text.** His engine 「bind[s] every unbounded quantifier by the
concrete set `K(u)`, the finite sequences over the formula set, the variables
and the members of `u`」, and the Σ₀ matrix runs 「with `w = K(u)`」. Every
quantifier is bound by a set built from its argument; there is no unbound
subject anywhere in the engine, let alone 24 of them chained. The target's
section 12 reading is faithful and I confirm it. **WHY NOT the rest:**
`:241-244` is the settled `[LJ-1.12]` Δ₀ question; `:258` onward is Step D,
which needs a definable well-order no `*Agree` tie reaches; C-46 forbids using
Devlin's tower axis as DD4's.

## 10. ARCHIVE USED (DD18)

One line read per archived file, as the brief orders.

- **`agents/tasks/LJ-1-347/lj-1.347-report.md`, read WHOLE.** **Line read:**
  its section 6, 「A container that is shaped cannot be my `⁅ c , c ⁆, because
  `shapedAt` forces every member to be a shape」. **TOOK** the refutation, the
  bisection and the sweep as the object of review. **REFUTED the section 6
  inference by a term (section 6 here) and corrected the sweep by two sites
  (section 4 here).**
- **`agents/tasks/LJ-1-349/lj-1.349-report.md`, read WHOLE.** **Line read:**
  its section 3, 「NEW, machine-checked: the chapter's own premise is inhabited
  there too ... which closes the reading that the countermodel environments
  are somehow outside the statement's intended range」. **TOOK** the standard
  and applied it in section 2 here. **REJECTED nothing.**
- **`agents/tasks/LJ-1-348/lj-1.348-report.md`, read WHOLE.** **Line read:**
  its section 2, 「SO A TAG-6 SHAPE IS `pr (fst N) (pr (# 6) (# 0))` FOR ANY
  `N` AT ALL, THE BOUND INCLUDED」. **TOOK** the twelve-column reading and the
  shapedness machinery, which my probe rebuilds at tag 3. **REJECTED nothing.**
- **`archive/dev/TASKS-archived.md`, header `:1-6` read.** **Line read:**
  「Archived task index: the `L3.32-T` series」. **TOOK SHAPE ONLY**, a retired
  route's index, read for the practice of naming what a countermodel needs of
  its frame. **REJECTED every figure and every claim:** different carrier,
  different coding, no `KFacts` record.

## 11. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| the arity conjunct is true | **MEASURED FALSE.** Re-run exit 0; my independent tag-3 rebuild |
| the shapedness repair saves the tie | **MEASURED FALSE.** `Repair352.agda`, exit 0, `shaped-wS` |
| the refutation is a parameters-green | **MEASURED FALSE.** `Wire` runs at `KValue`'s own record |
| the refuted premise is empty at the frame | **MEASURED FALSE.** Three layers re-read, section 2 |
| the refutation proves too much | **MEASURED FALSE.** `ControlR347` exit 42 at `:36.35-36` |
| the conjunct is absurd at every arity | **MEASURED FALSE.** `Control347:40`, holds at the numeral |
| the wall is anything but the split | **MEASURED FALSE.** The two-line pair, re-run, section 5 |
| the 24 sites are independent | **MEASURED FALSE.** All six chain links read, section 4 |
| the chapter count is other than 32/20 | **MEASURED FALSE.** My token sweep reproduces it |
| the family ends at four downstream sites | **MEASURED FALSE.** `TFacts` adds two, section 4 |
| the `TFacts` fields are refuted here | **MEASURED FALSE, they are INFERRED false.** Shape read, no term built |
| the target's line citations are all current | **MEASURED FALSE.** Its own `Control347` cites `:38/:42`, terms at `:40/:45` |
| the about-280-insertions price stands | **MEASURED FALSE.** Its basis is the refuted cure; count two short |
| `[LJ-1.350]` must be stopped | **MEASURED FALSE.** The conjunct is false; its direction is confirmed |
| the other seven second-shape sites are refuted | **MEASURED FALSE, INFERRED only.** Same as the target claimed |
| anything landed in `src/` | **MEASURED FALSE.** `git status --short` shows `agents/tasks/LJ-1-352/` only |
| a run exceeded the cap or was interrupted | **MEASURED FALSE.** One exhaustion at 382.95 s under `-M8g` |

## 12. WHAT I DID NOT SETTLE

- **A term at the `TFacts` fields.** Their refutation is INFERRED from the
  identical telescope shape. One file, the same rotation as mine, would settle
  it; it belongs to `[LJ-1.350]`'s sweep or its successor.
- **The re-price of the repair.** The real bound is `[LJ-1.350]`'s
  `arityNumAtL`; its threading price down 38 sites is not mine to name. I
  measured only that the old basis is dead.
- **The twelve consumer slots downstream** (`LowerAgree`/`UpperAgree`
  `:141-174`). The target disclaimed its downstream sweep; I read the producer
  blocks and the instantiations, not the consumer telescopes there.
- **`graphWitK`, `witK`, the red `Supply344.agda`.** Untouched, as ordered.
- **Whether C-58 generalizes past `ℕ` and `V`.** Still one index type, two
  hands.

## 13. PROHIBITIONS, ANSWERED

I wrote only inside `agents/tasks/LJ-1-352/`: this report, `Floor352.agda` and
`Repair352.agda`. **`src/` holds no file of mine and I opened nothing under
`src/` for writing.** I READ `src/L/Condensation.lagda.md`,
`src/L/Condensation/TwelveAgree.lagda.md`, `src/L/Condensation/LowerAgree.lagda.md`,
`src/L/Condensation/UpperAgree.lagda.md`, `src/L/Coding/Shape.lagda.md`,
`src/L/Coding/Model.lagda.md`, `src/L/Coding/EnvSupply.lagda.md`,
`src/FOL/Semantics.lagda.md`, `src/FOL/Syntax.lagda.md` and the cubical
library's `Constructions.agda`. I READ and re-ran probes in
`agents/tasks/LJ-1-347/` and edited that directory NOT AT ALL. I read the live
sibling `agents/tasks/LJ-1-350/` headers and touched nothing there. I did not
open `src/Everything.lagda.md`, `dev/`, `AGENTS.md` or `.claude/` for writing.
A stray empty `_build/352tmp` I created for no reason was removed; `_build/`
holds nothing of mine. **No commit, no push, no `git checkout`, `stash`,
`reset` or `clean`. No `make check`. No em dash in any language.** One agda
process at all times, slots counted before every invocation, cap never raised.
