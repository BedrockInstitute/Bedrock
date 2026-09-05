# LJ-1.347 report: the arity numeral conjunct is FALSE, and the wall was the case split

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. Written
incrementally (C-22). Every negative is MEASURED or INFERRED, in those words.

## 0. LEAD

**FALSE.** `[LJ-1.344]`'s INFERRED verdict is now **MEASURED**.
`agents/tasks/LJ-1-347/Residue347.agda`, **exit 0 in 3.16 s**, refutes `wCodesK`
at the chapter's own delivered `KValue` record, with non-vacuity in three layers.

**THE `m = 0` CLAUSE IS SETTLED**, `agents/tasks/LJ-1-347/Zero347.agda`, **exit 0
in 1.51 s**, against four runs interrupted at 330 s, 400 s, 160 s and 300 s.

**AND THE WALL WAS NOT WHERE ANYBODY LOOKED.** `[LJ-1.344]` varied the ROUTE
twice and read the cost as 「refusing `# 1 ∈ # 0` at concrete numerals」. **That
reading is MEASURED FALSE.** The explosive sub-term is the **PATTERN MATCH CASE
SPLIT on the numeral index**. Two files that differ by **two lines** measure
**1.73 s against an exhausted 8 GB heap**. C-56 called it: the cost was in the
assembly.

**THE THIRD SHAPE IS NOT TWO SITES. IT IS TWENTY FOUR**, inside
`src/L/Condensation.lagda.md` alone, and four more downstream. Section 5 names
every one. `[LJ-1.344]` wrote 「the arity-numeral family has SIX occurrences,
not four」. **That is MEASURED FALSE: the family has 32 producer sites in the
chapter and 20 consumer slots.**

## 1. WHICH SUB-TERM EXPLODES. The bisection, five controls

| file | what it holds | exit | seconds |
|---|---|---:|---:|
| `Floor347.agda` | empty module | 0 | **0.48** |
| `Zero347.agda` | `m = 0` clause alone, smallest imports | 0 | **1.51** |
| `Ctl347A.agda` | `m = 0` clause alone, FULL imports | 0 | **1.70** |
| `agents/tasks/LJ-1-344/Bisect344B.agda` | `suc m` clause alone | 0 | 2.01 |
| `Ctl347B.agda` | **BOTH clauses, no case split** | 0 | **1.73** |
| `Split347.agda` | `Ctl347B.agda` **plus a two line dispatcher** | 251 | **373.93, HEAP EXHAUSTED** |
| `Full347.agda` | both clauses inlined in one case split | 251 | **406.01, HEAP EXHAUSTED** |
| `Elim347.agda` | the same split through the library eliminator | 0 | **1.64** |

**`agents/tasks/LJ-1-347/Ctl347B.agda` and `agents/tasks/LJ-1-347/Split347.agda`
differ by exactly these two lines** (`Split347.agda:77-78`):

```agda
sgl1-not-numeral zero    = zero-clause
sgl1-not-numeral (suc m) = suc-clause m
```

**1.73 s against an exhausted heap. That is the sub-term, MEASURED.**

**FIVE CANDIDATES ARE MEASURED INNOCENT, each by its own control.**

| candidate | verdict | control |
|---|---|---|
| the numeral `# 0`, or the subst into it | **MEASURED innocent** | `Zero347.agda`, exit 0, 1.51 s |
| the import set, `V.Coding` included | **MEASURED innocent** | `Ctl347A.agda`, exit 0, 1.70 s |
| the route: `empty-spec` against regularity | **MEASURED innocent** | a THIRD route walls too, `Full347.agda` |
| inlining the clause bodies | **MEASURED innocent** | `Split347.agda` walls with them named |
| the two clauses coexisting in one module | **MEASURED innocent** | `Ctl347B.agda`, exit 0, 1.73 s |

**WHY THE ROUTE WAS NEVER THE QUESTION.** `[LJ-1.344]` wrote that 「one route
transports along an hProp path (`empty-spec`); the other forces the accessibility
of `# 1`; both fail」and read that as evidence about concrete numerals. **My
route E uses NEITHER.** The cubical library exports the refusal as a plain
FUNCTION, `∅-empty` at
`/opt/homebrew/Cellar/agda/2.8.0-r3/share/agda/cubical/Cubical/HITs/CumulativeHierarchy/Constructions.agda:86`,
and `# zero = ∅` is a DEFINING equation at `:164` of the same file, so the subst
lands in the empty set by conversion and costs nothing. **Route E still walls
under the case split, and still returns in 1.51 s without it.** All three routes
were sound. The split was the cost.

## 2. THE CURE, MEASURED

**Split by the library eliminator, not by a pattern match**
(`agents/tasks/LJ-1-347/Elim347.agda:75-78`):

```agda
sgl1-not-numeral =
  ℕB.elim {A = λ k → ⁅ # 1 , # 1 ⁆ ≡ # k → Empty.⊥}
    zero-clause (λ m _ → suc-clause m)
```

**Exit 0 in 1.64 s.** The coverage check then happens once, inside
`/opt/homebrew/Cellar/agda/2.8.0-r3/share/agda/cubical/Cubical/Data/Nat/Base.agda:37-42`,
at a motive that mentions no set. **Nothing else changed between
`Split347.agda` and `Elim347.agda`:** same imports, same two clause bodies, same
helper definitions.

**A LAW CANDIDATE, with its measurement.** I propose it and I do not number it;
the orchestrator assigns the ID (owner's delegation, 2026-08-06).

> **A pattern match case split on a numeral index that a `V`-valued recursive
> function reads in a later argument's type exhausts the heap. The library
> eliminator at the same split is free.** MEASURED at
> `agents/tasks/LJ-1-347/Split347.agda` (heap exhausted at 373.93 s) against
> `agents/tasks/LJ-1-347/Elim347.agda` (exit 0 at 1.64 s), two files that differ
> only in HOW the split is written. Each clause is green alone
> (`Ctl347B.agda`, 1.73 s). **This is P-i's class and R-40's family, and neither
> names the split.** The empty-file floor is 0.48 s, so the 373 s is not near
> any floor.

## 3. THE VERDICT ON THE CONJUNCT: FALSE, MEASURED

**`agents/tasks/LJ-1-347/Residue347.agda`, exit 0 in 3.16 s.**

**THE TIE**, `src/L/Condensation.lagda.md:7239-7245`. **Note the line numbers
moved:** the brief cites `:7130-7136`, which `[LJ-1.346]` shifted by 109 lines
when it landed `KTies`. I read the current text and quote it.

**THE PREMISE READING HOLDS, RE-MEASURED.** `wCodesK`'s telescope carries
`⟨ fst w' ∈ fst (lookup K γ) ⟩` and `⟨ fst c ∈ fst w' ⟩` and the pair equation,
and **NO shapedness**. `closedAt` and `shapedAt` stand in `witK`'s premise at
`:7233-7234` and NOT in `wCodesK`'s. MEASURED, by reading `:7239-7245` whole.

**THE COUNTERMODEL** is `[LJ-1.344]`'s, at `Residue347.agda:118-181`:

- `arS := sglS (numeralL 1)`, whose set is `⁅ # 1 , # 1 ⁆`;
- `cS := prʟ arS (prʟ (numeralL 0) (prʟ u u))`, of exactly the tie's pair shape
  at `k := 0` and `a := b := u`;
- `wS := sglS cS`, the singleton of the code.

**EVERY AMBIENT FACT NOW COMES FROM THE CHAPTER'S OWN DELIVERED CODE.**
`Z.pair∈pr` and `Z.b∈pair` are `ChainZ` at
`src/L/Condensation.lagda.md:2837-2844`, and both are PUBLIC. `sgltK` is `KTies`
at `:6227-6234`, which `[LJ-1.346]` landed. **This file re-writes no private
lemma and adds no closure fact.** `[LJ-1.302]`, `[LJ-1.338]`, `[LJ-1.341]`,
`[LJ-1.344]` and `[LJ-1.345]` each copied four lines of `inr∈⁅,⁆` because they
could not name it; **I did not need to, and the reason is that `ChainZ` already
carries `pair∈pr` and `b∈pair` in public.** That is 4 lines paid five times and
never needed.

The tie then forces `∥ Σ m. ⁅ # 1 , # 1 ⁆ ≡ # m ∥₁`, which `Elim347.agda`
refutes at every `m`.

## 4. THE NEGATIVE CONTROLS AND NON-VACUITY

**CONTROL, POSITIVE HALF, AND IT DISCRIMINATES.**
`agents/tasks/LJ-1-347/Control347.agda`, **exit 0 in 1.50 s**. The same file
holds both halves:

- `numeral-arity-holds` (`:38`) exhibits the tie's own last conjunct HOLDING at
  a genuine numeral arity. **So the conjunct is satisfiable and the refutation
  measures the SITE, not the statement** (C-42).
- `singleton-arity-fails` (`:42`) is the refutation at the countermodel's arity.

**One argument separates the two lines. MEASURED.**

**CONTROL, RED HALF, AND IT FAILS AT THE LINE IT NAMES.**
`agents/tasks/LJ-1-347/ControlR347.agda`, **exit 42 in 0.88 s**, refused at
`ControlR347.agda:36.35-36` with `fst (numeralL 1)` offered where the pairing
set of `# 1` with itself is wanted. **So the refutation does NOT prove too
much:** it turns on the choice of the arity element and cannot be pointed at a
real numeral. MEASURED.

**NON-VACUITY, THREE LAYERS, and the third is the one that matters.**

1. **The tie's OTHER conclusions HOLD at the witnesses.** `other-conjuncts`
   (`Residue347.agda:170-171`) is `⟨ fst arS ∈ K ⟩ × ⟨ fst u ∈ K ⟩ × ⟨ fst u ∈ K ⟩`.
   **So the tie dies at a point where every other conjunct is true, and ONLY the
   arity conjunct is refuted.**
2. **Every premise the tie asks for is a CLOSED term**, built and never assumed:
   `wS∈K` (`:150`), `cS∈wS` (`:153`), `codeEq` (`:155-159`).
3. **THE REFUTATION RUNS ON THE DELIVERED RECORD.** `Residue347.Wire`
   (`:196-226`) opens `KValue` at its own six frame parameters, takes its
   `facts` record, and produces `tie-false` (`:218-219`). **The five closure
   facts arrive from the chapter and nothing here restates one. This is not a
   parameters-green.** ONE hypothesis is mine, `#1∈γ`, which says the carrier
   stage is at least 1 and is what makes the carrier NON-EMPTY. **Without a
   non-empty carrier the tie would be true at this record because nothing would
   meet it**, which is the trap this whole chain is about (C-45).

## 5. THE THIRD SHAPE, SWEPT. 24 SITES IN THE CHAPTER, NOT 2

**THE BRIEF'S PREMISE AT RISK IS CONFIRMED.** I read
`src/L/Condensation.lagda.md:6261-6278` myself before building on it.
`ShapesAgree`'s `compK` (`:6268-6273`) and `unCompK` (`:6274-6278`) DO carry the
same last conjunct, and their subject `C : S` at `:6262` IS a bare module
parameter with **no hypothesis at all**. MEASURED.

**BUT THE COUNT WAS FAR TOO SMALL.** I read every module parameter block in the
chapter, 106 of them, and classified each tie by what constrains the CONTAINER
that the code sits in. **Do not grep for the token** (C-52): the token appears
in consumer premises too, and those are a different thing.

### 5.1 THIRD SHAPE: the container carries NO hypothesis at all. **24 sites**

**Sub-family A, the container is a bare `S` module parameter. 4 sites.**

| site | tie | lines |
|---|---|---|
| `BinFormAgree` | `compK` | `:5834-5839` |
| `UnFormAgree` | `unCompK` | `:5922-5926` |
| `ShapesAgree` | `compK` | `:6268-6273` |
| `ShapesAgree` | `unCompK` | `:6274-6278` |

**Sub-family B, the container is `lookup C γ`, an index into the bare
environment parameter. 20 sites.**

| site | tie | lines |
|---|---|---|
| `BotAgree` | `codesK` | `:2782-2785` |
| `PropAgree` | `codesK` | `:3292-3296` |
| `AndAgree` | `codesK` | `:3544-3548` |
| `OrAgree` | `codesK` | `:3599-3603` |
| `TopAgree` | `codesK` | `:3674-3677` |
| `NegAgree` | `codesK` | `:3747-3750` |
| `ForallAgree` | `codesK` | `:3860-3863` |
| `ExistAgree` | `codesK` | `:3972-3975` |
| `ClauseAgree` | `codesK` | `:4154-4157` |
| `MemAgree` | `codesK` | `:4422-4426` |
| `AllInAgree` | `codesK` | `:5022-5026` |
| `ExInAgree` | `codesK` | `:5151-5155` |
| `ImpAgree` | `codesK` | `:5279-5283` |
| `EqAgree` | `codesK` | `:5380-5384` |
| `BinFrameAgree` | `codesK` | `:6400-6404` |
| `UnFrameAgree` | `unCodesK` | `:6448-6451` |
| `ClosedAgree` | `codesK` | `:6554-6558` |
| `ClosedAgree` | `unCodesK` | `:6559-6562` |
| `ShapedAgree` | `codesK` | `:6655-6659` |
| `ShapedAgree` | `unCodesK` | `:6660-6663` |

**THE TWO SUB-FAMILIES ARE THE SAME DEFECT AT TWO SORTS**, exactly the sort
confusion `[LJ-1.344]` met in the singleton closure. A bare `C : S` and a
`lookup C γ` into a bare `γ` are equally unconstrained. MEASURED, by reading all
24 telescopes: **not one parameter anywhere in those modules says anything about
the container.**

### 5.2 SECOND SHAPE: the container is bounded in K, not shaped. **8 sites**

| site | tie | lines |
|---|---|---|
| `WitnessAgree` | `codesK` | `:6694-6699` |
| `WitnessAgree` | `unCodesK` | `:6700-6704` |
| `SatGraphAgree` | `codesK` | `:6985-6991` |
| `SatGraphAgree` | `unCodesK` | `:6992-6997` |
| `LeafAgree` | `wCodesK` | `:7239-7245` |
| `LeafAgree` | `wUnCodesK` | `:7246-7251` |
| `LeafAgree` | `gCodesK` | `:7262-7269` |
| `LeafAgree` | `gUnCodesK` | `:7270-7276` |

**`Residue347.agda` refutes the first of these.** **INFERRED that the same
countermodel refutes all eight**, because the telescopes differ only in the
index form and the arity or unary shape; **I ran it against `wCodesK` only.**

### 5.3 THE CONSUMERS: 20 slots that TAKE the conjunct as a premise

`envK` and `envInK` in `TopAgree` (`:3682`, `:3687`), `NegAgree` (`:3765`,
`:3770`), `ForallAgree` (`:3878`, `:3883`), `ExistAgree` (`:3990`, `:3995`),
`ClauseAgree` (`:4172`, `:4177`), `MemAgree` (`:4435`, `:4440`), `AllInAgree`
(`:5049`, `:5054`), `ExInAgree` (`:5178`, `:5183`), `ImpAgree` (`:5300`,
`:5305`), `EqAgree` (`:5393`, `:5398`).

**These are NOT refutable by my countermodel and they are not the defect.**
They are the DEMAND: something really wants the arity to be a numeral. **A
repair that simply deletes the conjunct must answer these 20.**

### 5.4 THE SITES ARE A CHAIN, not 24 independent statements

MEASURED, by reading the instantiations: `LeafAgree:7307` feeds `WitnessAgree`;
`WitnessAgree:6722` and `:6728` feed `ClosedAgree` and `ShapedAgree`;
`ShapedAgree:6667` and `:6675` feed `ShapesAgree` **at
`ShapesAgree {n} (lookup C γ) ...`, which is where sub-family A meets sub-family
B**; `ShapesAgree:6289` onward feeds `BinFormAgree` and `UnFormAgree`;
`ClosedAgree:6575` onward feeds `BinFrameAgree` and `UnFrameAgree`.

**So the 24 are one tie threaded down a chain, plus the 14 per-connective
`*Agree` modules, which are a SECOND family.** The second family is
instantiated OUTSIDE this chapter, at
`src/L/Condensation/LowerAgree.lagda.md:255`, `:262`, `:269` and
`src/L/Condensation/UpperAgree.lagda.md:259`.

### 5.5 FOUR MORE SITES DOWNSTREAM, and I did NOT sweep those chapters

`src/L/Condensation/LowerAgree.lagda.md:116-126` and
`src/L/Condensation/UpperAgree.lagda.md:116-126` each carry `codesK` and
`codesK-un` **as RECORD FIELDS**, with container `lookup (suc (suc zero)) γ`,
an index into a bare `γ`. **Same third shape, 4 more sites.** I read those two
blocks and no more. **I did NOT sweep either chapter, and I do not claim their
total.**

## 6. THE REPAIR, PRICED AND NOT LANDED

**THE SHAPE OF THE CURE IS `[LJ-1.343]`'s: put the missing bound in the
telescope.** For this conjunct the missing bound is **shapedness**, and the
chapter already states it: `witK`'s premise carries
`closedAt zero ∧̇ shapedAt zero (suc (suc (suc (suc w))))` at
`src/L/Condensation.lagda.md:7233-7234`. **A container that is shaped cannot be
my `⁅ c , c ⁆`, because `shapedAt` forces every member to be a shape.** That is
the same wall `[LJ-1.344]` measured against `witK`, and here it is the cure.

**WHERE IT GOES, and this is what makes it cheap.** Section 5.4 measures that
the 24 third-shape sites are ONE tie threaded down a chain from `LeafAgree`.
**`witK` already holds the shapedness at the top of that chain.** So the repair
adds the hypothesis at the top and threads it, rather than 24 times over.

**THE PRICE. INFERRED, and I name the basis (DD8).** Basis: a delivered
comparable, `[LJ-1.343]`, which moved a bound from one slot to another for TWO
ties at **20 insertions**, that is **10 insertions per tie**.

| what | count | insertions |
|---|---:|---:|
| the chain's ties, `LeafAgree` down to `BinFormAgree` | 10 | **about 100** |
| the per-connective family, `BotAgree` to `EqAgree` | 14 | **about 140** |
| the two downstream records | 4 | **about 40** |
| **total** | **28** | **about 280** |

**THIS IS AN ESTIMATE AND IT IS THE WIDEST UNMEASURED TERM ON THE CHAIN.** I
did not build one line of it. **The comparable is `[LJ-1.343]`'s and P-l says a
measured cure does not transfer by analogy**: `[LJ-1.343]` moved a MEMBERSHIP,
and this repair moves a SATISFACTION clause, which is a different sort. **The
next task should probe ONE tie before anybody funds 28.**

**AND THE 20 CONSUMERS ARE THE REAL GATE.** Section 5.3. A repair that adds a
hypothesis to the producers leaves the consumers alone, so it is safe there. **A
repair that DELETES the conjunct is not**, and I priced neither. **INFERRED that
adding the hypothesis is the cheaper of the two, and I did not measure it.**

## 7. A SIBLING PROBE IS NOW RED, and I say so here rather than let a reader find it

**`agents/tasks/LJ-1-344/Supply344.agda` NO LONGER TYPECHECKS.** MEASURED,
exit 42, refused at `Supply344.agda:292.54-58` with
`(fst E) != (fst z) of type (V ℓ)`.

**THE CAUSE.** `[LJ-1.346]` REMOVED the two tie parameters `envK` and
`defPairK` from `DefinesAgree`'s telescope
(`src/L/Condensation.lagda.md:6885-6892`) and now derives both from `KTies` at
`:6905`. `Supply344.agda:292` still passes them positionally, so `envK` lands in
`pairK`'s slot. **The probe is right about the chapter it was written against
and stale against the chapter as delivered today.**

**THIS IS NOT A DEFECT IN `src/`.** It is the ordinary cost of naming a
telescope by position. **I did not edit that directory.** My first
`Residue347.agda` imported it and died at 2.9 s; **the version that is green
imports it NOT AT ALL** and uses the chapter's own `ChainZ` and `KTies`
instead, which is the better file anyway.

## 8. SECONDS, LOAD, RUNS

One agda process at a time, always `GHCRTS="-A64m -I0 -M8g"`, **cap NEVER
raised**. `ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l` run before
every invocation: **0 every time**.

**FLOOR (C-53).** Empty-file floor `agents/tasks/LJ-1-347/Floor347.agda`:
**0.48 s** warm, about 1 s cold at one-second resolution.

| run | exit | seconds |
|---|---:|---:|
| `Floor347.agda` (cold) | 0 | ~1 |
| `Floor347.agda` (warm) | 0 | **0.48** |
| `Zero347.agda` (scope slip) | 42 | 0.78 |
| `Zero347.agda` | **0** | **1.51** |
| `Full347.agda` | **251, HEAP EXHAUSTED** | **406.01** |
| `Ctl347A.agda` | 0 | 1.70 |
| `Split347.agda` | **251, HEAP EXHAUSTED** | **373.93** |
| `Ctl347B.agda` | 0 | 1.73 |
| `Elim347.agda` | **0** | **1.64** |
| `Residue347.agda` (importing `Supply344`) | 42 | 2.90 |
| `Residue347.agda` (final) | **0** | **3.16** |
| `Control347.agda` | 0 | 1.50 |
| `ControlR347.agda` (EXPECTED RED) | 42 | 0.88 |

**TWO HEAP EXHAUSTIONS, REPORTED AS WALLS.** Neither reached 30 minutes: they
died at 406 s and 374 s with a clean `Heap exhausted` exit under the cap. **The
cap was never raised.** I bisected EARLY, as the brief ordered: the first wall
came at run four and the sub-term was named by run seven.

**THE DELTAS ARE MOSTLY UNMEASURABLE, and I say so.** `Zero347.agda` at 1.51 s
against the 0.48 s floor is a delta of 1.03 s, which is above the floor.
`Elim347.agda` at 1.64 s against `Ctl347B.agda` at 1.73 s is a delta of
**minus 0.09 s, far UNDER the floor: UNMEASURABLE, not small.** **The one delta
that is beyond argument is 1.73 s against an exhausted 8 GB heap.**

**A CACHE WARNING, inherited from `[LJ-1.345]` and `[LJ-1.344]`.** My files load
`L.Condensation` from its committed interface. **No figure here is a cold check
of the chapter, and none is offered as one.**

## 9. DD4, WITH THE AXIS NAMED (C-46)

**THE AXIS IS AC-AGAINST-GCH, fixed at `scripts/measure/ledger.py:50`.**

**EVERY TERM I WROTE IS CLASS-FREE.** MEASURED, by reading all six files:
`sgl1-not-numeral`, `zero-clause`, `suc-clause`, `x∈pair`, `pair-only`, `sglS`,
`sglK` and the whole of `Refute` name only `fst`, `∈`, `lookup`, `pr`, `prʟ`,
`numeralL`, `⁅_,_⁆`, `#_`, `∅` and five `KFacts` fields. **Not one mentions AC,
GCH, a well-ordering or a cardinal.**

**AND THE FINDING IS DOUBLY SHARED.** The refuted conjunct sits in `KFacts`
consumers that `[LJ-1.344]` measured generic at both carriers
(`GenAgree.agda:4886`). **So one refutation retires the same false statement at
both ends, and the repair of section 6, when someone builds it, is written once
for both.** One rule, two ends.

**THE CURE OF SECTION 2 IS THE MORE VALUABLE HALF FOR DD4**, because it is not
about this conjunct at all: it is about how any numeral-indexed lemma is written
anywhere in either tower.

## 10. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| the `m = 0` clause is unreachable | **MEASURED FALSE.** `Zero347.agda`, exit 0, 1.51 s |
| the wall is the numeral `# 0` | **MEASURED FALSE.** `Zero347.agda` and `Ctl347A.agda` |
| the wall is the route | **MEASURED FALSE.** A third route walls under the split and returns without it |
| the wall is the import set | **MEASURED FALSE.** `Ctl347A.agda`, exit 0, 1.70 s |
| the wall is the inlining | **MEASURED FALSE.** `Split347.agda` walls with the clauses named |
| the wall is the two clauses coexisting | **MEASURED FALSE.** `Ctl347B.agda`, exit 0, 1.73 s |
| the arity conjunct is true | **MEASURED FALSE.** `Residue347.agda`, exit 0, refutation at the delivered record |
| the refutation proves too much | **MEASURED FALSE.** `ControlR347.agda`, exit 42 at the named line |
| the conjunct is absurd at every arity | **MEASURED FALSE.** `Control347.agda:38`, it holds at a numeral |
| the refutation is a parameters-green | **MEASURED FALSE.** `Residue347.Wire` runs on `KValue`'s own record |
| the refutation kills the tie's other conclusions too | **MEASURED FALSE.** `other-conjuncts` holds; only the arity conjunct dies |
| the third shape has two sites | **MEASURED FALSE.** 24 in the chapter, named in section 5.1 |
| the arity family has six occurrences | **MEASURED FALSE.** 32 producers and 20 consumers in the chapter |
| the 24 sites are independent statements | **MEASURED FALSE.** They are a chain, section 5.4 |
| `agents/tasks/LJ-1-344/Supply344.agda` is green | **MEASURED FALSE.** Exit 42 at `:292.54-58` |
| the brief's line numbers are current | **MEASURED FALSE.** `[LJ-1.346]` moved them by 109 lines |
| the other seven second-shape sites are refuted here | **MEASURED FALSE.** Only `wCodesK` was run; the rest are INFERRED |
| the repair is measured | **MEASURED FALSE.** It is INFERRED at about 280 insertions and I built no line of it |
| the two downstream chapters are swept | **MEASURED FALSE.** I read two blocks and no more |
| anything landed in `src/` | **MEASURED FALSE.** `git status --short` shows `agents/tasks/LJ-1-347/` only |
| a run hit the 30 minute wall | **MEASURED FALSE.** Two heap exhaustions at 406 s and 374 s, cap never raised |

## 11. ARCHIVE USED (DD18)

One line read per archived file, as the brief orders.

- **`agents/tasks/LJ-1-344/lj-1.344-report.md`, read WHOLE.** **Line read:** its
  section 6.3, 「MEASURED: the cost is in refusing `# 1 ∈ # 0` at CONCRETE
  numerals, and it is not the route」. **TOOK** the countermodel entire, which
  is right, and the honesty of its INFERRED verdict, which funded this task.
  **CORRECTED it:** that sentence is MEASURED FALSE. The cost is the case split
  and neither the numerals nor the route, and section 1 gives five controls.
  **I also TOOK its top matter's warning that three of its probes do not return,
  and re-ran only `Bisect344B.agda`'s statement, never the three that wall.**
- **`agents/tasks/LJ-1-341/lj-1.341-report.md`, read the answer table.**
  **Line read:** `:297`, 「they are false only at some environments |
  **MEASURED FALSE.** `module Refute` is universal in `Ki` and `γ`」. **TOOK**
  its universality discipline: my `Refute` is likewise universal in `A`, `K` and
  `γ`, so the refutation is not about one environment. **REJECTED nothing.**
- **`agents/tasks/LJ-1-345/lj-1.345-report.md`, read the residue table.**
  **Line read:** `:165`, 「DefinesAgree `:6778` | `envK`, `pairK`, `satK` | the
  two FATAL ones」. **TOOK** its sweep discipline, which is that a refutation is
  followed by a COUNT before a cure. **CORRECTED its scope:** its sweep covered
  the FATAL shape at `DefinesAgree` and `LeafAgree`; section 5 shows the arity
  family reaches 24 further sites it never counted.
- **`archive/dev/TASKS-archived.md`, read the header at `:1-14`.** **TOOK SHAPE
  ONLY:** a retired route's dispatch index, 264 rows, kept for which approaches
  were measured. **REJECTED every figure:** that route has a different carrier
  and no `KFacts` record, so no count and no seconds figure from it prices
  anything here.

## 12. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md`, read `:246-249`.**

**THE ONE LINE THE BRIEF ASKS FOR: a conjunct whose subject carries no
hypothesis at all has NO counterpart in Devlin's text.** `:246-249` says the
argument writes `D(v, u) = "v = Def(u)"` as Σ₁ and then 「bind every unbounded
quantifier by the concrete set `K(u)`, the finite sequences over the formula
set, the variables and the members of `u`」. **Every quantifier of his is bound
by a set built from its argument. There is no unbound subject anywhere in the
engine.** So the 24 sites of section 5.1 are an artefact of the PORT and not of
the mathematics, and the repair of section 6 restores what Devlin already has.

**WHY NOT the rest of the digest.** `:243-244` is the `[LJ-1.12]` Δ₀ question,
settled and not about this conjunct. `:258` onward is Step D, the definable
well-order, which no tie of this family reaches. **The cardinality halves of 5.5
and 5.6 are another step, and C-46 forbids using Devlin's tower axis as DD4's.**

## 13. WHAT I DID NOT SETTLE

- **The other seven second-shape sites.** The reading applies to all eight by
  their telescopes; I ran the countermodel against `wCodesK` only.
- **The 24 third-shape sites, as refutations.** They are refutable MORE easily
  than `wCodesK`, because the container is not even bounded, but **I built no
  term at any of them.** INFERRED.
- **The repair.** Priced at about 280 insertions, INFERRED, basis `[LJ-1.343]`.
  **Not one line built.** P-l says re-measure it at its own site.
- **The two downstream chapters.** Two blocks read, no sweep.
- **`witK`, `graphWitK`.** Untouched, as the brief ordered.
- **The chapter's own green.** Nothing landed and I ran no whole-chapter check.
- **Whether the case-split law generalizes past `ℕ` and `V`.** One measurement,
  one index type. It is a law CANDIDATE and I say so.

## 14. PROHIBITIONS, ANSWERED

I wrote only inside `agents/tasks/LJ-1-347/`: this report and ten Agda files,
`Floor347.agda`, `Zero347.agda`, `Full347.agda`, `Ctl347A.agda`,
`Split347.agda`, `Ctl347B.agda`, `Elim347.agda`, `Residue347.agda`,
`Control347.agda` and `ControlR347.agda`. **`git status --short` shows that
directory and nothing else of mine.** **`src/` holds no probe of mine and I
opened no file under `src/` for writing.** I READ
`src/L/Condensation.lagda.md`, `src/L/Condensation/LowerAgree.lagda.md`,
`src/L/Condensation/UpperAgree.lagda.md` and `src/V/Coding.lagda.md`. I READ and
re-ran probes in `agents/tasks/LJ-1-344/` and edited that directory NOT AT ALL.
I did not open `src/Everything.lagda.md`, `dev/`, `AGENTS.md` or `.claude/` for
writing. **I did not touch `witK` or `graphWitK`.** No commit, no push, no
`git checkout`, `stash`, `reset` or `clean`. **No `make check`.** No em dash in
any language. **One agda process at all times, slots counted before every
invocation, cap never raised.**
