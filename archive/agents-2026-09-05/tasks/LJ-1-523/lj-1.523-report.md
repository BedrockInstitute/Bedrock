# LJ-1.523 report: the last mile priced, from the bounded subset theorem to GCH

## HEAD
head_slot: coder
machine: shared
verdict: GO

Written early as a skeleton and filled as each run landed (C-22). No commit,
no push. I wrote only in `agents/tasks/LJ-1-523/`. Agda ran under the caliber
the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a
time. I did not set `GHCRTS`. No heap event. Nothing is postulated. Nothing is
inhabited. The probe is a raw `.agda` file, so it carries no ` ```agda ` fence
and the ratio bar cannot fire on it.

## VERDICT

**GO. `GCHBridge` is built, with no holes, at the type the brief named.**
`agents/tasks/LJ-1-523/Probe523.agda:174-175`, exit 0, three forced rechecks in
`runs/full-1.out` to `runs/full-3.out`.

    GCHBridge : ModelL.isZFModel → Type (ℓ-suc ℓ)
    GCHBridge zf = BoundedSubsetTheorem → GCHStatement zf

`BoundedSubsetTheorem` (`Probe523.agda:143-156`) is the whole telescope of
`Devlin55.BoundedSubsetAt` (`src/L/BoundedSubset.lagda.md:1385-1395`) and of
`Co` (`:1554-1558`), written as Π arguments, ending at the conclusion
`⟨ x ∈ˢ Lset κ ⟩` (`:1621-1622`). `levelIn` and `cover` are carried and not
discharged, as the brief ordered. No hypothesis is hidden.

**THE ANSWER THE OWNER ASKED FOR IS IN SECTION `## WHAT IS STATED NOWHERE`.**
The type forms. It is not provable from its antecedent. Seven further inputs
stand between the two ends, and six of the seven are stated nowhere in the
tree.

**THREE OF THE BRIEF'S STATEMENTS DID NOT SURVIVE MEASUREMENT.** Section
`## THREE CORRECTIONS TO THE BRIEF` gives each with its evidence. One of them
changes what W3 means, so read that section before the input list.

I did not write a `review-of-*.md`. This is not a stop: the obligation is
delivered.

## THREE CORRECTIONS TO THE BRIEF

**1. "THIS IS THE FIRST TO LOOK AT THE JOIN" IS FALSE, AND THE PRIOR LOOKS
MEASURED THE SAME THING I DID.** Five dispatches reached this join.

- `archive/dev/LJ-dispatch-index.md:165`: "| LJ-1.90 | Instantiate BoundedSubsetAt for the first time | REACHES cardκ | Every other hypothesis takes a value, including AllCodes A in Lset lam. Nothing in the tree proves any set is a cardinal |"
- `archive/dev/LJ-dispatch-index.md:166`: "| LJ-1.90-A | Orchestrator audit: IsCardinal is never inhabited | CONFIRMED | Two hits in src: the definition and the hypothesis. The probe's own kappa, sucV omega, is not a cardinal either |"
- `archive/dev/LJ-dispatch-index.md:167`: "| LJ-1.91 | Gate the cardinal chapter | AMBIENT HARTOGS, 490 to 890 lines | IsCardinal is ambient, so the internal omega-1-L does not provably satisfy it. Order types are the widest term |"
- `archive/dev/LJ-dispatch-index.md:198`: "| LJ-1.121 | Supply levelIn and cover at the site | NEITHER REFUTABLE, NEITHER SUPPLIED | The wall is the LJ-1.12 crossing, the level-hood certificate, priced 2.8k to 3.3k lines and not built |"
- `archive/dev/LJ-dispatch-index.md:465`: "| LJ-1.8 | Build: assemble L models GCH | STATEMENT LANDED; ONE HYPOTHESIS BLOCKS THE PROOF | sq : SqShape, and LJ-1.286 measured that the delivered square law CANNOT supply it. Open work 7 |"

**`[LJ-1.91]` states my W3 finding in one line and it is dated before this
brief.** My measurement is a RE-measurement at a new site, the GCH statement's
own binding, and C-42 makes that the correct action, not a duplicate. What is
new here is the site and the size of the residue, not the shape.

**2. THE ANTECEDENT ALREADY EXISTS IN `src/`, IN MODULE FORM.**
`src/L/StageBound.lagda.md:64-91` copies the same telescope, and
`src/L/StageBound.lagda.md:111` is `go : SqFam α → ⟨ x ∈ˢ Lset κ ⟩` under the
same `levelIn` and `cover`. The brief said only `StageBound` consumes the
chapter (premise 8) and that is true, but it did not say that `StageBound`
already carries the theorem in consumer form. **A bridge does not have to
restate the antecedent. It can be built on `StageBound`.** My section 2 is the
CLOSED-TYPE form of the same thing, which is what an implication needs and
what `StageBound` does not provide.

`src/L/StageBound.lagda.md:137` goes further: `bounded-modulo-collect :
SqCollect α → ⟨ x ∈ˢ Lset κ ⟩` reduces the square-law hypothesis to
`SqCollect α` (`:44-48`), using `sq-trunc-closed`
(`src/L/SquareLawClosed.lagda.md:325-327`).

**3. `GCHStatement` AND `SuccCardL` ARE UNREAD, BUT THE CHAPTER IS NOT.**
The brief's grep is correct for those two names. It is not correct for the
chapter: `src/L/CantorBernstein.lagda.md:17` reads
`open import L.GCH {ℓ} lem using ( InjL )`, and
`src/L/CantorBernstein.lagda.md:51-55` builds `mutual-inj→bijection` on it.
**So one third of the GCH chapter is already a consumed dependency**, and the
Cantor-Bernstein step of the trophy is delivered.

## W3, THE TWO KAPPA

**THE ANSWER IS NO, AND IT IS NO TWICE OVER.** The two `κ` are not the same
type, and the theorem's `κ` is not the slot the statement's `κ` belongs in at
all.

`Probe523.agda:64-82`, exit 0, three forced rechecks in `runs/w3-1.out` to
`runs/w3-3.out`, taken with sections 2 to 4 absent. The slice is kept at
`runs/w3-slice.agda.txt`.

### The carriers differ

`src/L/GCH.lagda.md:27` opens `S` from `hPropStructure 𝒮ʟ`.
`src/L/BoundedSubset.lagda.md:56` opens `hPropStructure 𝒮ᵥ` UNQUALIFIED, so
`S` through that whole chapter is the V-carrier, and the L-carrier is reached
only as `CS` (`src/L/BoundedSubset.lagda.md:58`). `𝒮ʟ = 𝒮ᵥ ↾ isL`
(`src/L/Constructible.lagda.md:411`), and `_↾_` sets
`S = Σ[ x ∈ S ] (x ∈ᶜ M)` (`src/FOL/ZFStructure.lagda.md:146`). **The
statement's `κ` is a pair. The theorem's `κ` is its first component.**

### Under `fst`, two of the three certificates are the same term

| statement demands | at | theorem demands | at | same |
|---|---|---|---|---|
| `IsOrd (fst κ)` | src/L/GCH.lagda.md:61 | `IsOrd κ` | src/L/BoundedSubset.lagda.md:1386 | YES |
| `⟨ fst κ ∈ˢ ω ⟩ → ⊥` | src/L/GCH.lagda.md:63 | `⟨ κ ∈ˢ ω ⟩ → ⊥` | src/L/BoundedSubset.lagda.md:1386 | YES |
| `IsCardinalL κ` | src/L/GCH.lagda.md:62 | `IsCardinal κ` | src/L/BoundedSubset.lagda.md:1386 | NO |

`IsOrd` is one term: `src/L/GCH.lagda.md:15` and
`src/L/BoundedSubset.lagda.md:26-27` both import it from `L.Constructible {ℓ}`.
`ω` is one term: `src/L/GCH.lagda.md:21` and
`src/L/BoundedSubset.lagda.md:886` both open it from `InfinitySet`.
`kappa-shared` (`Probe523.agda:64-69`) typechecks the two agreeing rows at the
statement's binding.

### The residue

    kappa-agrees : Type (ℓ-suc ℓ)
    kappa-agrees =
        (κ : SL.S)
      → IsOrd (fst κ)
      → IsCardinalL κ
      → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
      → IsCardinal (fst κ)

`Probe523.agda:76-82`. `IsCardinalL` (`src/L/Cardinal.lagda.md:230-233`)
refutes a CODED injection, `∥ Σ[ F ∈ S ] InjCode F κ δ ∥₁ → ⊥`, with `δ` over
the L-carrier. `IsCardinal` (`src/L/BoundedSubset.lagda.md:1046-1047`) refutes
an AMBIENT injection, `⟪ κ ⟫ ↪ ⟪ δ ⟫ → ⊥`, with `δ` over the V-carrier and `↪`
the bare host function with injectivity (`src/L/BoundedSubset.lagda.md:1043-1044`).

**THE READBACK RUNS THE OTHER WAY, AND IT IS ALREADY BUILT.**
`src/L/CantorBernstein.lagda.md:33-38` is `readL`, which turns an `InjCode`
witness into an ambient injection. So an inhabitant of `IsCardinal (fst κ)`
yields `IsCardinalL κ` through `readL`. **The bridge needs the converse**, and
the converse asks for a CODE for an arbitrary ambient injection. That is the
counting leg's whole subject, and section `## WHAT IS STATED NOWHERE` says what
kind of object it is.

### The second no: the theorem's slot is the statement's delta

`GCHStatement` quantifies over κ and asserts a δ above it
(`src/L/GCH.lagda.md:59-68`). The theorem concludes `x ∈ˢ Lset κ` for ITS κ
(`src/L/BoundedSubset.lagda.md:1621`) and demands `α ∈ˢ κ` (`:1387`). To place
a subset of the statement's κ inside the stage at δ, the theorem must be
entered with **its κ at `fst δ` and its α at `fst κ`.**

**THE LITERATURE SAYS THE SAME, AND IT SAID IT FIRST.**
`dev/literature/devlin-II5.md:164`: "The application of 5.5 in 5.6 is at the
cardinal κ⁺ with α = κ: every".

So `kappa-agrees` is the right shape at the wrong site. The site the use needs
is `AmbientAtSucc` (`Probe523.agda:202-204`):

    AmbientAtSucc : Type (ℓ-suc ℓ)
    AmbientAtSucc = (κ δ : SL.S) → SuccCardL δ κ → IsCardinal (fst δ)

### And the demand is smaller than the telescope says

**`cardκ` is consumed exactly twice, at `src/L/BoundedSubset.lagda.md:1597` and
`:1601`, and both times as `cardκ α α∈κ`.** The `δ` argument is the telescope's
own `α` and never anything else. Both uses feed `β∈κ` (`:1595-1608`) and both
pass an ambient injection into `⟪ α ⟫`. **So the proof never needs
`IsCardinal κ` at any other member.** The weakest hypothesis that carries those
two lines is `CardSpentAt` (`Probe523.agda:213-214`):

    CardSpentAt : SV.S → SV.S → Type ℓ
    CardSpentAt κ α = ⟪ κ ⟫ ↪ ⟪ α ⟫ → Empty.⊥

and the residue at the site the use needs becomes `AmbientSpentAtSucc`
(`Probe523.agda:218-220`), which asks for one refutation and not a cardinal.
**This is a real reduction and I did not expect it before I grepped the two
lines.** It is the mathematician's to price.

### W3 measurement

Three forced rechecks, `Probe523.agdai` deleted before each, sections 2 to 4
absent, warm `src/` interfaces:

| run | wall | peak RSS |
|---|---|---|
| 1 | 2.93 s | 732545024 B |
| 2 | 2.91 s | 732577792 B |
| 3 | 2.94 s | 732545024 B |

Median **2.93 s**, median peak RSS **732545024 B**, which is 698.6 MiB.
The brief estimated about 25 lines and under 40 seconds. The lines are 25 net
of comments and blanks in section 1. The seconds are 2.93.

## THE INPUT LIST

Two lists, because the brief's three-way split answers two different questions
and mixing them would hide the second.

### A. The names the type mentions

Every one resolves. The type has no hole and no free name.

| name | type | status | at |
|---|---|---|---|
| `ModelL.isZFModel` | record | delivered in `src/` | src/FOL/ZFModel.lagda.md:187, applied at 𝒮ʟ as in src/L/GCH.lagda.md:30 |
| `GCHStatement` | `ModelL.isZFModel → Type (ℓ-suc ℓ)` | delivered in `src/` | src/L/GCH.lagda.md:59-70 |
| `IsOrd` | `S → Type (ℓ-suc ℓ)` | delivered in `src/` | imported at src/L/GCH.lagda.md:15 and src/L/BoundedSubset.lagda.md:26 |
| `IsCardinal` | `S → Type (ℓ-suc ℓ)` | delivered in `src/` | src/L/BoundedSubset.lagda.md:1046-1047 |
| `IsCardinalL` | `S → Type (ℓ-suc ℓ)` | delivered in `src/` | src/L/Cardinal.lagda.md:230-233 |
| `InjL` | `S → S → Type (ℓ-suc ℓ)` | delivered in `src/` | src/L/GCH.lagda.md:37-38 |
| `InjCode` | `S → S → S → Type (ℓ-suc ℓ)` | delivered in `src/` | src/L/Cardinal.lagda.md:223-228 |
| `SuccCardL` | `S → S → Type (ℓ-suc ℓ)` | delivered in `src/` | src/L/GCH.lagda.md:46-53 |
| `Lset` | `S → S` | delivered in `src/` | imported at src/L/BoundedSubset.lagda.md:27 |
| `ω`, `sucV` | `S` and `S → S` | delivered in `src/` | opened at src/L/BoundedSubset.lagda.md:886 |
| `_↾_` | structure restriction | delivered in `src/` | src/FOL/ZFStructure.lagda.md:143-150 |
| `Devlin55.BoundedSubsetAt` | module | delivered in `src/` | src/L/BoundedSubset.lagda.md:1385-1395 |
| `BoundedSubsetAt.Co` | module | delivered in `src/` | src/L/BoundedSubset.lagda.md:1554-1558 |
| `HullStage.M`, `.C.πX`, `.C.π` | `S`, `S`, `S → S` | delivered in `src/` | src/L/BoundedSubset.lagda.md:913-914, src/V/Collapse.lagda.md:53 and :75 |
| `𝒫` | `S → S` | delivered in `src/` | src/FOL/ZFModel.lagda.md:287-288 |
| `_↪_` | `Type ℓ → Type ℓ → Type ℓ` | delivered in `src/` | src/L/BoundedSubset.lagda.md:1043-1044 |
| `_∪_`, `⁅_⁆s`, `⟪_⟫` | Cubical | delivered by the library | opened at src/L/BoundedSubset.lagda.md:884, :51 |

### B. The inputs an inhabitant would consume

This is the list that carries the price. Each row is a type in section 4 of the
probe or a term in `src/`.

| # | input | type at | status |
|---|---|---|---|
| B1 | the model, `zf : ModelL.isZFModel` | argument of the bridge | delivered in `src/`: `L⊨ZFC` at src/Landmarks.lagda.md:76-77, whose `isZFCModel` carries the field `zf : isZFModel` at src/FOL/ZFModel.lagda.md:421 |
| B2 | Cantor-Bernstein at `InjL` | src/L/CantorBernstein.lagda.md:51-55 | delivered in `src/` |
| B3 | readback, code to ambient injection | src/L/CantorBernstein.lagda.md:33-38 | delivered in `src/` |
| B4 | `SuccCardExists`, the successor L-cardinal | Probe523.agda:191-195 | STATED NOWHERE |
| B5 | `AmbientSpentAtSucc`, the ambient refutation at δ | Probe523.agda:218-220 | STATED NOWHERE |
| B6 | `SubsetIntoStage`, a constructible subset of κ lies in `Lset (fst κ)` | Probe523.agda:224-228 | STATED NOWHERE |
| B7 | `AbsorbsAt`, the absorbing injection at the theorem's shape | Probe523.agda:234-238 | STATED NOWHERE |
| B8 | `LimitAbove`, a successor-closed stage above α holding x | Probe523.agda:244-251 | STATED NOWHERE |
| B9 | `StageCountedCoded`, `InjL (Lset δ) δ` | Probe523.agda:258-261 | STATED NOWHERE. Its ambient shadow IS delivered: `stage-card-upper` at src/L/StageCardinal.lagda.md:564-566 |
| B10 | `SuccIntoPower`, `InjL δ (𝒫 κ)` | Probe523.agda:266-268 | STATED NOWHERE |
| B11 | `levelIn` and `cover` | src/L/BoundedSubset.lagda.md:1555-1557 | stated in `src/` as hypotheses, NOT supplied. `archive/dev/LJ-dispatch-index.md:198` records the last attempt |
| B12 | `SqCollect α`, the square-law collection | src/L/StageBound.lagda.md:44-48 | stated in `src/`, NOT inhabited. Its comment at :42 says so |
| B13 | `sq-trunc-closed`, the pointwise truncated square law | src/L/SquareLawClosed.lagda.md:325-328 | delivered in `src/` |

**B11 AND B12 ARE NOT ON THIS BRIDGE'S BILL.** B11 is carried into
`BoundedSubsetTheorem` as a Π argument, so the bridge does not owe it. B12 is
carried the same way through `sq`. I list them so the next brief does not
count them twice.

## IS THE COUNTING LEG'S `InjCode` THIS ONE

**YES. It is the same term, from the same module at the same `{ℓ}` and the same
`lem`.** `agents/tasks/LJ-1-490/Probe490.agda:38` is
`open import L.Cardinal {ℓ} lem using ( InjCode )`, and `src/L/GCH.lagda.md:16`
is `open import L.Cardinal {ℓ} lem using ( IsCardinalL; InjCode )`.

Three further checks agree. `[LJ-1.490]`'s obligation
`RankCoded` (`agents/tasks/LJ-1-490/Probe490.agda:289-292`) concludes
`InjCode (fst (rank-graph Q a (fst (rank-bound a oa)))) a b`, which is that
`InjCode` at three L-elements. `[LJ-1.521]`'s conjunct table
(`agents/tasks/LJ-1-521/lj-1.521-report.md:396-401`) names `svAt`, the range
clause, `injAt` and `domAt`, which are exactly the four conjuncts of
`src/L/Cardinal.lagda.md:224-228`. And `src/L/Absorption.lagda.md:611-615`
already delivers a landed `∥ Σ[ F ∈ S ] InjCode F (sucʟ γ) γ ∥₁` at the same
term, with the conclusion written at `:614`.

**SO THE COUNTING LEG IS AIMED AT THE RIGHT OBJECT.** What it is not yet aimed
at is the SITE this bridge needs. `RankCoded` codes an injection of an L-element
into a bounding ordinal. Row B9 needs it at `a := Lset δ` and `b := δ`, and row
B5 needs its ambient converse. Neither site is named in any predecessor report I
read.

## WHAT IS STATED NOWHERE

Seven rows. For each, what kind of object it is. **No lines and no seconds: the
brief reserved that for the mathematician.**

**B4, `SuccCardExists`.** A CARDINAL ARITHMETIC fact, and the largest of the
seven. It asserts that every infinite ordinal L-cardinal has a successor
ordinal L-cardinal. **Nothing in `src/` produces an `IsCardinalL` witness at
all**: `grep -rn "IsCardinalL" src --include='*.lagda.md'` returns six hits and
every one is the definition (`src/L/Cardinal.lagda.md:230-233`), an import
(`src/L/GCH.lagda.md:16`), a mention in a comment (`src/L/Cardinal.lagda.md:216`,
`src/L/SquareLawClosed.lagda.md:313`) or a use inside the statement
(`src/L/GCH.lagda.md:49`, `:51`, `:63`). The nearest delivered thing is
`L.Cardinal.InternalLeastCard` (`src/L/Cardinal.lagda.md:235-269`), which
selects a LEAST δ that κ codes into. That is not a successor cardinal, and
C-42 forbids reading it as one.

**B5, `AmbientSpentAtSucc`.** A CROSSING fact, between the ambient universe and
the model. It says no ambient injection carries `⟪ fst δ ⟫` into `⟪ fst κ ⟫`
when δ is the successor L-cardinal of κ. **This is the row the whole bridge
turns on.** `archive/dev/LJ-dispatch-index.md:167` already recorded its shape:
"IsCardinal is ambient, so the internal omega-1-L does not provably satisfy
it." An ambient Hartogs construction once supplied a `cardκ`
(`archive/dev/LJ-dispatch-index.md:170`, 1058 lines, green), and **it is not in
the tree**: `grep -rln "Hartogs" src` returns nothing, and `src/Everything.lagda.md`
carries no such import.

**One reading of the route, marked as a reading and not a measurement.** The
hull the theorem collapses is built in the ambient structure
(`src/L/Hull.lagda.md:148`, `:313`, entered through
`src/L/BoundedSubset.lagda.md:1405`), so its size is an ambient size, and
Devlin's own statement carries "Assume V = L"
(`dev/literature/devlin-II5.md:147`). Bedrock does not assume V = L: it states
the trophy relativized, and `archive/dev/LJ-dispatch-index.md:444` records the
ruling that removed every ambient injection from that statement. **The chapter
and the statement therefore sit on opposite sides of a relativization that
nobody has written.** I did not measure this claim and it is the
mathematician's to settle.

**B6, `SubsetIntoStage`.** A CODING fact about the stage tower. It says a
member of the model's `𝒫 κ` is a subset of `Lset (fst κ)`. The ingredient is
that the ordinals below κ already sit in `Lset κ`; the nearest delivered term is
`ord∈Lset-suc` (`src/L/Ordinal/Stages.lagda.md:434`), which lands an ordinal in
the stage at its OWN successor, not in the stage at κ.

**B7, `AbsorbsAt`.** A CARDINAL ARITHMETIC fact: adjoining one point to an
infinite stage does not grow it. **A term named `absorbs` IS delivered**, at
`src/L/Absorption.lagda.md:635-637`, with type
`⟪ sucV (fst γ) ⟫ ↪ ⟪ fst γ ⟫`. That is a different shape from
`⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫` (`src/L/BoundedSubset.lagda.md:1392`), and
C-42 forbids reading one as the other. The name collision is a trap for the
next reader and I flag it deliberately.

**B8, `LimitAbove`.** An ORDINAL SUPPLY fact. `isL x` gives a stage holding x by
definition (`src/L/Constructible.lagda.md:376`), but neither the successor
closure `succλ` nor `α ∈ˢ lam`. The pieces exist as ordinal machinery
(`src/L/Ordinal.lagda.md` supplies `boundingOrd`), and nothing assembles them at
this shape.

**B9, `StageCountedCoded`.** A CODING fact, and it is where the counting leg
lands. The ambient version is delivered: `stage-card-upper`
(`src/L/StageCardinal.lagda.md:564-566`) gives `⟪ Lset α ⟫ ↪ ⟪ α ⟫`. `InjL`
wants that injection with a code (`src/L/GCH.lagda.md:37-38`), and the code is
what `[LJ-1.490]` through `[LJ-1.521]` are building. **This row is the one the
counting leg is closest to, and its four conjuncts are two-and-a-half delivered
by `agents/tasks/LJ-1-521/lj-1.521-report.md:396-401`.**

**B10, `SuccIntoPower`.** A CODING fact, and it is NOT on this bridge at all.
`InjL δ (𝒫 κ)` is the third conjunct of the statement
(`src/L/GCH.lagda.md:68`), the direction `κ⁺ ≤ 2^κ`. The bounded subset theorem
says nothing about it. **A brief that prices the bounded subset route as "the
last mile" is pricing two thirds of the mile.** The other third has no leg in
this campaign that I could find.

## MEASUREMENTS

Caliber `-A64m -I0 -M8g`, read off the pane, never set by me. One Agda process
at a time. `_build/2.8.0/agda/agents/tasks/LJ-1-523/Probe523.agdai` deleted
before each run, so each number is the probe re-elaborated against warm `src/`
interfaces. **A cold-tree number is not in this report and nothing may be
funded against these as if it were.**

Full file, three forced rechecks, `runs/full-1.out` to `runs/full-3.out`:

| run | wall | peak RSS |
|---|---|---|
| 1 | 8.23 s | 1458651136 B |
| 2 | 8.41 s | 1458651136 B |
| 3 | 8.43 s | 1458651136 B |

Median **8.41 s**, median peak RSS **1458651136 B**, which is 1391.1 MiB.

W3 alone: median 2.93 s, median peak RSS 732545024 B. The table is in the W3
section.

**THE MODULE APPLICATION IS THE COST.** Section 1 alone is 2.93 s. Adding
section 2, whose only new work is `module BSA = Devlin55.BoundedSubsetAt ...`
with sixteen arguments, took the file to 7.91 s on its first green run. That is
about 5 s and about 570 MiB for one section application of that module.
Sections 3 and 4 together added about 0.5 s. **Anyone who instantiates
`BoundedSubsetAt` should budget those 5 s, and `src/L/StageBound.lagda.md:73-77`
already pays them once.**

## ESTIMATE AGAINST MEASURED

**ESTIMATE for the Agda was about 120 lines, of which the obligation about 40.
MEASURED 269 lines, 123 of them non-blank and non-comment.** The file is 224
percent of the estimate on raw lines and 103 percent on code lines.

- **The obligation: estimated about 40, measured 2** (`Probe523.agda:174-175`).
  The estimate priced the obligation together with the antecedent it needs.
- **The antecedent: not priced separately, measured 60** (`Probe523.agda:97-156`).
  `SqLaw`, `module Tele` and `BoundedSubsetTheorem`. The brief's basis, "the
  type must open both chapters' telescopes", is exactly right about the work and
  it attached the number to the wrong definition.
- **W3: estimated about 25, measured 25** (`Probe523.agda:64-82` net of
  comments and blanks). The estimate was right.
- **Section 4 was not in the estimate and it is 36 code lines**
  (`Probe523.agda:191-268`). I wrote it because `## WHAT IS STATED NOWHERE`
  demands seven statements, and a typechecked type is evidence where prose is
  not. It is not an obligation and AD12 is not touched.
- **Comments are 146 of the 269 lines.** Every `file:line` in this report that
  points into the probe is also written beside the definition it justifies.

## WHAT THE NEXT BRIEF SHOULD KNOW

**THE THREE LEGS DO NOT MEET AT ONE TARGET AND THE GAP IS NOT IN THE LEGS.**
The counting leg is building the right `InjCode` at the wrong site (B9). The
condensation leg is building `levelIn` and `cover`, which this bridge carries
and does not owe (B11). **The bounded subset leg needs an ambient fact at the
successor cardinal (B5) that no leg is building, and the trophy needs a second
direction (B10) that no leg is building either.**

**ONE CHEAP THING WOULD MOVE B5 A LONG WAY.** The telescope asks for
`IsCardinal κ` and the proof spends `⟪ κ ⟫ ↪ ⟪ α ⟫ → ⊥` at one fixed α, twice
(`src/L/BoundedSubset.lagda.md:1597`, `:1601`). Weakening that one parameter is
a two-line change to a landed chapter and it re-prices B5 from "build an
ambient cardinal" to "refute one ambient injection". I did not make the change:
it lands in `src/` and this brief forbids that.

**A FOURTH LEG IS NEEDED, AND ITS NAME IS B10.** The brief asked whether the
three legs converge on a reachable target or on one that needs a fourth. **They
need a fourth.** `InjL δ (𝒫 κ)` is one of the three conjuncts of the trophy and
the bounded subset route does not touch it.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: READ. `:165` reads "| LJ-1.90 | Instantiate BoundedSubsetAt for the first time | REACHES cardκ | Every other hypothesis takes a value, including AllCodes A in Lset lam. Nothing in the tree proves any set is a cardinal |". `:167` reads "| LJ-1.91 | Gate the cardinal chapter | AMBIENT HARTOGS, 490 to 890 lines | IsCardinal is ambient, so the internal omega-1-L does not provably satisfy it. Order types are the widest term |". `:170` reads "| LJ-1.94 | Build the ambient Hartogs cardinal and end at the consumer | CARDK SUPPLIED, GREEN | 1058 lines, 27 s, no choice. But IsCardinal is stated locally, and the next blocker is Devlin55's sq |". `:198` reads "| LJ-1.121 | Supply levelIn and cover at the site | NEITHER REFUTABLE, NEITHER SUPPLIED | The wall is the LJ-1.12 crossing, the level-hood certificate, priced 2.8k to 3.3k lines and not built |". `:444` reads "| LJ-1.323 | Fable RULING: the statement of both trophies | AC UNCHANGED. GCH BECOMES THE INTERNAL EQUALITY | sq leaves, every ambient injection leaves, the conclusion is 2^kappa = kappa-plus in L |". `:465` reads "| LJ-1.8 | Build: assemble L models GCH | STATEMENT LANDED; ONE HYPOTHESIS BLOCKS THE PROOF | sq : SqShape, and LJ-1.286 measured that the delivered square law CANNOT supply it. Open work 7 |". This file carried correction 1 and it is the most valuable hit of the five.
- `archive/dev/JOURNAL-archived.md`: DECLINED. `:1` reads "# Archived journal: the retired route". `grep -n "IsCardinal\|BoundedSubset\|GCHStatement\|InjCode"` over it returns nothing, so it holds no evidence for this task.
- `archive/dev/JOURNAL.md`: DECLINED. `:1` reads "# ARCHIVED 2026-08-20". Same grep, same empty result.
- `archive/dev/DD-archived.md`: DECLINED. `:1` reads "# THE `DD` RULING SERIES, archived in full 2026-08-18". Same grep, same empty result, and the `DD` series is set aside in this form.
- `archive/dev/ORCHESTRATION.md`: DECLINED. `:1` reads "# ORCHESTRATION: the orchestrator's operating rules". It governs how the loop is operated and says nothing about either chapter.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: READ, and it settled the second half of W3. `:147` reads "> 5.5 Lemma. Assume V = L. Let κ be a cardinal. If x is a bounded subset of". `:164` reads "The application of 5.5 in 5.6 is at the cardinal κ⁺ with α = κ: every". The second quote is an independent confirmation, from the primary source, that the theorem's κ slot takes the statement's δ.
- `dev/literature/truncation-and-selection.md`: READ, for row B12. `:216` reads "**These refute the UNIVERSALLY QUANTIFIED form. They do not reach a family". `SqCollect` (`src/L/StageBound.lagda.md:44-48`) is exactly a family-indexed collection of truncations over `V ℓ`, and this file says a principle of that shape is neither refuted nor proved and must be ruled on. B12 is carried by the bridge and not owed by it, so I did not take the question further.
- `dev/literature/digest.md`: READ, briefly. `:513` reads "6. **A sourced GCH-in-L derivation**: SETTLED by [L3.30-L2]'s Devlin ch. II". It routed me to `devlin-II5.md` and carries no part of the chain itself.
- `dev/literature/devlin-errata.md`: DECLINED. `:41` reads "  section 9 of Chapter I and section 1 of Chapter VI." The errata inventory does not reach Chapter II section 5, and `devlin-II5.md:31-34` records that boundary, so there is no erratum to apply to 5.5 or 5.6.
- `dev/literature/geology.md`: DECLINED. `:1` reads "# Geology dossier: set-theoretic geology sources and the five questions". Set-theoretic geology is `[L6]` material and bears on neither chapter.
