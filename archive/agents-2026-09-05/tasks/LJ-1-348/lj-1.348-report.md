# LJ-1.348 report: `witK` is FALSE, and `graphWitK`'s field exists at another sort

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. Probe, lands
nothing. Written incrementally (C-22). Every negative is MEASURED or INFERRED,
in those words.

## 0. LEAD

**NEITHER TIE IS SUPPLIED, AND THE REASON IS NOT THE SAME FOR THE TWO.**

**`witK` IS FALSE. A COUNTERMODEL EXISTS AND AGDA CHECKED IT.**
`agents/tasks/LJ-1-348/Refute348.agda:247-252`, **exit 0 in 1.71 s**, derives
`Empty.⊥` from the tie. `:300-325` re-states `WitnessAgree`'s type and
`LeafAgree`'s type VERBATIM and discharges both. **So a third telescope needs
repair, and I land no repair.**

**THE BRIEF'S CENTRAL QUESTION IS ANSWERED, AND THE ANSWER IS 「NEITHER」.**
`[LJ-1.344]` wrote that `shapedAt` blocks the countermodel. **MEASURED FALSE.**
`shapes` is a twelve-fold disjunction and its tag-6 disjunct pins the PAYLOAD
and leaves the ARITY component free (`src/L/Coding/Shape.lagda.md:104-105`,
`:178`, `:186`). `closedAt` speaks about tags 2, 3, 4, 5, 8, 9, 10 and 11 and
**never about tag 6** (`src/L/Coding/Model.lagda.md:2182-2195`). **So the free
arity slot takes the BOUND ITSELF, and the tie closes a four-step membership
cycle.**

**AND THE CURE IS BLOCKED, SEPARATELY AND MEASURABLY.**
`agents/tasks/LJ-1-348/MustFail348.agda`, **EXPECTED RED, exit 42 in 1.11 s**,
offers the call site's own data where the cure's new hypothesis is wanted.
Agda refuses and **the error names the missing fact**. So the two halves of the
brief's disjunction are both true at once: the conjunct does not save the tie,
and the cure is not payable at the site either.

**`graphWitK`: THE BRIEF'S PREMISE AT RISK IS MEASURED FALSE, EXACTLY AS THE
BRIEF PREDICTED.** The field is absent from `KFacts`, MEASURED by reading all
29. **Its SUPPLIER is in the tree today, at another sort, and it is TWO lines.**
`agents/tasks/LJ-1-348/Field348.agda`, **exit 0 in 2.08 s**, produces the field
at `KValue`'s own frame from `γ∈λ`, which `KValue` already assumes.
**`src/L/Axioms/Basic.lagda.md:156-158` already writes the hard half INLINE and
throws the membership away.**

**BUT THE FIELD DOES NOT CLOSE `graphWitK`.** The tie has THREE conclusions
(`src/L/Condensation.lagda.md:7295-7297`), and the field closes the THIRD only.
The first two are about `d` and `e`, and they carry `witK`'s own defect.
**MEASURED, by reading the telescope.**

**COST.** Fourteen Agda invocations, longest 2.48 s. **No wall. No heap
exhaustion. The cap was never raised.** Nothing was landed in `src/`.

## 1. THE ANSWER TABLE

| claim | verdict | basis |
|---|---|---|
| `witK` is supplied | **NO. It is FALSE** | `Refute348.agda:247-252`, exit 0 |
| `shapedAt` blocks the `[LJ-1.341]` countermodel | **MEASURED FALSE** | section 2; tag 6 has a free arity slot |
| `closedAt` blocks it | **MEASURED FALSE** | tag 6 is in none of the eight clauses |
| the hole is a new discovery of mine | **MEASURED FALSE** | `src/L/Coding/CodeSet.lagda.md:21-27` states it, section 2.1 |
| the countermodel's premise is inhabited | **YES, MEASURED** | `Refute348.agda:235-238`, all three conjuncts are terms |
| the refutation reaches the chapter's own two index forms | **YES, MEASURED** | `Refute348.agda:300-325`, verbatim types |
| `[LJ-1.343]`'s cure applies to `witK` | **MEASURED FALSE at the call site** | `MustFail348.agda`, exit 42 |
| the cure is a term in isolation | **YES, MEASURED** | `Refute348.agda:338-346`, one `carrierK` call |
| `graphWitK` needs a field `KFacts` lacks | **YES, MEASURED** | 29 fields read; none gives `fst A ∈ fst K` |
| that field needs NEW mathematics | **MEASURED FALSE** | `Field348.agda:55-63`, two lines from delivered names |
| the field exists at another SORT | **YES, MEASURED** | `src/L/Axioms/Basic.lagda.md:158` writes it inline |
| one field and one line close `graphWitK` | **MEASURED FALSE** | it closes 1 of 3 conclusions, section 5.3 |
| `LeafAgree` has an intended environment to test against | **MEASURED FALSE** | zero consumers in `src/`, section 3.3 |
| anything landed in `src/` | **MEASURED FALSE** | `git status`, section 11 |
| a run hit a wall | **MEASURED FALSE** | longest 2.48 s, section 9 |

## 2. `witK`. WHY `shapedAt` DOES NOT BLOCK THE COUNTERMODEL

**THE TIE, verbatim at two sites.** `src/L/Condensation.lagda.md:6683-6685`
(`WitnessAgree`) and `:7233-7235` (`LeafAgree`):

```agda
  (witK : (w : S) → ⟨ (w ∷ γ) ⊨ ((var (suc x) ∈̇ var zero)
               ∧̇ (closedAt zero ∧̇ shapedAt zero (suc A))) ⟩
         → ⟨ fst w ∈ fst (lookup K γ) ⟩)
```

**WHAT `[LJ-1.344]` SAID.** 「It is NOT refutable by `[LJ-1.341]`'s countermodel,
MEASURED, because `shapedAt` blocks it ... `shapedAt` forces every member of
`w'` to be a shape, so `w'` cannot be the set that produces a membership
cycle.」

**THE FIRST CLAUSE IS TRUE AND THE CONCLUSION DOES NOT FOLLOW.** Every member of
`w'` must indeed be a shape. **A shape can still name the bound.** MEASURED, by
reading the definition:

- `src/L/Coding/Shape.lagda.md:104-105`:
  `unForm k rel = ∃̇ (∃̇ (arityTagAtL (suc (suc zero)) (suc zero) k zero ∧̇ rel))`.
  **The arity `N` and the payload `a` are both EXISTENTIAL**, and the only thing
  said about `N` is that the member is `pr (fst N) (pr (# k) (fst a))`.
- `src/L/Coding/Shape.lagda.md:186` puts tag 6 in `shapes` as
  `unForm 6 zeroPay`, and `:178` reads `zeroPay = var zero ≐ con (numeralL 0)`.
  **`zeroPay` pins the PAYLOAD to the numeral zero and says NOTHING about the
  arity.**
- The four disjuncts that DO reach the carrier are tags 0, 1, 10 and 11, through
  `bothTm`/`fstTm` (`:171-173`), and `isTmAt` (`:140-141`) puts their payloads
  inside `A`. **Tag 6 is not one of them.**

**SO A TAG-6 SHAPE IS `pr (fst N) (pr (# 6) (# 0))` FOR ANY `N` AT ALL, THE
BOUND INCLUDED.**

**AND `closedAt` DOES NOT REPAIR THE GAP.**
`src/L/Coding/Model.lagda.md:2182-2189` names the eight clauses:
`andClosedAt` (tag 2), `orClosedAt` (3), `impClosedAt` (4), `negClosedAt` (5),
`existClosedAt` (8), `forallClosedAt` (9), `allInClosedAt` (10),
`exInClosedAt` (11), and `:2191-2195` conjoins exactly those eight. **TAGS 0, 1,
6 AND 7 CARRY NO CLOSURE CLAUSE.** MEASURED, by reading all eight lines. So a
set whose only member carries tag 6 satisfies every clause vacuously, and
`Refute348.agda:183-212` proves each of the eight by refusing its tag.

**THE COUNTERMODEL, in full, at `Refute348.agda:128-252`.**

```agda
  c  = prʟ B (prʟ (numeralL 6) (numeralL 0))     -- B := lookup K γ
  w' = pairʟ c c
```

`c` is a tag-6 shape whose ARITY component is the bound. `w'` is its L-side
singleton, so both are elements of the carrier and not bare ambient sets. Then:

- **shaped**, at the sixth disjunct, `:217-230`. **Nothing about `A` is used.**
- **closed**, vacuously, `:183-212`.
- **the read slot is a member**, `:232-233`, from the module's one hypothesis.
- **the conclusion is a cycle**, `:247-252`:

```
  b  ∈  ⁅ b , pr (# 6) (# 0) ⁆  ∈  fst c  ∈  fst w'  ∈  b
```

four steps, refuted by `noCycle4` on `regularityV`
(`src/V/Hierarchy.lagda.md:139-144`). **`[LJ-1.341]`'s cycle lemma, unchanged.**

### 2.1 THE TREE ALREADY KNEW. The hole is recorded in a delivered chapter

**I FOUND THIS AFTER THE COUNTERMODEL WAS GREEN, BY THE C-42 EXTENT SWEEP, AND
IT IS THE STRONGEST EVIDENCE IN THIS REPORT.**
`src/L/Coding/CodeSet.lagda.md:21-27`, delivered prose, the chapter that OWNS
`hasWitnessAt`:

> The first conjunct is the load-bearing one, and it is the finding. `recover`
> does not take a member of a closed and shaped set; it takes a member handed
> over **as a key at a stated arity**, and nothing in `closedAt` or `shapedAt`
> constrains the arity slot. Shapedness binds the arity existentially and puts
> no condition on it, so a set holding a pair whose first component is not a
> numeral at all satisfies both halves, and the decode has nothing to say about
> that pair.

**That is my countermodel, stated in English, in `src/`, before this task
started.** My tag-6 member is exactly 「a pair whose first component is not a
numeral at all」: its first component is the BOUND. **So `[LJ-1.344]`'s
「`shapedAt` blocks it」 was contradicted by delivered prose two chapters away,
and nobody had read it against this tie.**

**AND THE SAME CHAPTER SAYS WHY THE UNBOUNDED WITNESS IS NOT A DEFECT THERE.**
`:14-19`: 「The second one ... is unbounded existentials and costs nothing here:
satisfaction is read at the class model, where an existential ranges over `L`
and no stage has to reflect anything.」 **The witness is unbounded ON PURPOSE at
the class model. `witK` is the attempt to bound it at a stage, and that is the
step that is false.**

## 3. WHAT THE REFUTATION COVERS, AND WHAT IT DOES NOT

### 3.1 It covers both of the chapter's index forms, verbatim

`Refute348.agda:300-325` writes `WitnessAgree`'s type and `LeafAgree`'s type out
in the chapter's own binders and index arithmetic and discharges both into
`Empty.⊥` through `Refute.witK-false`. **Exit 0. So this is not a refutation of
a paraphrase.** MEASURED.

### 3.2 The one thing it asks of the environment, said plainly

The premise's first conjunct is `fst (lookup x γ) ∈ fst w'`, and shapedness
forces every member of `w'` to be a shape. **So the countermodel needs the read
slot to hold the shape**, and `Refute348.agda:128-130` takes that equation as a
hypothesis rather than hiding it.

**`Refute348.agda:268-290` INHABITS the hypothesis** at a two-slot environment
built from one arbitrary carrier element. So the demand is met by an environment
and not by an assumption. MEASURED.

**THE HONEST LIMIT, and I state it before anyone asks.** `[LJ-1.341]` proved its
two ties empty at EVERY environment. **Mine is not, and it CANNOT be:** where
the read slot is not a shape at all, `witK`'s premise is empty and the tie is
vacuously true. **So the strongest true statement is the one I proved: no term
inhabits `witK` at every `γ`, hence no supplier exists.** That is what a module
parameter demands.

### 3.3 Why the limit costs nothing here

**`LeafAgree` HAS ZERO CONSUMERS IN `src/`, RE-MEASURED TODAY.** `grep -rn
'LeafAgree\|WitnessAgree' src/` returns hits only inside
`src/L/Condensation.lagda.md`, and inside that file `LeafAgree` appears at its
own declaration `:7224` and in three comment lines. `WitnessAgree` has exactly
ONE consumer, `LeafAgree` at `:7307`. **So there is no intended environment to
test the tie against.** The tie must hold at every `γ` or nothing can use it,
and section 2 shows it does not.

### 3.4 The stronger statement I did NOT build, and its price

**A supplier could still be argued for if the countermodel were reachable from
ANY inhabited premise.** The route is to adjoin `c` to a given witness `W₀`:
`w'' := unionʟ (pairʟ W₀ (pairʟ c c))`, which keeps `W₀`'s closure clauses
(their conclusions land in `W₀ ⊆ w''`) and adds one tag-6 member. **That would
prove: at every environment, `witK` is EMPTY or VACUOUS, never useful.**

**PRICE, INFERRED and not built:** the union membership both ways from
`union-ax` and `pairing-ax`, about 15 lines; eight closure clauses re-proved with
a lift instead of a refusal, about 8 lines each; shapedness by cases through
`shaped-out` (`src/L/Coding/Shape.lagda.md:242`), about 12 lines. **About 90
lines and three to six runs.** The basis is a line count of the analogous blocks
in this file, not a comparable elsewhere (DD8). I did not build it because the
refutation of section 2 already denies a supplier, which is the question the
brief asked.

### 3.5 THE EXTENT (C-42). The count inside `src/` is TWO

**THE SHAPE THE REFUTATION KILLS is 「a tie that concludes a membership in the
bound from `closedAt` and `shapedAt` alone」.** I read all fourteen `LeafAgree`
parameters at `src/L/Condensation.lagda.md:7233-7305` and every use of
`shapedAt` in `src/`. **The count is TWO, and they are `witK` and `graphWitK`.**
MEASURED.

| parameter | why it is not in the shape |
|---|---|
| `wCodesK`, `wUnCodesK`, `wEntryK` (`:7239-7255`) | each TAKES `⟨ fst w' ∈ K ⟩` as a premise |
| `gCodesK`, `gUnCodesK`, `gEntryK`, `domEntryK`, `domK` (`:7262-7287`) | each TAKES `⟨ fst d ∈ K ⟩` or `⟨ fst e ∈ K ⟩` |
| `twelve-out`, `twelve-back` (`:7256-7261`) | conclude a satisfaction, not a membership |
| `keyValK` (`:7298-7299`) | reads a tag and concludes about the SAME variable |
| `satK` (`:7303-7305`) | carries its carrier membership INSIDE its formula |
| **`witK` (`:7233-7235`)** | **in the shape. MEASURED FALSE** |
| **`graphWitK` (`:7288-7297`)** | **in the shape at two of three conclusions** |

**AND THE OTHER `shapedAt` CONSUMERS ARE NOT TIES.** `ShapedAgree.out` and
`.back` (`:6665`, `:6673`) convert `shapedAt` to `shapedBS` and take `codesK`
and `unCodesK`, which already carry the bound. `src/L/Coding/KeyRead.lagda.md:131`
and `src/L/Coding/Recover.lagda.md:148` take `hcl` and `hsh` to DECODE, and
section 2.1 is the record that they already pay for the free arity slot.
**Nothing landed by `[LJ-1.346]` is touched: `envK`, `defPairK` and `sgltK`
(`src/L/Condensation.lagda.md:6197-6259`) never mention a shape.** MEASURED, by
reading the module.

## 4. THE CURE. IT IS ONE CALL, AND THE SITE CANNOT PAY IT

**`[LJ-1.344]` priced the cure at 「`[LJ-1.343]`'s repair plus one `carrierK`
call」. The call is real.** `Refute348.agda:338-346` adds
`⟨ fst u ∈ fst (lookup A γ) ⟩` to the telescope and closes the tie with
`carrierK u hu`, one line, exit 0. **So the refutation is about the QUANTIFIER
and not about the formula**, the same finding `[LJ-1.341]` recorded for its two.

**AND THAT IS WHERE THE ANALOGY STOPS.** `[LJ-1.341]`'s load-bearing check was
that the new hypothesis is FREE at the call site: 「`DefinesAgree.fwd` ... both
begin `λ z (hz , hx) →`, and `hz` IS `⟨ fst z ∈ fst (lookup w γ) ⟩`」. **The
same check FAILS here, and I ran it.**

**THE SITE.** `src/L/Condensation.lagda.md:6717` reads
`go (w , (hxw , (hcl , hsh))) =` and `:6721` reads
`wK = witK w (hxw , (hcl , hsh))`. **`w` comes out of the UNBOUNDED existential
`hasWitnessAt A x`** (`:6712`), and the three things bound beside it are the
formula's three conjuncts: the read membership, the closure and the shapedness.
**None of them is a carrier membership of `w`.** MEASURED, by reading the two
lines and the `go` type at `:6714-6716`.

**THE CONTROL MEASURES IT.** `agents/tasks/LJ-1-348/MustFail348.agda` offers the
closest candidate the site has, the first conjunct, where the cure wants the
carrier membership. **Exit 42 in 1.11 s**, refused at `MustFail348.agda:59.26-32`
with

```
fst (lookup xi γ) != fst u of type V ℓ
when checking that the expression h .fst has type
⟨ fst u ∈ fst (lookup A γ) ⟩
```

**The error NAMES the missing fact.** So the green of `Refute348.agda` is not the
green of an empty file, and the gap is exactly the hypothesis the cure adds.
**EXPECTED RED. DO NOT REPAIR THAT FILE.**

**WHAT THIS MEANS FOR THE CHAPTER.** The repair `[LJ-1.343]` made moved a bound
that was already implicit at the site back into the telescope. **Here there is no
such bound to move.** The witness of an unbounded existential is unbounded, which
is the whole content of the step. **So `witK` is not a transcription slip like
its two siblings; it is the un-ported half of Devlin's construction.** Section 8.

## 5. `graphWitK`. THE FIELD, AND WHAT IT DOES NOT BUY

### 5.1 The field is absent from `KFacts`, and I read all 29

`src/L/Condensation.lagda.md:6079-6115`: twelve `tagEq`, twelve `numK`, then
`innerK`, `innerPairK`, `pairK`, `carrierK`, `arityK`. **`carrierK` carries
MEMBERS of the carrier into the bound; `arityK` carries members DOWN out of a
member of the bound. Neither puts the carrier itself in.** MEASURED, by reading
all 29 fields.

### 5.2 The supplier EXISTS, at another sort, and it is two lines

**THE BRIEF NAMED THIS AS ITS PREMISE MOST LIKELY TO BE WRONG, AND IT IS
WRONG IN THE CHEAP DIRECTION.**

**`src/L/Axioms/Basic.lagda.md:156-158` already needs the hard half and writes it
INLINE:**

```agda
  isL-Lset : (β : V ℓ) → IsOrd β → ⟨ isL (Lset β) ⟩
  isL-Lset β oβ = 𝒟ₒ→isL β oβ (Lset β)
    (𝒟ₒ-intro (Lset β) (Lset β) ∣ ⊤̇ , DefOf.defSet⊤≡A (Lset β) ∣₁)
```

**The parenthesis is `⟨ Lset β ∈ 𝒟ₒ (Lset β) ⟩`: the stage is a definable subset
of itself, by the formula `⊤̇`.** The chapter builds it, uses it to get `isL`,
and throws the membership away. **Named and carried one step by `Lset-in`
(`src/L/Constructible.lagda.md:319`), it IS the field.**

`agents/tasks/LJ-1-348/Field348.agda:55-63`, **exit 0 in 2.08 s**:

```agda
Lset∈𝒟ₒ : (β : V ℓ) → ⟨ Lset β ∈ 𝒟ₒ (Lset β) ⟩
Lset∈𝒟ₒ β = 𝒟ₒ-intro (Lset β) (Lset β) ∣ ⊤̇ , DefOf.defSet⊤≡A (Lset β) ∣₁

bound-mem : (lam gam : V ℓ) → ⟨ gam ∈ lam ⟩ → ⟨ Lset gam ∈ Lset lam ⟩
bound-mem lam gam h = Lset-in lam gam (Lset gam) h (Lset∈𝒟ₒ gam)
```

**ITS ONLY HYPOTHESIS IS `⟨ gam ∈ lam ⟩`, WHICH `KValue` ALREADY ASSUMES AS
`γ∈λ`** (`src/L/Condensation.lagda.md:7383`). **No `IsOrd`, no successor step, no
limit.** `Field348.agda:79-88` produces the field at `KValue`'s own frame and its
own indices `iA` and `iK`, which is the test `[LJ-1.344]` set for a supply.

### 5.3 THE FIELD CLOSES ONE CONCLUSION OF THREE

**`graphWitK` (`src/L/Condensation.lagda.md:7288-7297`) concludes a TRIPLE:**

```agda
         → ⟨ fst d ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
           × ⟨ fst e ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
           × ⟨ fst f ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
```

**The first conjunct of its premise (`:7289`) pins `f` to the CARRIER**, so the
third conclusion is the field and one `subst`. `Field348.agda:106-114` writes
that term: 4 lines, exit 0.

**THE FIRST TWO CONCLUSIONS ARE NOT BOUGHT, AND THEY ARE `witK`'s DEFECT.**
`d` carries `closedAt` (`:7290`) and NO shapedness at all; `e` is tied to `d` by
`domAt` (`:7291`) and to two `γ` slots by `appAt` (`:7292-7293`); `twelveAt`
(`:7294`) relates the three. **Nothing bounds `d` or `e` above.** MEASURED, by
reading the telescope. **So `[LJ-1.344]`'s 「one field and one line close it」 is
MEASURED FALSE: one field and four lines close ONE THIRD of it.**

**IS `graphWitK` ALSO FALSE? INFERRED YES, NOT MEASURED.** Its `d` premise is
`closedAt` alone, which section 2 shows is vacuous on a tag-6 singleton, so the
same cycle is available at `fst d ∈ K`. **What I did not measure is `domAt`,
`appAt` and `twelveAt` at that `d`**, and they are three more predicates to
inhabit. **PRICE, INFERRED: the eight vacuous closure clauses transfer unchanged
from `Refute348.agda:183-212`; `twelveAt` is twelve more clauses of the same
refusal shape plus one real case; `domAt` and `appAt` need a one-entry function
built on the L side. About 120 lines and one to three runs.** I did not build it.

### 5.4 The price of the field, MEASURED

**PRODUCERS IN `src/` ARE EXACTLY TWO.** MEASURED, by grep of `KFacts` over
`src/` and reading every hit:

| producer | at | new line |
|---|---|---|
| `KFactsCons`, the one-slot lift | `src/L/Condensation.lagda.md:6129-6157` | `boundK = f .boundK`, because `lookup (suc A) (c ∷ γ)` is `lookup A γ` |
| `KValue.facts` | `:7411-7425` | `boundK = bound-mem lam gam γ∈λ` |

**Everything else that mentions `KFacts` in `src/` TAKES it and does not build
it**: `ShapesAgree` (`:6264`), `ClosedAgree` (`:6553`), `ShapedAgree` (`:6654`),
`WitnessAgree` (`:6682`), `LeafAgree` (`:7226`). **A consumer of a record does
not change when the record gains a field.** MEASURED.

**SO THE FIELD COSTS: 2 lines of declaration, 1 line at `KFactsCons`, 1 line at
`KValue.facts`, and 2 lines of supplier.** The supplier's home is
`src/L/Axioms/Basic.lagda.md`, beside `isL-Lset` at `:156-158` which already
writes half of it; **the chapter imports that module at `:7376` already**, so the
landing adds one name to an existing `using` list and NO import line. MEASURED,
by reading `:7375-7377`.

**WHAT IT DRAGS IN THAT A COUNT DOES NOT SHOW.** `KFactsCons` is applied SIX
times inside the chapter (`:6668`, `:6676`, `:6726`, `:6731`, `:6754`, `:6759`)
and each application re-checks the record. **A new field is a new component in
each of those six, and `[LJ-1.346]` measured the whole-chapter cold check at
132.82 s against a 132.11 s baseline, a delta under its own floor.** **INFERRED
that one more field stays inside that noise. I did not re-check the chapter, and
nothing here is a cold figure for it.**

**AND SEVENTEEN FROZEN PROBE RECORDS IN `agents/` BUILD THE RECORD BY HAND.**
MEASURED, by grep of `arityK =` over `agents/tasks/`. **They are records and a
record is never rewritten.** They would simply stop typechecking against a newer
chapter, which is already true of them for other reasons
(`[LJ-1.346]` section 10).

## 6. WHERE EACH SUPPLY BELONGS, IF THE ORCHESTRATOR LANDS ANYTHING

**FOR `witK`: NOTHING. Do not land a supply.** The tie is false. What the chapter
needs is a RESTATEMENT, and it is not mine to choose:

- **The honest restatement** is Devlin's own: the witness is not any set with the
  body, it IS the bounded set. That means changing `hasWitnessAt`
  (`src/L/Coding/CodeSet.lagda.md`) or the step that consumes it, not adding a
  hypothesis to `witK`.
- **The cheap restatement**, adding `⟨ fst w ∈ fst (lookup A γ) ⟩`, TYPECHECKS
  (`Refute348.agda:338-346`) and **has no supplier at `:6721`**
  (`MustFail348.agda`, exit 42). **A brief that orders it will get a second
  unsuppliable tie one level up.**

**FOR `graphWitK`: the FIELD may land, and it closes one conclusion of three.**
If the orchestrator wants it:

1. `bound-mem` and `Lset∈𝒟ₒ` into `src/L/Axioms/Basic.lagda.md`, after
   `isL-Lset` at `:158`, 4 lines.
2. `boundK` into the `KFacts` record at `src/L/Condensation.lagda.md:6115`,
   2 lines, and one line each at `:6157` and `:7425`.
3. `:7376`'s `using ( LsetS )` gains `bound-mem`.

**I LANDED NONE OF THIS. `src/` is untouched.**

## 7. THE NEGATIVE CONTROLS, AND THE NON-VACUITY

**CONTROL A: THE GATE IS LIVE, AND IT NAMES THE MISSING FACT.**
`MustFail348.agda`, **EXPECTED RED, exit 42 in 1.11 s**, section 4. This is the
control the brief asked for: it measures that the cure's hypothesis has no
supplier at the site, which is a fact about the PROOF and not about the type.

**CONTROL B: NON-VACUITY OF THE REFUTED PREMISE, THREE LAYERS.** A hypothesis can
look refutable because nothing meets its premise, and `[LJ-1.338]`'s third
control tested exactly that failure.

1. `Refute348.agda:217-230` builds the shapedness witness at the sixth disjunct,
   with a real `UnWit` and not a truncation trick.
2. `:183-212` builds all eight closure clauses.
3. `:235-238` builds the whole premise as one term, and `:268-290` inhabits the
   module's one hypothesis at a concrete two-slot environment. **So the
   countermodel is applied to an inhabited premise.** MEASURED.

**CONTROL C: THE REFUTATION DOES NOT KILL EVERY VERSION.**
`Refute348.agda:338-346` is a TERM of the cured statement. **A refutation that
also killed the repaired form would mean the shape is unsalvageable; it does
not.** MEASURED.

**CONTROL D: THE BOUND IS NOT MADE EMPTY.** `Refute348.agda:257-258` is
`∈-irrefl b`, so what the hierarchy refuses is the cycle and nothing wider.
MEASURED.

**CONTROL E, on the `graphWitK` side: THE FIELD IS PRODUCED, NOT ASSUMED.**
`Field348.agda:87-88` is a closed term at `KValue`'s own frame with no free
hypothesis but `KValue`'s own six parameters. **`exit 0` on a parameters-green
would prove nothing (C-45); this is a value.** MEASURED.

## 8. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md`, read `:238-256`.**

**THE ONE LINE THE BRIEF ASKS FOR: `witK` is the port of NEITHER. It is the port
of a step Devlin does not take.** `:246-251` says 2.2 to 2.4 write
`D(v, u) = "v = Def(u)"` as Σ₁ and 「then bind every unbounded quantifier by the
concrete set K(u) ... The Σ₀ matrix C(w, v, u) **with w = K(u)**」. **Devlin's
`w` IS `K(u)`, fixed by the construction.** He never proves that an arbitrary
closed shaped set is a member of `K(u)`, because he never quantifies over one.
**Our `witK` asks exactly that, and section 2 shows it is false.** So this is the
same class of defect `[LJ-1.341]` found and one layer worse: there the binder was
dropped from a premise, here the WITNESS was set free.

**`graphWitK`'s FIELD is the port of something the tree PROVES, not of something
Devlin assumes.** `Lset gam ∈ Lset lam` is a tower fact, and
`src/L/Axioms/Basic.lagda.md:156-158` proves its hard half today. It is not a
`K(u)` closure property at all, which is why it does not sit naturally in
`KFacts` and why its home is the tower chapter.

**WHY NOT the rest of the digest.** `:236-240` is the union law at limit stages,
settled and not about closure. `:241-244` is the `[LJ-1.12]` Δ₀ question,
settled. `:258` onward is Step D, the hull with least witnesses, which needs a
definable well-order and which no tie of `LeafAgree` reaches. **The cardinality
halves of 5.5 and 5.6 are another step, and C-46 forbids using Devlin's tower
axis as DD4's.**

## 9. SECONDS, LOAD, RUNS

One agda process at a time, always `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.
`ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l` run before every
invocation **except the two floor re-runs**, which I fired within seconds of a
count that returned 1 and which I record here rather than claim a count I did
not take. **The counts returned 1 nine times and 0 once**, the 0 immediately
before the three confirmation runs. A sibling held the other slot throughout, so
C-12's cap of two was never exceeded.

**THE FLOOR, AND IT DISAGREES WITH THE TWO PRIOR TASKS BY TEN TIMES.**
`agents/tasks/LJ-1-348/Floor348.agda`, an empty module: **0.07 s**, measured
twice and once with its interface deleted first. `[LJ-1.346]` measured 0.78 s and
`[LJ-1.344]` 0.92 s for the same file shape. **MEASURED: the machine is not the
machine those tasks measured, so NO seconds figure of mine is comparable with
theirs, and I offer none as such** (C-53).

| run | exit | seconds |
|---|---:|---:|
| `agents/tasks/LJ-1-348/Floor348.agda` (first) | 0 | 0.06 |
| `agents/tasks/LJ-1-348/Floor348.agda` (cache hit) | 0 | 0.09 |
| `agents/tasks/LJ-1-348/Floor348.agda` (cold, interface deleted) | 0 | 0.07 |
| `agents/tasks/LJ-1-348/Refute348.agda` (scope slip, `_+_`) | 42 | 1.14 |
| `agents/tasks/LJ-1-348/Refute348.agda` | **0** | **1.71** |
| `agents/tasks/LJ-1-348/Field348.agda` (scope slip, `IsOrd`) | 42 | 2.03 |
| `agents/tasks/LJ-1-348/Field348.agda` (scope slip, `sucV`) | 42 | 2.01 |
| `agents/tasks/LJ-1-348/Field348.agda` (PARTS 1 and 2) | **0** | **2.12** |
| `agents/tasks/LJ-1-348/Field348.agda` (with PART 3) | **0** | **2.08** |
| `agents/tasks/LJ-1-348/MustFail348.agda` (scope slip, `_∈_`) | 42 | 1.08 |
| `agents/tasks/LJ-1-348/MustFail348.agda` (**EXPECTED RED**) | **42** | **1.11** |
| `agents/tasks/LJ-1-348/Refute348.agda` (CONFIRM, interfaces deleted) | **0** | 2.48 |
| `agents/tasks/LJ-1-348/Field348.agda` (CONFIRM, interfaces deleted) | **0** | 1.94 |
| `agents/tasks/LJ-1-348/MustFail348.agda` (CONFIRM, **EXPECTED RED**) | **42** | 1.00 |

**NO INVOCATION CAME NEAR THE 30-MINUTE WALL; the longest was 2.48 s. NO heap
exhaustion. Nothing was interrupted. The cap was never raised.**

**THE CACHE TRAP, honoured.** Every file of mine loads `L.Coding.Model`,
`L.Coding.Shape` and, for `Field348.agda`, `L.Condensation` from their committed
interfaces. **No figure here is a cold check of the chapter, and none is offered
as one.** I ran no whole-chapter check, because nothing was landed.

## 10. DD4, WITH THE AXIS NAMED (C-46)

**THE AXIS IS AC-AGAINST-GCH, fixed at `scripts/measure/ledger.py:50`.**

**THE COUNTERMODEL IS CLASS-FREE, so the finding serves both ends at once.**
MEASURED, by reading `Refute348.agda`: it names `pr`, `prʟ`, `pairʟ`,
`numeralL`, `⁅_,_⁆`, `regularityV`, `closedAt` and `shapedAt`. **Not one of them
mentions AC, GCH, a well-ordering or a cardinal.** So `witK` is false at BOTH
carriers by one file, and no second refutation is owed.

**THE PROPOSED FIELD KEEPS THE RECORD GENERIC, AND I SAY SO EXPLICITLY AS THE
BRIEF ORDERS.** `boundK : ⟨ fst (lookup A γ) ∈ fst (lookup K γ) ⟩` names only
`fst`, `∈` and `lookup`, exactly like the 29 fields beside it. **It is
class-free.** MEASURED.

**ITS OBLIGATION SIDE IS WHERE A NEW FIELD COULD BREAK DD4, and today it does
not.** `src/` has exactly ONE non-lift producer of the record, `KValue`
(section 5.4), and section 5.2 discharges it. **A future producer at the ambient
carrier would owe the analogous fact about its own two stages. INFERRED that it
is available there too, by the same tower argument; I did not build it, and no
such producer exists in `src/` today.**

**`dev/ledger.toml:204` UNDERSTATES, as the brief notes.** The GCH closure is
read from a STATEMENT whose proof is not wired. **I did not re-measure the ledger
and I quote no new figure from it.**

**WHAT THIS TASK DOES FOR DD4'S SHARING.** Nothing lands, so no line is shared or
unshared. **What it removes is a FALSE line from the shared side:** `witK` was
going to be assumed at both carriers, and a false hypothesis assumed twice is
worse than one assumed once.

## 11. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| `shapedAt` blocks the countermodel | **MEASURED FALSE.** Tag 6's arity slot is free |
| `closedAt` blocks it | **MEASURED FALSE.** Tag 6 has no clause |
| the arity hole was unrecorded before this task | **MEASURED FALSE.** `src/L/Coding/CodeSet.lagda.md:21-27` |
| `witK` is true as stated | **MEASURED FALSE.** `Refute348.agda:247-252` |
| the refutation is of a paraphrase | **MEASURED FALSE.** Both chapter types, verbatim, discharged |
| the refuted premise is empty | **MEASURED FALSE.** Three layers of witness, section 7 |
| the refutation kills the cured statement too | **MEASURED FALSE.** Control C, a term |
| the cure is payable at the call site | **MEASURED FALSE.** `MustFail348.agda`, exit 42 |
| the tie is empty at EVERY environment | **MEASURED FALSE**, and it cannot be; section 3.2 |
| `LeafAgree` has an intended environment | **MEASURED FALSE.** Zero consumers, re-measured today |
| `KFacts` has a field for `graphWitK` | **MEASURED FALSE.** All 29 read |
| the field needs new mathematics | **MEASURED FALSE.** `Field348.agda`, exit 0, two lines |
| the field needs `IsOrd` or a successor step | **MEASURED FALSE.** `Lset-in` needs only `gam ∈ lam` |
| one field and one line close `graphWitK` | **MEASURED FALSE.** One of three conclusions |
| `graphWitK` is refuted here | **MEASURED FALSE.** INFERRED false, section 5.3; I built no countermodel for it |
| the new field breaks genericity | **MEASURED FALSE** today. One producer, discharged |
| a consumer of `KFacts` must change | **MEASURED FALSE.** Five consumers take the record and build none |
| anything landed in `src/` | **MEASURED FALSE.** `git status --short` shows `agents/tasks/LJ-1-348/` only |
| a run hit a wall | **MEASURED FALSE.** Longest 2.48 s |
| the chapter was re-checked | **MEASURED FALSE.** Nothing landed; I ran no chapter check |
| the two arity-numeral conjuncts were touched | **MEASURED FALSE.** A sibling has them; I did not open them |

## 12. WHAT I DID NOT SETTLE

- **`graphWitK`'s truth.** INFERRED false at its first conclusion, priced at
  about 120 lines in section 5.3, not built.
- **The 「empty or vacuous at every environment」 strengthening for `witK`**,
  priced at about 90 lines in section 3.4, not built.
- **The right restatement of the witness step.** Section 6 says what the two
  candidates are and stops. DD23 and the brief reserve the chapter for the
  orchestrator.
- **The two arity-numeral conjuncts.** A sibling has them. I did not open them.
- **Whether the ambient carrier can supply the proposed field.** INFERRED yes;
  no ambient producer exists in `src/` to ask.
- **The chapter's green with the field landed.** Nothing landed and I ran no
  chapter check.

## 13. ARCHIVE USED (DD18)

One line read per archived file, as the brief orders.

- **`agents/tasks/LJ-1-344/lj-1.344-report.md`, read WHOLE.** **Line read:** its
  section 6.1, 「I did NOT refute it, and I say why. The easy countermodel is
  closed off: `shapedAt` forces every member of `w'` to be a shape ... THE CURE
  IS `[LJ-1.343]`'s, and then the supply is ONE line.」 **TOOK** the reading of
  the telescope, which is correct, and the cure, which is one line.
  **CORRECTED BOTH CONCLUSIONS:** `shapedAt` does not close the countermodel off
  (section 2), and the one line has no supplier at the site (section 4).
- **`agents/tasks/LJ-1-346/lj-1.346-report.md`, read WHOLE.** **Line read:** its
  section 3.1, 「`src/L/Condensation.lagda.md:2837-2839` is `ChainZ.pair∈pr` ...
  a TOP-LEVEL module of the chapter that is NOT private」, with its ruling that
  the block stays private and that `ChainZ`'s `arityK` parameter is real
  friction. **TOOK** the ruling and did NOT open `src/V/Coding.lagda.md`.
  **REJECTED the access:** my file has no `arityK` to invent, so it re-writes
  `pair∈pr` in three lines and says so at `Refute348.agda:84-92`, which is the
  friction that report predicted.
- **`agents/tasks/LJ-1-341/lj-1.341-report.md`, read WHOLE.** **Line read:**
  `ProbeTies341.agda:94-96`, `noCycle4`, and section 4's load-bearing check,
  「THE NEW HYPOTHESIS IS FREE AT BOTH CALL SITES, AND THIS IS THE LOAD-BEARING
  CHECK」. **TOOK** the cycle lemma unchanged and the check itself. **APPLIED THE
  CHECK AND GOT THE OPPOSITE ANSWER** at `witK`'s site, which is section 4.
- **`archive/dev/TASKS-archived.md`, read the header at `:1-20`.** **TOOK SHAPE
  ONLY:** 「The 264 rows below record every dispatch made on the retired route」,
  a dispatch history read for the practice of naming what a countermodel needs of
  its environment. **REJECTED every figure:** that route has a different carrier,
  a different coding and no `KFacts` record, so no count and no seconds figure
  from it prices anything here.

## 14. PROHIBITIONS, ANSWERED

I wrote only inside `agents/tasks/LJ-1-348/`: this report, `Refute348.agda`,
`Field348.agda`, `MustFail348.agda` and `Floor348.agda`. **`src/` holds no probe
of mine and I opened no file under `src/` for writing.** I read
`src/L/Condensation.lagda.md`, `src/L/Coding/Shape.lagda.md`,
`src/L/Coding/Model.lagda.md`, `src/L/Coding/Bound.lagda.md`,
`src/L/Constructible.lagda.md`, `src/L/Axioms/Basic.lagda.md`,
`src/L/Ordinal/Stages.lagda.md`, `src/V/Coding.lagda.md`,
`src/FOL/Semantics.lagda.md`, `src/FOL/Absoluteness.lagda.md` and
`src/FOL/ZFStructure.lagda.md`. I READ and did not edit
`agents/tasks/LJ-1-341/`, `LJ-1-344/`, `LJ-1-346/` and `LJ-1-338/`. **I did not
touch the two arity-numeral conjuncts**, which a sibling has. I did not open
`src/Everything.lagda.md`, `dev/`, `AGENTS.md` or `.claude/` for writing. **No
commit, no push, no `git checkout`, `stash`, `reset` or `clean`. No `make
check`.** No em dash in any language.
