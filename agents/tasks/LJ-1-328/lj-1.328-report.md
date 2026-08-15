# LJ-1.328 report: the definable well-order of L, as a formula

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. Probe. It lands
nothing. Written incrementally (C-22).

## VERDICT: DELIVERED

**The definable well-order of L is ALREADY an element of the model, at EVERY
ordinal, with BOTH adequacy directions. It is ALREADY described by a formula in
the object language, in two different languages, one of them with a Σ₁
certificate.** The task's own object is on the tree and green.

**And NONE of the three consumers the brief names is unblocked by it. MEASURED.**
Two of the three want a different object, and they want the SAME different
object. The third wants a third object. Section 6 gives the evidence.

I also BUILT the one residual the object has, because it is small: the same
order as ONE formula with the STAGE AT A SLOT. 63 code lines, exit 0, 2.11 s.

## 1. WHAT `orderL` IS, AND WHY IT IS NOT EVEN THE BEST ANSWER

`orderL : S` at `src/L/Choice/Order.lagda.md:693-694` is the order at ONE stage,
the bounding ordinal of one constructible set. The brief asks whether the object
needed is the order UNIFORMLY, and says to name the gap.

**THERE IS NO GAP AT THAT LEVEL. `orderL` is ONE INSTANCE of a UNIFORM family
that the same chapter exports.** MEASURED:

```agda
orderL = relL boundOrd boundOrd-isL boundOrd-ord
```

`src/L/Choice/Order.lagda.md:694`. The general term is

```agda
relL : (α : V ℓ) → ⟨ isL α ⟩ → IsOrd α → S
```

`src/L/Choice/Table.lagda.md:795-796`, with both readings at
`:825-827` (`relL-fill`) and `:829-832` (`relL-rep`). The chapter says so in its
own prose: "the relation it carries at every ordinal",
`src/L/Choice/Order.lagda.md:638-639`.

**The uniform family is CONSUMED today.** `src/L/Hull.lagda.md:440` reads
`ordL = fst (relL o o-isL o-ord)` inside `module OrderAt (o : S) ...`, generic in
the ordinal. So the uniform form is not a paper claim. It carries a chapter.

## 2. THREE DELIVERED LAYERS, NOT ONE

| layer | term | where | both directions |
|---|---|---|---|
| the order at ONE stage, as an L-set | `orderL : S` | `src/L/Choice/Order.lagda.md:693` | `:696`, `:700` |
| the order at EVERY ordinal, as an L-set | `relL` | `src/L/Choice/Table.lagda.md:795` | `:825`, `:829` |
| the order as a FORMULA, generic in the ordinal, with a Σ₁ certificate | `φ< : Formula S 2` | `src/L/Hull.lagda.md:450-451` | `:463`, `:473` |

**`L.Hull` is wired.** `src/Everything.lagda.md:376` imports it. So layer three
is delivered and green, not a probe.

**And the two formula layers are in DIFFERENT LANGUAGES, which matters.**
MEASURED by reading the two module headers:

- `src/L/Hull.lagda.md:52` opens `hPropStructure 𝒮ᵥ`, so its `S` is `V ℓ` and
  `AtS.⊨` at `:54` is AMBIENT satisfaction. `φ<` is an ambient formula that
  names the order element as a CONSTANT, `con ordL`. It is the atom the hull's
  elementarity argument reads.
- `src/L/Choice/Order.lagda.md:83` opens `hPropStructure 𝒮ʟ`, so its `S` is the
  model's carrier, and `_⊨_` at `:86` is satisfaction RELATIVIZED to L. `Stp`,
  `Cond` and `GraphAt` live there. They are the descriptions that CARVE `relL`
  out through `hasSeparationL`.

**So "described by a formula in the object language" is true twice over, in two
senses, and the brief's question has a YES in both.**

## 3. WHAT RAN, AND THE MACHINE LOAD BESIDE EVERY FIGURE

The probe is `agents/tasks/LJ-1-328/ProbeLJ1328A.agda`, 140 non-blank lines.
Load counted before EVERY invocation with the brief's command,
`ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`. It returned 1 every
time, so I took the free slot and never took two. `GHCRTS="-A64m -I0 -M8g"` on
every run. One process. No heap wall. The longest single invocation was 2.15 s,
which is far under the 30-minute line.

| run | what | exit | real s | load before |
|---|---|---:|---:|---:|
| 1 | part 1, module name wrong | error | 0.08 | 1 |
| 2 | part 1, GREEN | 0 | 1.93 | 1 |
| 3 | part 2 formula, `GraphAt` not exported | error | 2.00 | 1 |
| 4 | part 2 formula, GREEN | 0 | 1.97 | 1 |
| 5 | both directions, `IsTable` not exported | error | 1.93 | 1 |
| 6 | both directions, GREEN | 0 | 2.11 | 1 |
| 7 | exit code captured | **0** | 2.0 | 1 |
| 8 | **NEGATIVE CONTROL 1** | **error** | 1.92 | 1 |
| 9 | **NEGATIVE CONTROL 2** | **error** | 2.01 | 1 |
| 10 | Levy imports added, GREEN | 0 | 2.15 | 1 |
| 11 | **NEGATIVE CONTROL 3** | **error** | 2.11 | 1 |
| 12 | restored, GREEN, exit captured | **0** | 2.01 | 1 |

Every figure is WARM. Every interface was already built. No cold cost is
measured here.

## 4. THE THREE NEGATIVE CONTROLS

**Runs 8, 9 and 11 are the point of the table.** A green typecheck alone proves
nothing about whether the term says what I claim.

**CONTROL 1, on the built residual.** I swapped the two order arguments in the
pair atom of `ltAt`, from `prAtL zero (suc (suc u)) (suc (suc v))` to
`prAtL zero (suc (suc v)) (suc (suc u))`. Agda refused at line 126, the `hpr`
witness inside `ltAt-fill`:

```
error: [UnequalTerms] u != v of type Fin n
when checking that the expression hpr has type
⟨ (thePair ∷ r₀ ∷ γ) ⊨ prAtL zero (suc (suc v)) (suc (suc u)) ⟩
```

That is the exact point the swap breaks. **So the formula really is elaborated
and the adequacy proof really reads the ORDER OF THE PAIR.**

**CONTROL 2, on the DELIVERED claim of section 1.** I reversed the coded pair in
the hand-written type `IsOrderElement`, from `pr (fst a) (fst b)` to
`pr (fst b) (fst a)`. Agda refused at line 61, on `relL-fill` itself:

```
error: [UnequalTerms] fst a != fst b of type V ℓ
when checking that the expression relL-fill α hα oα has type
(a b : Mem (Lset α)) → ... → ⟨ pr (fst b) (fst a) ∈ fst (relL α hα oα) ⟩
```

**So `relL-fill` really carries the direction of the order, and my one-line
derivation of the target is not a coincidence of a loose type.**

**CONTROL 3, and it MEASURES the residual rather than checking a term.** I wrote
`Σ₁-ltAt : Σ₁ ltAt` and tried to build it. Agda refused and named the blocker:

```
error: [UnequalTerms]
(_t Formula.∈̇ _u) != (∃̇ (R.ApproxAt zero (suc (suc b)) ∧̇ StepAt (suc zero) (suc (suc b)) zero))
when checking that the expression δ-∈ has type Δ₀ (R.GraphAt zero (suc b))
```

**That is the whole of section 7 in one error.** `R.GraphAt` is not an atom; it
opens with an unbounded `∃̇` over an approximation, and `R.ApproxAt` then puts
TWO unbounded `∀̇` under it (`src/L/Coding/Sequence.lagda.md:286-292`). `Δ₀` has
no `∀̇` constructor and `Σ₁` has only `σ-Δ₀` and `σ-∃`
(`src/FOL/LevyHierarchy.lagda.md:47-75`). So no witness exists.

## 5. THE ONE RESIDUAL, AND I BUILT IT

**THE GAP, at `file:line`.** The delivered `φ<` pins the order element as a
CONSTANT, `con ordL`, at `src/L/Hull.lagda.md:451`. So it is ONE FORMULA PER
STAGE. What no delivered term gives is the order as ONE formula with the stage,
the first member and the second member ALL AT SLOTS.

**I BUILT IT. 63 code lines, exit 0, 2.11 s**, at
`agents/tasks/LJ-1-328/ProbeLJ1328A.agda:78-158`. `module Uniform (b u v) (γ)`
gives:

```agda
ltAt : Formula S n
ltAt = ∃̇ ( R.GraphAt zero (suc b)
         ∧̇ ∃̇∈ (var zero) (prAtL zero (suc (suc u)) (suc (suc v))) )
```

with `ltAt-fill` at `:122` and `ltAt-rep` at `:134`, both directions against the
sealed ambient `orderAt`. **It is a ONE-CONJUNCT edit of the delivered `φ<`:**
the constant `(var zero ≐ con ordL)` becomes the delivered graph
`R.GraphAt zero (suc b)`, which already carries the stage and the order element
at slots, with `graph-only` (`src/L/Choice/Table.lagda.md:497`) and
`graph-table` (`:514`) as its two readings.

**The seal cost me nothing, and I report that plainly (P-y).** I did not need to
look inside `orderAt`. Every statement I made about it goes through
`relL-fill`, `relL-rep`, `rel-rep` and `graph-only`, which are all stated at the
sealed `orderAt` and proved inside the delivered chapters. **So the seal on
`orderAt` is priced at ZERO definitions looking inside it, for this object.**
MEASURED: my probe has no `unfolding` clause.

**One thing I had to work around, and it is a real finding.** `GraphAt` is NOT
exported from `L.Choice.Order`: `Described` opens it with `open A using (...)`
and no `public`, at `src/L/Choice/Table.lagda.md:406-409`. I re-instantiated the
same generic module at the same delivered step,
`module R = RecShape StepAt` (`ProbeLJ1328A.agda:76`), and the two agree by
definition. A landing version would add `public` there, one word.

## 6. DOES ONE DESCRIPTION SERVE ALL THREE CONSUMERS? NO, AND NOT ONE OF THEM.

**This is the most valuable thing in the report, and it is MEASURED at each
site.**

### 6.1 Consumers A and C are ONE object, and it is NOT this one

**Consumer A, `[LJ-1.321]`'s live route.** It needs `SWO {ℓ} (sq α)`, an AMBIENT
well-order on the AMBIENT type

```agda
sq α = Σ[ f ∈ (⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫) ] ((x y : ...) → f x ≡ f y → x ≡ y)
```

`src/L/Ordinal/SquareLaw.lagda.md:685-688`. `pullOrder`
(`src/L/Choice/Step.lagda.md:252-258`) reduces that to an INJECTION of `sq α`
into any well-ordered carrier, and `[LJ-1.321]` names the carrier the tree
offers: `Mem (Lset β)` ordered by `orderAt`
(`agents/tasks/LJ-1-321/lj-1.321-report.md:267-281`).

**`orderAt` is AMBIENT and DELIVERED. So consumer A needs NO coded order at
all.** MEASURED. What it needs is `c : sq α → Mem (Lset β)` with injectivity,
which is the coding of an ambient FUNCTION as a member of an L-set.
`[LJ-1.321]` says so in its own words: "the obligation is: code the ambient
pairing function as an L-set at a bounded stage"
(`lj-1.321-report.md:281-282`).

**Consumer C, `[LJ-1.316]`'s diagnosis, is the SAME object.** Its sentence is
"the object to be selected lives outside every well-ordered domain the tree
has", `agents/tasks/LJ-1-316/lj-1.316-report.md:206-208`, and it names the same
wall, the ambient-to-code crossing, at `:209-210`.

**So A and C are one line, not two, and the coded order is not it.** The brief
says "a coded order changes which side of that line objects sit on". **MEASURED
FALSE for A and C:** the line those two stand at is whether the FUNCTION is a
member of an L-set. Coding the ORDER does not move a function across it, because
the order they would use is already ambient and already delivered.

### 6.2 Consumer B is a different object, and this one is its INPUT

**Consumer B, the restated trophy's reverse bound.** `[LJ-1.325]` named its
widest term as the ORDER-TYPE predicate in the object language, and measured it
absent: `agents/tasks/LJ-1-325/lj-1.325-report.md:148-149` records the grep for
`otp|orderType|isWellOrderAt|woCode` coming back empty.

**That is a third object, and the coded order is a PREREQUISITE for it, not an
answer to it.** An order-type predicate says "y is the order type of x under the
order", so it needs the order as an L-set to quantify against. `relL` supplies
exactly that, at every ordinal, with both readings. **So consumer B is the one
consumer this object serves, and it serves it as an input.**

### 6.3 The count

**ONE description serves NONE of the three by itself. A and C are one object,
and it is the ambient-to-code crossing for a FUNCTION. B is another object, and
it is the order-type predicate.** The project should fund the crossing as one
line and the order-type predicate as a second. **It should fund nothing for the
coded order, because the coded order is delivered.**

## 7. WHAT「UNIFORMLY Δ₁」DEMANDS THAT A BARE WELL-ORDER DOES NOT

The brief says the phrase may be the whole specification. **It is three demands,
and Bedrock has none of the three. I mark each MEASURED or INFERRED.**

**D1. ONE formula, the SAME at every level, so it RELATIVIZES.** Devlin's
`<_L` is "uniformly Δ₁ at limit levels", `dev/literature/devlin-II5.md:264` and
`:294`. Uniform means the level is a PARAMETER of the statement, not of the
formula, so that `φ` relativized to `L_α` defines `<_α` for every limit `α`.
**Bedrock's `φ< ` is one formula PER STAGE, because it names `con ordL` and
`ordL` depends on the stage. MEASURED** at `src/L/Hull.lagda.md:450-451`.
**I closed this demand in the probe:** `ltAt` has the stage at a slot,
`ProbeLJ1328A.agda:82-84`, both directions green.

**D2. A Σ₁ FORM WHOSE WITNESS LIES INSIDE THE CARRIER.** The digest states this
as its own clause: "level-hood as Σ₁-with-Σ₀-matrix, uniform Δ₁ at limit levels,
**with the Σ₁ witness inside the carrier**", `dev/literature/devlin-II5.md:299-300`.
**Bedrock's stage-uniform form is NOT Σ₁. MEASURED by negative control 3:** the
graph's approximation carries two unbounded `∀̇`
(`src/L/Coding/Sequence.lagda.md:286-292`). The delivered `Σ₁-φ<`
(`src/L/Hull.lagda.md:460-461`) is a Σ₁ certificate for the PARAMETERIZED
formula, which is Devlin's `Δ₁^p`, not his uniform form.

**D3. A Π₁ HALF, AND THE EQUIVALENCE.** Δ₁ is Σ₁ AND Π₁. It is what lets a
`<_L` statement transfer in BOTH directions along a Σ₁-elementary embedding,
which is what part (iii) of condensation consumes:
`dev/literature/devlin-II5.md:289-292`. **NOTHING in `src/L/` carries a `Π₁`
certificate. MEASURED: `grep -rn "Π₁" src/L/ | wc -l` returns 0.** The datatype
exists only at `src/FOL/LevyHierarchy.lagda.md:77-79`.

**So the one-line answer: a bare well-order gives you the ORDER. "Uniformly Δ₁"
additionally gives you a SINGLE formula that survives relativization, a bounded
witness, and TWO-WAY transfer along an embedding. Bedrock has the order and the
single formula. It has neither the bounded witness nor the transfer.**

## 8. THE PRICE OF THE RESIDUAL, EACH TERM AGAINST ONE NAMED COMPARABLE (DD8)

| term | lines | basis |
|---|---:|---|
| D1, the stage-uniform formula with both directions | **63** | **MEASURED**, `agents/tasks/LJ-1-328/ProbeLJ1328A.agda:78-158`, exit 0, 2.11 s |
| exporting `GraphAt` | **1 word** | **MEASURED**, add `public` at `src/L/Choice/Table.lagda.md:406-409` |
| D2, a bounded matrix and its Σ₁ certificate | about 65 | **COMPARABLE**, `L.BoundedSubset.LevelHood`, `src/L/BoundedSubset.lagda.md:74-146`, **65 MEASURED**, which is the tree's one delivered example of exactly this move: bounded matrix, `Δ₀` certificate, `Σ₁` closure |
| re-proving the two graph readings against the bounded form | about 60 | **COMPARABLE**, `src/L/Choice/Table.lagda.md:496-560`, **60 MEASURED**, the two readings as they stand |
| D3, the Π₁ half and the Δ₁ equivalence | **UNPRICED** | **NO COMPARABLE EXISTS.** Zero `Π₁` certificates in `src/L/`, MEASURED. DD8 says name the basis; there is none, and I refuse to invent one |

**So D1 is DONE at 63 measured lines. D2 is about 125 against two delivered
comparables. D3 cannot be priced from the tree and needs its own probe.**

**AND THE PROJECT SHOULD NOT FUND D2 OR D3 TODAY**, because section 6 measured
that no consumer is waiting on them. They become live only when the reverse
bound's transfer step is funded.

## 9. THE ABORT CRITERION, ANSWERED ROW BY ROW

| the brief's row | outcome |
|---|---|
| **`orderL` ALREADY IS IT** | **TAKEN, and more.** `orderL` is one instance; `relL` is the uniform family; `φ<` is the formula. Sections 1 and 2 |
| **WRITABLE AND YOU BUILD THE DECISIVE PART** | **TAKEN for the one residual.** 63 lines, exit 0, section 5 |
| **IT IS EXPENSIVE** | not taken for the object. The unfunded residual D2 is about 125 against two comparables |
| **IT IS BLOCKED** | **PARTLY.** D3, the Π₁ half, has no comparable in the tree |
| **IT SERVES ONLY ONE OF THE THREE CONSUMERS** | **TAKEN, and the answer is sharper.** It serves B as an INPUT. A and C are one object and it is not this one. Section 6 |
| **A WALL** | not taken. Longest single invocation 2.15 s |

## 10. DD4

**NAME THE AXIS (C-46).** DD4's axis is AC closure against GCH closure, fixed in
code at `scripts/measure/ledger.py:50`.

**IS MY OBJECT IN THE SHARED PART? YES, AND IT IS TOWER-BLIND.** MEASURED by
reading my own module header, `ProbeLJ1328A.agda:78-80`: `module Uniform` takes
three slots, an environment, a constructibility witness and an ordinality
witness. **It names no stage, no numeral, no tower and no ω.** Its inputs are
`R.GraphAt` (generic in the step, `src/L/Coding/Sequence.lagda.md:281`) and
`relL` (generic in the ordinal).

**And the delivered object it describes is already in the shared part by
construction.** The definable well-order is what makes `L ⊨ AC` a theorem, and
`[LJ-1.321]` measured that `pullOrder`, from the AC trophy's own machinery,
already serves the GCH descent (`lj-1.321-report.md:267-281`). **So this is one
term at both ends, which is DD4's whole point.**

**WHAT I DID NOT MEASURE: the closure figures.** My term is not landed and its
placement is the orchestrator's call, so the import edges are not fixed. I do
not guess them.

## 11. WHAT I DID NOT SETTLE

1. **Whether `ltAt` can be made Σ₁.** I measured that it is NOT, at the
   delivered `GraphAt`. I did not try to build a bounded `ApproxAt`.
2. **The Π₁ half.** Not attempted, and not priceable from the tree.
3. **A cold check cost.** Every figure is warm.
4. **Whether the ambient-to-code crossing for `sq α` is writable.** That is
   section 6's object and it is NOT this task's object. I did not probe it.
5. **Whether `φ<` and `ltAt` agree.** They are in DIFFERENT satisfactions
   (ambient against L-relativized, section 2), and I did not build the bridge.

## 12. PROHIBITIONS, ANSWERED

- **Writes:** `agents/tasks/LJ-1-328/` only, two files, this report and
  `ProbeLJ1328A.agda`. Nothing in `src/`, nothing in `dev/`, no other task
  directory, no `.claude/`, no `AGENTS.md`.
- **I did not unseal `orderAt`.** My probe has no `unfolding` clause. Section 5
  reports what the seal cost: nothing, for this object.
- **I read the CURRENT `src/L/GCH.lagda.md` and `src/L/BoundedSubset.lagda.md`**
  at HEAD. `BoundedSubset`'s `LevelHood` block at `:74-146` is the comparable in
  section 8, read at HEAD.
- **I did not read or change the two sibling probes.** I did not need them: my
  object shares no term with either.
- **No commit, no push, no `make check`.** No `git checkout`, `stash`, `reset`
  or `clean`.
- **Agda:** twelve invocations, one at a time, load counted before each and
  equal to 1 every time, `GHCRTS="-A64m -I0 -M8g"`, cap never raised.
- The two backups of the negative controls sit in the session scratchpad,
  outside the repository.
- `lint-agda.py --check` passes on the probe.

## 13. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-327/lj-1.327-report.md`, READ WHOLE.** Line read
  `:403-406`: "Do not fund the square law's formula. Fund a probe on the
  definable well-order as a formula." **TOOK: the recommendation, and I report
  that its premise was half right.** Its section 6.3 called the definable
  well-order "AMBIENT and SEALED, with no formula" at `:253-255`. **That half is
  MEASURED FALSE:** `relL` is an L-set at every ordinal
  (`src/L/Choice/Table.lagda.md:795`) and `φ<` is a formula
  (`src/L/Hull.lagda.md:450`). Its `Carve` finding at `:75-97` I did not need and
  did not re-derive.
- **`agents/tasks/LJ-1-325/lj-1.325-report.md`, READ `:80-190`.** Line read
  `:134-136`: "L's own order, AS AN L-SET. `orderL : S`." **TOOK: the locator,
  and I widened it.** `[LJ-1.325]` found the instance; the family
  `relL` and the formula `φ<` it did not name.
- **`agents/tasks/LJ-1-321/lj-1.321-report.md`, READ `:240-300`.** Line read
  `:277-279`: "the obligation is: code the ambient pairing function as an L-set
  at a bounded stage." **TOOK: the statement, and it is what refutes the brief's
  claim that a coded order helps this consumer** (section 6.1).
- **`agents/tasks/LJ-1-316/lj-1.316-report.md`, READ the diagnosis.** Line read
  `:206-208`: "What blocks the classical move here is not the truncation. It is
  that the object to be selected lives outside every well-ordered domain the
  tree has." **TOOK: the sentence, and I measured that it names the SAME object
  as `[LJ-1.321]`.**
- **`archive/dev/TASKS-archived.md`, SHAPE ONLY, never a claim.** The retired
  route also carried a definable order. **WHAT WOULD NOT TRANSFER:** the retired
  route described its objects over the rud presentation, and `dev/PLAN.md:787`
  records that its code moved to `archive/src/2026-08-09-rud-route/` when the
  route changed. Every term I touched runs through `hasSeparationL` and a
  `Formula S 1`, and through `RecShape`, neither of which the rud route had in
  this form. **So no figure there prices anything in section 8.**

## 14. LITERATURE USED (DD18)

- **`dev/literature/devlin-II5.md`. IT BEARS, and it is section 7 whole.**
  READ `:255-300`, `:335-362` and `:396-412`.
  Line read `:360-362`: "The single engine II.5 leans on most is item 7: the
  uniformly-Δ₁ level formula whose Σ₁ witness is the level sequence with its
  K(u)-bound." **TOOK: the phrase, and I unpacked it into three demands**
  (section 7). Line read `:299-300` supplies the "witness inside the carrier"
  clause, which is demand D2. Line read `:289-292` supplies the two-way transfer
  along `π⁻¹ : L_β → L_α`, which is demand D3.
  **AND THE DIGEST'S DD4 TABLE BEARS TOO.** Line read `:383`: the well-order is
  "PER-TOWER content, both towers carry one". **TOOK: that is why my term is
  written generic in the step, `module R = RecShape StepAt`, and why the J tower
  would instantiate the same core.**
- **`dev/literature/truncation-and-selection.md`. IT BEARS, but NOT on the object
  this task names. WHY IT DOES NOT DECIDE ANYTHING HERE:** its diagnosis is
  about selecting from an ambient function type, which section 6.1 measures to be
  consumers A and C's object, not this one. Nothing I built needs untruncation:
  `ltAt-fill` returns a satisfaction and `ltAt-rep` returns a truncation, exactly
  as the delivered `φ<-rep` does (`src/L/Hull.lagda.md:473-475`).
- **WHY NOT re-fetched:** the digest carries locators into `dev2.txt` and I take
  only statement-level facts from it.

## 15. THE ONE-LINE RECOMMENDATION

**Fund nothing for the definable well-order as a formula. It is delivered, at
every ordinal, in both languages, and I closed its one residual in 63 lines.**
**Fund the ambient-to-code crossing for a FUNCTION, once, because
`[LJ-1.321]` and `[LJ-1.316]` are the same line and neither is waiting on an
order.**
