# LJ-1.333 report: item 2, the weakly constant endomap, at the cheaper truncation

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. Probe. It lands
nothing. Written incrementally (C-22).

## VERDICT: STATEMENT-LEVEL

**The cheapest check FIRED FIRST and it came back NO.** The consumers need the
DATA. **But the reason is not the one the brief expects, and it is not the one
five earlier tasks looked for.**

**The consumer's FINAL motive is ALREADY a proposition.** `theorem` concludes
`⟨ x ∈ˢ Lset κ ⟩`, `src/L/BoundedSubset.lagda.md:1621`. **So the brief's third
abort row would fire, if the final motive were the gate. It is not.**

**The gate is an INTERMEDIATE step.** The descent inside `Upper` carries a DATA
motive and its step eats the induction hypothesis as a Pi-indexed FAMILY of
injections (`src/L/StageCardinal.lagda.md:396-398`, `:534-536`, `:561-562`,
`:566`). **A truncated `sq` truncates that motive, and a truncated motive cannot
feed the family.** Negative control 1 puts the whole answer in one error
message, `∥ Motive δ ∥₁ !=< (Σ (⟪ Lset δ ⟫ → ⟪ δ ⟫) ...)`.

**AND THE BRIEF'S PREMISE IS HALF FALSE, in the half that funds the task.** The
SOME-member truncation needs no well-order to be PROVED. **It needs strictly
MORE than the least-member form to be UNTRUNCATED**, and one term measures the
direction: `some-is-not-weaker`, `ProbeLJ1333A.agda:184-188`.

**I did not build the map and I do not claim it cannot exist (C-36).**

## 1. THE BRIEF'S PREMISE, ANSWERED FIRST

The premise: 「the SOME-member truncation does not need a well-order at all」.

**IT SPLITS IN TWO, and the two halves have opposite answers.**

**HALF ONE, THE TRUNCATED LAW. TRUE, MEASURED.** `[LJ-1.332]`'s
`limit-truncated` needs LEM only and names no order. I did not take that on
trust. **This probe IMPORTS `LJ-1-332.ProbeLJ1332A`** (`ProbeLJ1333A.agda:35-36`)
rather than copying it, so that file re-compiled under my own hand: exit 0, 2 s.

**HALF TWO, THE UNTRUNCATION. FALSE, MEASURED, and it is the opposite of
cheaper.**

The brief infers that SOME is cheaper than LEAST because SOME asks for less.
**That inference holds for PROVING a statement and it INVERTS for untruncating
one.** Untruncation needs canonicity. **A weaker witness type carries LESS
canonicity, never more.**

**THE TERM.** `some-is-not-weaker`, `ProbeLJ1333A.agda:184-188`, green:

```agda
some-is-not-weaker : (α : S) (f : Witness α → sq α) → 2-Constant f
                   → (β : S) (oβ : IsOrd β) (β∈α : ⟨ β ∈ˢ α ⟩) (ω∈β : ⟨ ω ∈ˢ β ⟩)
                   → 2-Constant (λ e → f (inj→witness α β oβ β∈α ω∈β e))
some-is-not-weaker α f kf β oβ β∈α ω∈β u v = kf _ _
```

**The SOME-member obligation IMPLIES the fixed-member one.** And negative
control 2 measured that the converse FAILS: Agda answered `β′ != β`. **So the
implication runs one way. The cheaper truncation's `2-Constant` obligation is
STRICTLY STRONGER than the one at a fixed member.**

**WHERE THE WELL-ORDER RE-ENTERS.** Fixing the member is FREE: the members of an
ordinal already carry a well-order (`OrdSWO`,
`src/L/StageCardinal.lagda.md:228-276`, with `leastOf` imported at `:36`). **What
survives the fixing is an untruncation of a FUNCTION type.** `beta-fixed-residue`
states it exactly, `ProbeLJ1333A.agda:149-157`, green:

```agda
beta-fixed-residue : (α β : S) → IsOrd α → IsOrd β → ⟨ β ∈ˢ α ⟩ → ⟨ ω ∈ˢ β ⟩
                   → IH α
                   → (∥ InjAt α β ∥₁ → InjAt α β)
                   → ∥ InjAt α β ∥₁ → sq α
```

**That hypothesis is `[LJ-1.329]`'s refuted object, and I did not re-derive its
refutation.** `[LJ-1.329]` measured 35 `SWO` instances in `src/` with no function
carrier. **So the well-order is not avoided by the cheaper truncation. It is
postponed by one step, and it comes back at the same type.**

## 2. THE CHEAPEST CHECK: DO THE CONSUMERS NEED THE DATA? YES

### 2.1 The final motive is a proposition, and it does not decide

`final-motive-isProp`, `ProbeLJ1333A.agda:74-75`, green:

```agda
final-motive-isProp : (x κ : S) → isProp ⟨ x ∈ˢ Lset κ ⟩
final-motive-isProp x κ = (x ∈ˢ Lset κ) .snd
```

**MEASURED, by reading the consumer: `sq` enters `BoundedSubsetAt` at TWO points
only, and both sit at the site α.** `src/L/BoundedSubset.lagda.md:1410`
(`SC.Bound` takes `sq α`) and `:1513` (`code-inj` takes `stage-card-upper α`).
**Two data points into a propositional conclusion is a `PT.rec` and nothing
more.** So the brief's cheapest row had a real chance.

### 2.2 The step that refuses, and the exact principle it wants

**`stage-card-upper` is an `∈-induction` whose motive is DATA**
(`src/L/StageCardinal.lagda.md:530-532`, `:566`). Its step calls `limit-step`,
which takes a FAMILY (`:396-398`):

```agda
           → ((m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫)
```

`branch` builds that family from the induction hypothesis (`:534-536`) and
`step` joins the two (`:561-562`).

**THE UNTRUNCATED CONTROL, WRITTEN FIRST (C-56).** `descent-data`,
`ProbeLJ1333A.agda:102-103`, green, one line:

```agda
descent-data : StepShape → BranchFrom → ((δ : S) → sq δ) → (α : S) → Motive α
descent-data st bf sqD = ∈-induction (λ α ih → st α (sqD α) (bf α ih))
```

**THE TRUNCATED ROUTE NEEDS ONE MORE THING, and it is a choice principle.**
`ACBranch` at `ProbeLJ1333A.agda:109-111` and `descent-trunc` at `:113-119`,
green:

```agda
ACBranch = (α : S) → ((δ : S) → ⟨ δ ∈ˢ α ⟩ → ∥ Motive δ ∥₁)
         → ∥ ((δ : S) → ⟨ δ ∈ˢ α ⟩ → Motive δ) ∥₁
```

**That is choice over the site's own members, at an injection type.** **I state
it as a hypothesis and I never assume it.**

**MEASURED: the truncation is where `sq` ENTERS and not an artefact of my
assembly.** `step-truncates`, `ProbeLJ1333A.agda:124-125`, green: a truncated
`sq` truncates the step's output with the family still honest.

### 2.3 The DELIVERED consumer refuses it too

**Probe A measures a shape. Probe B measures the module.**
`ProbeLJ1333B.agda:49-53` instantiates `L.StageCardinal` with its real parameter
(`stage-card-at`, green, 2 s), and `:63-67` shows that the pointwise-truncated
family closes the consumer WITH the choice principle and not without it.

**Negative control 4 fed the delivered module the truncated family. Agda
refused, and it named `sq` itself:** `∥ sq δ ∥₁ !=< (Σ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫)
...)`.

**So the third abort row does NOT fire. The consumers demand data.**

### 2.4 The one sentence that states the finding

**The blocker is not the shape of the conclusion. It is the shape of the
DESCENT.** A propositional conclusion untruncates a FIXED number of data points.
**It does not untruncate a family indexed by the site.**

## 3. ITEM 2, AND WHY THE CHEAPER TRUNCATION DOES NOT OPEN IT

### 3.1 The door, stated with the delivered eliminator

`item2-door`, `ProbeLJ1333A.agda:171-173`, green:

```agda
item2-door : (α : S) (f : Witness α → sq α) → 2-Constant f
           → ∥ Witness α ∥₁ → sq α
item2-door α f kf = PT.SetElim.rec→Set (sq-set α) f kf
```

**`sq-set` is `[LJ-1.319]`'s measured precondition, imported and re-compiled
under my hand** (`ProbeLJ1333A.agda:34`). **So the door is delivered and only the
`2-Constant` map is missing.** That is the exact statement of item 2 at the
cheaper truncation.

### 3.2 The tree's ONLY canonicalizer consumes what the band negates

**This is the finding I did not expect and it is a route-level one.**

**The delivered untruncated supplier is `via-col-square`**
(`src/L/Ordinal/SquareLaw.lagda.md:960-961`). **It is the order collapse of a
Godel well-order.** `godSWO` at `:308-314` builds the order on the square;
`col∈α` at `:931-932` is the step that keeps the collapse INSIDE the site.
**I traced that step to its hypothesis and did not stop at the name.** `col∈α`
calls `col≤α` (`:922-929`), `col≤α` calls `exclude` at `:928`, and `exclude`
spends `InitialCore`'s `noinj²` parameter at `:876`. The parameter is declared at
`:705-708`. **It is `Init`'s FOURTH ROW**,
`src/L/Ordinal/SquareLaw.lagda.md:696-698`.

**The limit band is DEFINED by that row failing.** `band-kills-row4`,
`ProbeLJ1333A.agda:201-204`, green, one line.

**Negative control 3 printed the two hypotheses side by side.** I offered the
band's own hypothesis where the canonicalizer takes `Init`, and Agda expanded
`Init` in full, including row 4, against `Init α → Empty.⊥`.

**SO: item 2 searches for a canonicalizer at exactly the ordinals where the
tree's only canonicalizer is refuted by the band's DEFINITION**, and not by an
accident of proof or by a missing lemma. **That is why five attempts found
nothing. They were not unlucky.**

**I mark the limit of this claim, twice.** **MEASURED:** the delivered
canonicalizer consumes row 4, and the band negates row 4. **NOT MEASURED, and I
claim no such thing:** that no OTHER canonicalizer exists. C-36 binds, and
`agents/tasks/LJ-1-319/lj-1.319-ruling.md:71-75` records that no in-theory term
can ever refute the door.

### 3.3 What item 2 would still have to be

**A weakly constant `f : Witness α → sq α`.** By section 1 it must be constant
across witnesses at DIFFERENT members, which is strictly more than the
fixed-member obligation `[LJ-1.329]` refuted. **I did not build it. I did not
refute it.**

## 4. LINES, SECONDS AND LOAD, WITH THE UNTRUNCATED CONTROL BESIDE THEM (C-56)

Two files, both in `agents/tasks/LJ-1-333/`.

| file | total | non-blank | code |
|---|---:|---:|---:|
| `ProbeLJ1333A.agda` | 287 | 258 | 77 |
| `ProbeLJ1333B.agda` | 91 | 79 | 37 |

**The new mathematics is small on purpose.** Every heavy term is imported from a
sibling probe rather than copied, so the count is the new statements only.

Load counted before EVERY invocation with the brief's command,
`ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`. `GHCRTS="-A64m -I0
-M8g"` on every run. ONE process. Cap never raised. No heap exhaustion.

| run | what | exit | real s | agda slots before | 1-minute load |
|---|---|---:|---:|---:|---:|
| 1 | A, one scope error at `some-is-not-weaker` | error | 2 | 0 | 13.35 |
| 2 | A, binders named, **GREEN** | **0** | 2 | 0 | 11.09 |
| 3 | A, GREEN, exit code captured | **0** | 2 | 0 | 9.02 |
| 4 | A, **NEGATIVE CONTROL 1** | error | 2 | 0 | n/a |
| 5 | A, **NEGATIVE CONTROL 2** | error | 2 | 0 | n/a |
| 6 | A, **NEGATIVE CONTROL 3** | error | 2 | 0 | n/a |
| 7 | **B, GREEN** | **0** | 2 | 0 | 12.62 |
| 8 | B, **NEGATIVE CONTROL 4** | error | 2 | 0 | n/a |
| 9 | A, controls recorded in comments, **GREEN** | **0** | 2 | 0 | 16.30 |
| 10 | B, control recorded in comments, **GREEN** | **0** | 2 | 0 | 23.22 |
| 11 | A, one comment citation sharpened, **GREEN** | **0** | 2 | 0 | n/a |

**C-56 HELD, AND IT COST NOTHING HERE.** I wrote `descent-data` (untruncated)
before `descent-trunc` (truncated), and `stage-card-at` before
`stage-card-trunc`. **Both truncated forms then checked in 2 s.**

**MEASURED: no run exceeded 2 seconds and NO WALL FIRED.** `[LJ-1.332]`'s 400-
second wall came from nesting `PT.map` inside `PT.rec` over terms that mention
the ambient `S`. **My `descent-trunc` nests the same two eliminators
(`ProbeLJ1333A.agda:118-119`) and it costs 2 s**, because the step is a
hypothesis and nothing unfolds. **That is a second data point for C-56 and it
points the same way: the price is in what the eliminators must normalize, never
in the nesting itself.**

**Every figure is WARM.** Every interface under `src/` was already built. **No
cold cost is measured here** and P-l forbids pricing a landing from these
seconds.

**The machine was NOT quiet.** The 1-minute load ran between 9.02 and 23.22, and
other work held it. **I measured no check time as a price, so the load damages
no figure I report.** The agda slot count was 0 before every run.

## 5. THE FOUR NEGATIVE CONTROLS, AND WHAT EACH ONE NAMED

Each control was applied, run and reverted. All four are recorded in the probe
files, at `ProbeLJ1333A.agda:213-287` and `ProbeLJ1333B.agda:69-91`, because
nothing typechecks these files once the task closes. **ALL FOUR MEASURE.**

**CONTROL 1, ON THE CHEAPEST ABORT ROW.** I ran the truncated descent without
the choice principle and changed nothing else. Agda answered in 2 s:

```
error: [UnequalTerms]
∥ Motive δ ∥₁ !=<
(Σ (⟪ Lset δ ⟫ → ⟪ δ ⟫)
 (λ f → (x y : ⟪ Lset δ ⟫) → f x ≡ f y → x ≡ y))
when checking that the expression ih has type
(δ : S) → ⟨ δ ∈ˢ α ⟩ → Motive δ
```

**THAT IS THE ANSWER TO THE CHEAPEST CHECK, IN ONE ERROR MESSAGE.** The step
wants the family; the hypothesis offers a family of bars.

**CONTROL 2, ON THE DIRECTION OF THE OBLIGATION.** I tried the converse of
`some-is-not-weaker`. Agda refused, 2 s:

```
error: [UnequalTerms]
β′ != β of type (Cubical.HITs.CumulativeHierarchy.Base.V ℓ)
when checking that the expression e′ has type InjAt α β
```

**The machine names the two members that cannot be identified.** That is why the
SOME-member obligation is strictly stronger.

**CONTROL 3, ON THE CANONICALIZER'S OWN HYPOTHESIS.** I offered the band's
hypothesis where `via-col-square` takes `Init`. Agda refused, 2 s, and it printed
the WHOLE of `Init` including row 4 against `Init α → Empty.⊥`.

**THE MACHINE PRINTS THE ROUTE-LEVEL FINDING.** The band's hypothesis is the
negation of the canonicalizer's hypothesis.

**CONTROL 4, ON THE DELIVERED CONSUMER.** I fed `L.StageCardinal` the
pointwise-truncated family. Agda refused, 2 s:

```
error: [UnequalTerms]
∥ sq δ ∥₁ !=<
(Σ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫)
 (λ f → (x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y))
when checking that the expression h has type SqBelow α
```

**The refusal is the module's own and not my shape's.**

## 6. WHAT REMAINS OF `[LJ-1.8]`'s BLOCKER

| band | supplier | status after this probe |
|---|---|---|
| ω | `squareω`, `src/L/InjChain.lagda.md:184-185` | **DELIVERED, untruncated** |
| `Init` ordinals | `via-col-square`, `src/L/Ordinal/SquareLaw.lagda.md:960-961` | **DELIVERED, untruncated** |
| successors above ω | `sq-suc`, `agents/tasks/LJ-1-330/ProbeLJ1330A.agda:120-127` | **BUILT, untruncated, not landed** |
| **non-initial LIMITS** | `limit-truncated`, `agents/tasks/LJ-1-332/ProbeLJ1332A.agda:196-204` | **BUILT, TRUNCATED, not landed. UNCHANGED by me** |

**The blocker is where `[LJ-1.332]` left it: one missing untruncation at one
band. This task did not move it, and it says why it did not.**

**WHAT THIS PROBE ADDS.**

1. **The consumers need the data. MEASURED**, at the delivered module (control 4)
   and at the shape (control 1). **The cheapest abort row is CLOSED and it will
   not need re-checking.**
2. **The reason is an intermediate Pi-of-data, not a non-propositional
   conclusion.** The conclusion IS propositional. **A future brief must not
   repeat the search for a propositional motive: it is already there.**
3. **The exact repair is named:** `ACBranch`, `ProbeLJ1333A.agda:109-111`.
   Choice over the site's members, at an injection type.
4. **The cheaper truncation does NOT open item 2**, and it makes item 2's
   obligation strictly stronger.
5. **The band is the exact complement of the tree's only canonicalizer.**

**WHAT I DID NOT SETTLE, and I name it rather than guess.**

- **The untruncation itself.** **NOT REFUTED. C-36 binds.** I refuted no map. I
  measured that one route is stronger than another and that one delivered device
  cannot reach this band.
- **`[LJ-1.321]` item 1, the pointwise-least pairing.** **UNTOUCHED by me.** The
  literature digest bears directly on it and section 9 quotes the line.
- **Whether `ACBranch` is derivable.** **INFERRED, not measured:** `Motive δ` is
  a Σ over a function type and not a proposition, so joining pointwise bars into
  one bar is the choice shape. **No Agda term can settle non-derivability**, and
  I claim none.
- **The sweep (C-42).** I measured ONE shape, the descent in `Upper`. **I did not
  sweep `src/` for other data-motive inductions that a truncated hypothesis would
  block, and I claim no count.**
- **The landing cost.** Every second here is warm.

## 7. DD4, STATED AND ANSWERED, WITH MY AXIS (C-46)

**DD4: maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker. DD4's own axis is AC against GCH, fixed in
code at `scripts/measure/ledger.py:50`.

**MY AXIS: does the term name a tower, a stage or a formula?**

**Answer: PART 2 and PART 3 are TOWER-BLIND. PART 1 is NOT, and it cannot be.**

- `InjAt`, `beta-fixed-residue`, `item2-door`, `inj→witness`,
  `some-is-not-weaker` and `band-kills-row4` name `S`, `IsOrd`, ambient
  membership, `ω`, `sucV` and `sq`. **They name no `Lset`, no `Formula`, no `𝒟ₒ`
  and no `⊨`.**
- **`Motive`, `Branch`, `StepShape` and `BranchFrom` name `Lset`, and that is
  correct**: they exist to measure the DELIVERED descent, which is about stages.
  **A tower-blind version of them would measure nothing.**
- **`[LJ-1.330]`'s and `[LJ-1.332]`'s property is KEPT where it applies.**
  `beta-fixed-residue` takes a POINT of a delivered injection type and never a
  total map out of `sq α`. **That is why `[LJ-1.329]`'s object could not exist,
  and my PART 2 does not ask for one.**
- **MEASURED: I import no new module into either closure.** `L.StageCardinal` in
  probe B is the delivered consumer, already in the GCH closure.
- **INFERRED, and I mark it INFERRED:** this probe proposes nothing for landing,
  so it moves no ledger row. **The standing figure I quote comes from
  `ledger.py --brief` under my own hand: 32,474 lines over 94 masters, measured
  from HEAD.** The tool reports the endpoint REFUSED and the DD5 benchmarks NOT
  MEASURED, so I quote neither.

## 8. THE ABORT CRITERION, ANSWERED ROW BY ROW (D-1)

| the brief's row | outcome |
|---|---|
| **THE MAP EXISTS AND YOU BUILD IT** | **NOT TAKEN.** I built no map. `sq` is not total and `[LJ-1.8]`'s blocker stands |
| **THE SOME-MEMBER TRUNCATION STILL NEEDS A CHOICE** | **TAKEN.** Section 1 measures it, and section 2 measures that the consumers demand data. **This is the route-level finding and it goes to the owner** |
| **THE CONSUMERS DO NOT NEED DATA** | **NOT TAKEN, MEASURED, and I checked it FIRST as ordered.** Controls 1 and 4. **The final motive IS propositional and it does not help** |
| **A WALL** | **NOT TAKEN.** No run passed 2 seconds. C-56 was obeyed and the untruncated control was written first |

## 9. THE RULES THIS CHAIN EARNED, ANSWERED

- **C-44. The brief warned about its own premise, and the warning paid AGAIN.**
  **The premise 「the SOME-member truncation does not need a well-order at all」
  is HALF FALSE**, and the false half is the one that funds the task. **That is
  the sixth check in a row to find something.**
- **C-56. Obeyed, and it produced a second measurement.** The untruncated control
  came first in both files. **The nested `PT.rec`/`PT.map` that cost 400 s at
  `[LJ-1.332]` costs 2 s here.** The difference is what the eliminators must
  normalize. **The nesting is not the price; the payload is.** I offer this as
  evidence for C-56 and not as a new law.
- **C-54. A truncation stall at a SET motive is a `2-Constant` obligation before
  it is a principle.** Section 3.1 states the obligation with the delivered
  eliminator. **The stall at PART 1 is NOT of that kind: it is a Pi-of-data, and
  `rec→Set` does not reach it.** That is a distinction the law does not yet make.
- **C-36. A failed substitution is not a proof of impossibility.** **I refuted
  NOTHING.** I measured one implication's direction and one device's hypothesis.
  **The untruncation is not refuted and I say so three times.**
- **C-42. A refutation measures the site it names.** I measured ONE descent. **I
  ran no sweep and I claim no count.**
- **D-10. Price the TRUTH of a recorded residue before pricing its proof.** I
  priced the premise first, in section 1, before writing any map.
- **C-45. `exit 0` is not a supply.** Both probes are green and land nothing.
- **P-l.** I priced nothing by analogy. Section 4 marks every second warm.
- **D-1.** The abort criterion was fixed before the run, and section 8 answers it
  row by row. **The cheapest decisive check ran first.**

## 10. PROHIBITIONS, ANSWERED

- **Writes: `agents/tasks/LJ-1-333/` only**, three files: this report,
  `ProbeLJ1333A.agda` and `ProbeLJ1333B.agda`. Nothing in `src/`, nothing in
  `dev/`, no other task directory, no `.claude/`, no `AGENTS.md`.
- **I read the sibling probes and changed no line of them.** I IMPORTED
  `LJ-1-319.SqIsSet` and `LJ-1-332.ProbeLJ1332A` rather than copying them, so
  both re-compiled under my own hand. **`git status --porcelain` lists my three
  new files and no modified tracked file.**
- **I did NOT land any sibling's term.**
- **I did NOT re-derive `[LJ-1.329]`'s refutation.** I cited it.
- **No commit, no push, no `make check`.** No `git checkout`, `stash`, `reset` or
  `clean`.
- **Agda: eleven invocations, ONE process at a time.** Slots counted before every
  one with the brief's command. `GHCRTS="-A64m -I0 -M8g"` on every run. Cap never
  raised. **Every run counted 0 slots before it.**

## 11. ARCHIVE USED (DD18), ONE LINE READ PER FILE

- **`agents/tasks/LJ-1-332/lj-1.332-report.md`, READ WHOLE, as the brief
  ordered.** Line read `:189-190`: 「The truncation it meets is `Init`'s fourth
  row, which is nearer and cheaper: it asks for ONE member, not for the LEAST
  one」. **TOOK: the exact object of my section 1, and the word 「cheaper」 is
  what I tested.** Also `:274-275`, the 400-second bisection, which is the
  comparable for my section 4.
- **`agents/tasks/LJ-1-321/lj-1.321-report.md`, READ section 8 whole.** Line
  read, item 2: 「A weakly constant endomap of `sq α` by any other route. Kraus
  et al. Theorem 16 says this is exactly equivalent to what is wanted. A
  well-order is one supplier (section 7). No argument here says it is the only
  one」. **TOOK: the exact statement of my target.** **Item 1 I leave STANDING
  and untouched**, and section 6 says so.
- **`agents/tasks/LJ-1-329/lj-1.329-report.md`, READ the verdict and section 1.**
  Line read `:49-53`: 「That is a function out of the whole ambient type. `sq α`
  is `Σ[ f ∈ (⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫) ] (injectivity)` ... Its elements are
  AMBIENT injective pairing functions, all of them, not the definable ones」.
  **TOOK: the reason the residue in my `beta-fixed-residue` is the refuted
  object, so that I cite the refutation instead of re-deriving it.**
- **`archive/dev/TASKS-archived.md`, SHAPE ONLY, never a claim.** Line read
  `:82` (L3.32-T47): 「Truncated square law at initial ordinals | DELIVERED」.
  **TOOK, SHAPE ONLY: the retired route ALSO delivered this law truncated
  first, and at the initial ordinals.** **WHAT WOULD NOT TRANSFER:** every figure
  in that row prices modules of a retired tower, and its report lives in
  `_build/`, a temporary folder, so no figure of it is readable today and I quote
  none. **That row says nothing about a non-initial limit, which is my band.**

## 12. LITERATURE USED (DD18)

- **`dev/literature/truncation-and-selection.md`. IT BEARS, and it already
  contains the sharpest statement of my finding.** READ `:288-305` and
  `:311-316`.

  **Line read `:311-316`:** 「Whether a well-order on the two carriers yields a
  canonical injection between them. It does not, in general: the greedy
  construction that sends each element to the least unused target fails at order
  type `ω · 2` into `ω`. **A canonical injection needs a well-order on the
  INJECTIONS, which is what `<_L` supplies classically and what an ambient
  function type does not have.**」

  **THAT IS MY BAND, NAMED BY ITS ORDER TYPE.** `ω · 2` is a non-initial limit.
  **So the digest already recorded that the least-element device fails at exactly
  the band this leg cannot close**, and it names the missing supplier: a
  well-order on the injections.

  **Line read `:297-300`, the digest's own checklist item 4:** 「Does `A`
  decompose as an index over a well-order plus a PROPOSITION-valued payload? Then
  `leastOf` applies」. **MEASURED against my witness: the SOME-member witness
  DOES decompose as an index over a well-order, because the member ranges over
  `⟪ α ⟫`. Its payload is an INJECTION type and NOT proposition-valued.** **So
  checklist item 4 does not fire, and item 5, the weakly constant endomap, is
  where the question sits.** That is `[LJ-1.321]` item 2, and section 3 states
  it.

  **Theorem 16 and `rec→Set`:** read `:158-161` and `:175`, and `item2-door`
  compiles the criterion at `ProbeLJ1333A.agda:171-173`.

  **WHY NOT re-fetched:** the digest carries the theorem numbers and the library
  path, and I take statement-level facts only.

- **`dev/literature/devlin-II5.md`. NOT RE-READ, and WHY NOT:** `[LJ-1.332]`
  section 12 measured its bearing whole and my question is not his. **THE BRIEF'S
  ONE-LINE QUESTION, ANSWERED: the untruncation is UNUSUAL and NOT optional.**
  Devlin never owes it, because a cardinality equation asserts that a bijection
  EXISTS and that is already truncated. **But this tree's consumer is not his
  prose: `L.StageCardinal` runs a data-motive `∈-induction` that Devlin does not
  run, and control 4 measured that it refuses the truncated family.** **So the
  debt is created by the FORMALIZATION's descent and not by the theorem**, and a
  formalization that reduced by cardinal arithmetic, as he does, would not owe
  it.

- **Kraus, Escardo, Coquand and Altenkirch, LMCS 13(1) 2017. NOT FETCHED, and WHY
  NOT:** the digest carries Theorem 16 and the library carries `rec→Set`. **My
  question is whether one map exists in this tree. The type checker settles that
  and no source can.**

- **Jech 13, Schindler and Zeman. NOT READ, and WHY NOT:** they price the
  classical construction, which goes through the initial ordinal. **Section 3.2
  measures that the tree already does exactly that, and the band is what is left
  over.**

## 13. CHECKS RUN

- `GHCRTS="-A64m -I0 -M8g" agda agents/tasks/LJ-1-333/ProbeLJ1333A.agda`: exit 0,
  2 s.
- `GHCRTS="-A64m -I0 -M8g" agda agents/tasks/LJ-1-333/ProbeLJ1333B.agda`: exit 0,
  2 s.
- `.venv/bin/python scripts/gate/lint-agda.py --check` on both probe files: exit
  0.
- `.venv/bin/python scripts/gate/lint-prose.py --check` on this file: recorded in
  section 14.
- `.venv/bin/python scripts/gate/check-probes.py`: **clean, 3,145 tracked files,
  no probe outside `agents/tasks/` and no generated file.**
- `.venv/bin/python scripts/dispatch/rules.py --for probe`: run, every statement
  read. **I opened the full `dev/LESSONS.md` entry for D-1, C-42 and P-l.**
- `.venv/bin/python scripts/measure/ledger.py --brief`: run under my own hand, and
  section 7 quotes it and nothing else.
- MEASURED: no em dash in any of the three files I wrote, by `grep -c`, 0 in all
  three.
- MEASURED: `grep -c "postulate\|TERMINATING\|{!\|trustMe"` on both probe files:
  0. Both are `--safe` with no hole and no postulate.
- **Every `ProbeLJ1333A.agda:<line>` and `ProbeLJ1333B.agda:<line>` citation in
  this report was re-verified against the files after my last edit**, by printing
  the cited start line and reading the identifier there.

## 14. LINT AND TREE STATE

- `.venv/bin/python scripts/gate/lint-agda.py --check agents/tasks/LJ-1-333/ProbeLJ1333A.agda agents/tasks/LJ-1-333/ProbeLJ1333B.agda`:
  exit 0.
- `.venv/bin/python scripts/gate/lint-prose.py --check agents/tasks/LJ-1-333/lj-1.333-report.md`:
  exit 0.
- `.venv/bin/python scripts/gate/check-probes.py`: clean.
- `git status --porcelain`: **my three new files only.** No tracked file is
  modified. I ran no `git` command that writes.
