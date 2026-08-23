# LJ-1.574 report: the assignment and its formula, in one task

## HEAD
head_slot: coder
machine: shared
verdict: STOP

The report was written as a skeleton before any Agda and filled as each answer
landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-574/`. Nothing is postulated, the probe carries `--safe`,
and there is no hole. The probe is a raw `.agda` file, so it carries no
` ```agda ` fence, counts 0 in-fence lines, and the ratio bar cannot fire on
it. Nothing lands in `src/`.

## VERDICT

**STOP, AND THE STOP IS A PRICE AND NOT A WALL.**
`agents/tasks/LJ-1-574/review-of-succ-assignment-definable.md`.

**THE OBLIGATION IS A THREE-STEP PRICE AND THIS BRIEF FUNDS TWO OF THEM.**
`[LJ-1.552]`'s review, which premise 1 cites at line 161, prices this same
obligation further down at THREE steps, and rules step 2, "the square law
INSIDE L", "a chapter and not a task"
(`agents/tasks/LJ-1-552/review-of-succ-assignment.md:185-192`).

**AND THE BRIEF'S OWN CITATION IS FOUR LINES EARLY, WHICH IS WHY THE SENTENCE
WAS MISSED.** Premise 1 gives `:161`, and that line is "BRIEF NEEDS.**
`[LJ-1.549]` recorded its residue as two independent missing". The sentence the
brief quotes is at `:165-169`. The premise is TRUE; the line is four early, and
the price sits 16 lines past where the brief stopped reading.

**AND ROW 2 WOULD NOT PAY STEP 2 EITHER.** The brief forbids rows 1 to 4, but
that is not the point: row 2 of the bill is `SqAt`
(`agents/tasks/LJ-1-550/Probe550.agda:309-310`), which is the AMBIENT square
law (`Probe550.agda:82-86`), so **even paying row 2 in full would not supply
step 2.**

**W3 IS GO, AND THE BRIEF'S ANTICIPATED NO-GO IS THEREFORE CLOSED
POSITIVELY.** The brief said a NO-GO on the reflection step "NAMES THE LAST
OPEN QUESTION ON THIS ROW". The reflection step DOES bound the search, and the
probe spends it.

**WHAT IS DELIVERED IS NOT HALF A TASK.** `[LJ-1.549]`'s `Residue δ b` is the
assignment AND its formula in ONE type. `residue-at-stage` inhabits it at
`b := LsetS β oβ`. The obligation is the same type at `b := κ`, and two
typechecked rows say the identification is the elaborator's
(`residue-closes`, `obligation-gives-residue`). **The whole difference is the
bound, and the bound is steps 2 and 3.**

## A DISCIPLINE SLIP, REPORTED BEFORE ANY NUMBER

**TWO AGDA PROCESSES OF MINE OVERLAPPED FOR ABOUT 2 MINUTES 47 SECONDS.** The
harness moved a long typecheck to the background without my noticing, and I
started a second one on the same file. I killed the second as soon as I saw it
(`ps` showed PIDs 74940 and 76937 both live). **No number measured during that
overlap is admissible and none is reported.** Every wall time and every memory
figure below comes from a run with exactly one Agda process on this pane. The
clause is my slot file's "Start one Agda process and no more".

## TWO RUNS I KILLED, AND WHY THAT IS NOT A HEAP EVENT

**NEITHER RUN ABORTED. GHC DID NOT REPORT A HEAP OVERFLOW. I KILLED BOTH, ON
THE RSS, AND I SAY SO RATHER THAN CALL THEM WALLS.**

| what | at | RSS | action |
|---|---|---|---|
| the whole probe, first form | 19 min 52 s | 9,383,152 KB | killed by me |
| `runs/T8.agda.txt`, the bisection slice that adds `residue-closes` | 1 min 55 s | 9,004,256 KB | killed by me |

The caliber on this pane is `-M8g`. RSS is not the GHC heap, so 9.0 GB of RSS
is not by itself a heap overflow; it is a run I judged doomed and stopped.
**A rerun would have been the forbidden move.** I bisected instead, and the
bisection is the next section.

## W3, THE WIDEST UNMEASURED TERM

**GO, AND IT IS THE FILE'S HINGE.** `agents/tasks/LJ-1-574/runs/W3.agda`, 190
lines, written FIRST and typechecked ALONE before any other Agda of this task.
Three cold runs, exit 0: `runs/w3-1.out` to `runs/w3-3.out`.

The brief names the term as "`[LJ-1.560]`'s obligation, re-ascribed at
`leastOf`'s predicate, TYPE ONLY", and warns "If it does not apply, the formula
has no bound and the estimate above is void: say so in the first hour."

**IT APPLIES, AND THE REASON IS ONE ROW AND NOT AN ARGUMENT.** `leastOf`'s
predicate at `[LJ-1.557]` is `Good` (`agents/tasks/LJ-1-557/Probe557.agda:204-205`),
which is `Code` (`Probe557.agda:82-83`), which is `L.GCH.InjL`
(`src/L/GCH.lagda.md:38`). `[LJ-1.560]`'s reflection step takes a FORMULA. So
"does it apply" is ONE question: **is that quantifier the `⊨` of a formula?**

**IT IS.** `InjCode F a c` (`src/L/Cardinal.lagda.md:223-228`) has four
conjuncts. Three are already `⊨` of a named formula, and the three formulas are
arity-POLYMORPHIC (`svAt`, `src/L/Coding/Model.lagda.md:210`; `domAt`, `:278`;
`injAt`, `src/L/Coding/Injection.lagda.md:44`), so they move to a wider
environment with the same `Fin` index and no cost. **The fourth conjunct is the
only one the tree does not carry as syntax at this site**: `ranAt`
(`src/L/Coding/Injection.lagda.md:230`) is that sentence, but it sits under the
`private` at `src/L/Coding/Injection.lagda.md:156` and it states the range
EXACTLY where `InjCode` asks only for containment. `valFoAt` is the one
implication, built from the exported `appAt`, and it is 3 lines.

W3 then re-ascribes BOTH reflection steps the tree carries at that formula, and
neither term is written by me:

| row | library term | what it costs |
|---|---|---|
| `w3-single` | `Single.reflect` (`src/L/Reflect.lagda.md:495`) | `Below (Single.βω ψ) ρ`, and `βω` is fixed by ψ alone |
| `w3-full` | `mkReflect` (`src/L/ReflectFo.lagda.md:525`) | the matrix is RELATIVIZED |

**NEITHER IS WHAT THE SITE WANTS, AND SECTION 2 OF THE PROBE SAYS WHY IN SIX
LINES OF AGDA.** The site wants the caller's δ INSIDE the stage (so `Single` is
out) AND the matrix untouched (so `mkReflect` is out), because the witness has
to come back out as an `InjCode` and not as a relativized one. `Ladder`
(`src/L/Reflect.lagda.md:256`) is generic and `Single`'s step is public, so the
same ladder started at a caller's σ₀ is six lines and proves nothing new: the
closure argument is `Ladder.closure`, unchanged.

| run | wall s | peak memory footprint (bytes) |
|---|---|---|
| `runs/w3-1.out` | 1.77 | 339772232 |
| `runs/w3-2.out` | 1.78 | 339755848 |
| `runs/w3-3.out` | 1.76 | 339755848 |

Median wall **1.77 s**, against the brief's ceiling of 3 minutes. No heap
event. Three COLD runs, `W3.agdai` deleted before each, exit 0.

**ESTIMATE AGAINST MEASURED.** The brief said about 20 lines. Measured 190
lines, of which 78 comment, 25 blank and 87 Agda; 30 of the 87 are the pragma,
the module header and the imports, so the Agda that answers W3 is **57 lines**.
The overrun is the bridge: the brief expected a type ascription, and I inhabited
BOTH directions of `InjCode ↔ ⊨`, because a type ascription would have left the
answer a reading.

## THE FORMULA, WRITTEN OUT

The brief requires this section. **The formula is `Link.Fo`, section 4 of
`Probe574.agda`. Its arity is 3, which is `[LJ-1.554]`'s `LinkAt` arity
(`agents/tasks/LJ-1-554/Probe554.agda:81-82`), and its environment is
`(y ∷ x ∷ z ∷ [])` with `z` read by no conjunct.** It carries THREE constants
and no coded syntax:

```
Fo =    (var 0 ∈̇ con c)
   ∧̇ (  codeFoAt 0 1 κ
      ∧̇ ¬̇ ∃̇ (  (var 0 ∈̇ con c)
             ∧̇ (  codeFoAt 0 2 κ
                ∧̇ appC r 0 1 ) ) )
```

In words: **`y` is a member of the stage; `y` codes an injection of `x` into
κ; and no member of the stage that codes an injection of `x` into κ stands
before `y` in the stage's own order.**

- `c` is `LsetS β oβ`, the stage as an L-set (`src/L/Axioms/Basic.lagda.md:160`).
- `κ` is the site's own cardinal, a constant because the site fixes it.
- `r` is `relL β βisL oβ`, the stage's well-order **as an element of the
  model**, which is what lets it be named by a constant at all
  (`src/L/Choice/Order.lagda.md:693-702`).
- `appC` (`src/L/InjChain.lagda.md:196`) reads a pair out of a CONSTANT graph,
  which is the atom the third conjunct needs.

**THE SHAPE IS NOT NEW AND I DID NOT INVENT IT.** It is
`L.Choice.Transversal.Pick` (`src/L/Choice/Transversal.lagda.md:116-123`): a
member of the stage, a condition on it, and nothing before it in the order.
Only the condition is new, and section 1 is what makes the condition sayable.
The literature calls this device "a definable well-order plus a universal
guard" (`dev/literature/truncation-and-selection.md:68`), and that is exactly
the three conjuncts.

**DID `[LJ-1.560]`'s REFLECTION STEP SUPPLY ITS BOUND? YES, AND ONLY FOR THE
SECOND CONJUNCT'S SEARCH.** The description above quantifies over the stage
twice and over nothing else. Before section 2 the predicate quantified over the
whole L-carrier, and `[LJ-1.557]` recorded exactly that as the reason the
pointwise code does not reach the uniform one. **The bound is what turns that
quantifier into `var 0 ∈̇ con c`.** The `∃̇` in the third conjunct is unbounded
as syntax, but it is guarded by `(var 0 ∈̇ con c)` in its first conjunct, so it
ranges over the stage too; that is `Pick`'s own arrangement
(`src/L/Choice/Transversal.lagda.md:118`).

**THE TWO READINGS ARE `Link.lin` AND `Link.lout`, AND NEITHER IS A COROLLARY
OF THE OTHER.** `lin` builds a satisfaction out of a least element; `lout`
extracts a least element out of a satisfaction and then spends
`isPropLeastOf` (`src/L/WellOrder/Base.lagda.md:136`), because leastness in a
well-order is unique by trichotomy alone. `isPropLeastOf` had exactly one
consumer in the tree before today (`L.Choice.Transversal`); this is its second.

## WHAT THIS DOES TO THE BILL

**I PAID NO ROW OF `[LJ-1.564]`'s BILL, AND I READ NO DISCHARGE INTO ANYTHING I
DID NOT INHABIT.**

| row | what it is | what this task did |
|---|---|---|
| 1 `AmbientCardAtSucc` | forbidden by the brief | not attempted |
| 2 `SqAt` | forbidden by the brief | not attempted. **And measured NOT to be step 2 even if paid**: `SqAt` is `SqLaw` (`agents/tasks/LJ-1-550/Probe550.agda:82-86`), an AMBIENT function |
| 3 `CoHyps` | forbidden by the brief | not attempted |
| 4 `StageCountedCoded` | forbidden by the brief | not attempted |
| 5 `SuccIntoPower`, B10 | the obligation | **NOT PAID.** `Obligation` is stated in section 6 and nothing inhabits it |

**WHAT MOVED IS NOT A ROW, IT IS THE ROW'S PRICE.** Before this task the row's
price was `[LJ-1.552]`'s three steps with step 1 delivered pointwise only.
After it:

| step | before | after |
|---|---|---|
| 1, internal injection code per member | `[LJ-1.557]`, POINTWISE, and it recorded that the pointwise form does not reach the uniform one | **UNIFORM.** `codes-at-one-stage`: ONE stage holds a code for EVERY member of δ |
| the selection | the predicate was "a quantifier over the whole L-carrier and not over a stage" | **A SET.** `leastOf` runs over `Mem (Lset β)` |
| 3, the formula | not built | **BUILT.** `Link.Fo` with both readings, at the stage |
| 2, the square law inside L | not built, "a chapter and not a task" | **NOT BUILT.** This is the whole remaining gap |

## WHAT THE SHAPE RESISTED

**ELEVEN RED TYPECHECKS ACROSS THE SLICES, AND NINE WERE SCOPE OR ARITY AND
NOT MATHEMATICS.** The five that are worth another task's time:

1. `∃[∶]-syntax` is not in scope from `Base.Prelude` even where the truncation
   is. Cure: name it from `Cubical.Functions.Logic`.
2. `⟪_⟫` must be imported BEFORE the module header when the header's own
   parameters mention it, which `sq`'s type does.
3. `tt*` comes from `Cubical.Data.Unit` and `Base.Prelude` does not re-export
   it. `Below σ []` is `Unit*`, so the empty tail of an environment needs it.
4. Cubical's `_⊆_` is stated at the library's SMALL membership `_∈ₛ_`, so
   `extensionality` cannot be applied to a `_∈_` hypothesis directly. Cure:
   `V.Hierarchy.extensionalV` (`src/V/Hierarchy.lagda.md:114`), which is the
   same theorem with the glue already paid.
5. `appC-adequate` is a path of `Ω` and not of `Type`, so it needs
   `subst ⟨_⟩` and not `transport`. `valFoAt-adequate` is the opposite, because
   I stated it at `Type`.

**WHAT COST NOTHING, AGAINST EXPECTATION.** Injectivity of the assignment.
I expected to spend the leastness on it. **A code determines its DOMAIN**, by
`domAt` read in both directions (`src/L/Coding/Model.lagda.md:289`, `:294`),
and the domain of the code at `k` is the k-th member of δ; so two members of δ
carrying the same code have the same members and are equal by extensionality.
The leastness is spent only on single-valuedness, which is what the literature
predicted: the guard "turns 'some witness' into 'THE witness'"
(`dev/literature/truncation-and-selection.md:68-70`).

**WHAT I HAD TO WEAKEN.** One thing, and it is named in the probe rather than
hidden. `Select.Good` is `∥ InjCode … ∥₁` and not `InjCode …`, because
`leastOf` takes an `hProp`-valued predicate and `InjCode` is a Σ. Nothing is
lost: the obligation's conclusion is truncated already. This is the constraint
`dev/literature/truncation-and-selection.md:146` states in advance.

**WHAT I COULD NOT CLOSE.** The bound. Every value the route produces is a
CODE, that is a set of ordered pairs; every member of `powL κ` is a SUBSET of
κ (`agents/tasks/LJ-1-549/Probe549.agda:124-125`). Carrying one to the other is
the classical coding of a well-ordering of a subset of κ by a pairing on κ, and
the pairing has to be an L-SET for the description to name it.

## THE PERFORMANCE FINDING, AND IT IS THE ONE MEASUREMENT NOBODY ASKED FOR

**THE BISECTION, FIVE SLICES, ONE AGDA PROCESS AT A TIME.** Each slice is the
probe truncated at a named point, kept in `runs/`.

| slice | what it ends after | wall s | peak RSS |
|---|---|---|---|
| `runs/D1.agda` | the five predecessor imports and three re-ascriptions | 3.20 | 781 MB |
| `runs/T5.agda` | section 5's `residue-at-stage` | 18.53 | 1.12 GB |
| `runs/T6.agda` | section 5's `stage-assignment-definable` | 18.80 | 1.07 GB |
| `runs/T7.agda` | section 6's `Obligation`, the TYPE | 18.79 | 1.11 GB |
| `runs/T8.agda.txt` | section 6's `residue-closes` | KILLED at 1 min 55 s | 9.0 GB |

**SO THE COST IS ONE TERM, AND INSIDE IT ONE `subst`.** Both
`stage-assignment-definable` and `residue-closes` moved a `LinkAt` from one
assignment to a pointwise-equal one, and both did it the obvious way,
`subst (P554.LinkAt δ)` along a `funExt` path. **The identical line is FREE at
`b := LsetS β oβ` and CATASTROPHIC at `b := powL κ`.**

The reason is in the tree already: `powL κ` is `℩ (hasPowerL κ)`
(`agents/tasks/LJ-1-549/Probe549.agda:121-122`), and the transport pushes the
`funExt` path through `⟪ fst (powL κ) ⟫↪`, which forces that `℩`.
`src/L/Cardinal.lagda.md:88` records the same shape at `leastOf` and seals it
for the same reason.

**THE CURE IS 4 LINES AND IT IS NOT A SEAL.** `linkAt-refst` (`Probe574.agda`,
just after `upS`) rebuilds the `LinkAt` at the new assignment by composing two
paths at the `fst` level, because `LinkAt δ s` reads `s` only through
`fst (s k)` (`agents/tasks/LJ-1-554/Probe554.agda:83-88`). The formula and the
two readings are untouched. **With it the same file checks in 19.2 s at
1.00 GiB.**

**I PROPOSE THIS AS A LAW AND I DO NOT WRITE IT.** The candidate: *when a
statement reads an assignment only through one projection, move it along a
path of that projection and never transport the statement*. It is measured at
ONE site, and `AGENTS.md:45` says a measured cure does not transfer by analogy,
so the second site has to re-measure. The owner rules.

## THE COST

| run | wall s | peak memory footprint (bytes) |
|---|---|---|
| `runs/final-1.out` | 19.99 | 1070056792 |
| `runs/final-2.out` | 19.30 | 1070040384 |
| `runs/final-3.out` | 18.56 | 1070056792 |

Median wall **19.30 s**, peak memory footprint about **1.00 GiB** against the
8 GB cap. Three COLD runs, `Probe574.agdai` deleted before each, exit 0. No
heap event. The file they measured is the file this report describes,
md5 `59dc7122213c96df9800b362abbb8588`.

**THE WITNESS METER AGREES WITH THE VERDICT, IN BOTH DIRECTIONS.**

- The brief's declared obligation:
  `missing exit=42 agents/tasks/LJ-1-574/Probe574.agda::succ-assignment-definable`,
  `1 UNRESOLVED of 1`, `probe_red=False` (`runs/witness-1.out`). **The probe is
  green and the obligation is absent**, which is what a stop looks like and
  what a red probe does not.
- The nine terms this task DOES deliver: `0 UNRESOLVED of 9`
  (`runs/witness-2.out`), covering `codes-at-one-stage`, `residue-at-stage`,
  `stage-assignment-definable`, `residue-closes`, `obligation-gives-residue`,
  `injL-is-search`, `search-is-injL`, `w3-single` and `w3-full`.

**ESTIMATE AGAINST MEASURED.** The brief said about 240 lines in the probe, of
which the obligation is about 60, and called it "the least certain estimate in
the queue". The probe is 806 lines: 183 comment, 114 blank and 509 Agda, of
which 68 are the pragma, the module header and the imports. **The obligation is
0 of them.** The overrun is not the obligation; it is sections 1 to 4, which
the brief did not price because it expected W3 to decide the task before they
were written.

## WHAT THE NEXT BRIEF NEEDS FROM THIS ONE

1. **STEP 2 HAS A MEASURED PRICE ALREADY, AND THE REASON IT WAS DECLINED IS NOW
   FALSE.** `archive/dev/LJ-dispatch-index.md:382` records `[LJ-1.327]`:
   "Describe the square law's pairing as a FORMULA | EXPENSIVE, ABOUT 820, AND
   DO NOT FUND IT | pairomega is a well-founded RECURSION, and a coded square
   law is consumed by NOTHING today". **A coded square law is consumed by this
   obligation.** The "about 820" is that task's own estimate and I did not
   re-measure it; it is a comparable of SHAPE and nothing may be funded against
   it without a fresh probe.
2. **`residue-at-stage` IS A DELIVERED TERM WITH A FREE BOUND.** `[LJ-1.549]`
   section 2 measured that the freedom in `b` is worth nothing FOR B10. It did
   not measure what a definable injective assignment of δ into a STAGE is worth
   elsewhere, and B9 (`StageCountedCoded`) is stated at a stage.
3. **THE CALLER-STARTED LADDER IS SIX LINES AND IT IS REUSABLE.** `Start`
   (section 2 of the probe) is `Ladder` at `Single`'s step from a caller's σ₀.
   Any site that needs "the witness lies in a stage that also holds my
   parameters, matrix untouched" can take it. Neither `Single` nor `mkReflect`
   gives that today.
4. **`InjL` IS A FORMULA'S `⊨`, AND THAT IS GENERAL.** `injL-is-search` and
   `search-is-injL` are stated at an arbitrary pair, not at this site's. Any
   task that wants to reflect, separate or bound an `InjL` can now do it.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: **READ, AND IT CHANGED THIS REPORT.**
  Line 382: `| LJ-1.327 | Describe the square law's pairing as a FORMULA | EXPENSIVE, ABOUT 820, AND DO NOT FUND IT | pairomega is a well-founded RECURSION, and a coded square law is consumed by NOTHING today |`
  It gives the missing step a prior price and a prior ruling whose stated
  reason this task overturns.
- `archive/dev/JOURNAL-archived.md`: **READ.** Line 1632:
  `the square law (the honest syntax injection of a pair of members into unary formulas IS the square`
  It records that the counting route cannot avoid the product, which is the
  same obstruction from the other side.
- `archive/dev/JOURNAL.md`: not read. Its two hits on my terms are in a
  successor file to the one above and I used the archived journal instead.
- `archive/dev/DECISIONS-archived.md`: not read. It is the `D<n>` series, 61
  lines, and it carries no hit on any term of this task.
- `archive/dev/ORCHESTRATION.md`: declined. It is the archived loop document
  and this task is mathematics, not process.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`: **READ, AND IT PREDICTED TWO
  MEASUREMENTS.** Line 68:
  `**The selection device is a definable well-order plus a universal guard.** The`
  and line 146:
  `**The constraint the route carries: `P` must be `hProp`-valued.** So `leastOf``
  The first is the shape of `Link.Fo`; the second is why `Select.Good` is
  truncated.
- `dev/literature/devlin-II5.md`: **READ.** Line 160:
  `> Proof. By 5.5, 𝒫(κ) ⊆ L_{κ⁺} for all infinite cardinals κ. So by 1.1(vii),`
  It is the OTHER direction of GCH, `InjL (𝒫 κ) δ`, and it confirms that
  Devlin's II.5 gives this task's direction no separate argument: `κ⁺ ≤ 2^κ` is
  the ZFC half, and it is the half that needs the pairing.
- `dev/literature/digest.md`: not read.
- `dev/literature/terms-2026-08.md`: not read. It is a terminology file and
  this task added no term.
- `dev/literature/geology.md`: declined; it is not about this route.

## WHAT WAS NOT DONE

No postulate, no hole, no module parameter that asserts the assignment. The
`sq` parameter of the probe is `[LJ-1.568]`'s own header parameter
(`agents/tasks/LJ-1-568/Probe568.agda:46-49`), and the probe carries it only
because `P561` and `P568` are parameterized by it. **It occurs at exactly three
places in the file, `Probe574.agda:54`, `:118` and `:119`: its own binding and
the two imports. No term of this file applies it to an argument.** `src/` is untouched. The
obligation `succ-assignment-definable` exists in no file of this task, by
design and not by omission. I did not attempt rows 1, 2, 3 or 4. I did not
commit and did not push.
