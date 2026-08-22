# LJ-1.549 report: SuccIntoSubsets, and the freedom in `b` that is worth nothing

## HEAD
head_slot: coder
machine: shared
verdict: NO-GO

The report was written as a skeleton before any Agda and filled as each answer
landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-549/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. No heap event. Nothing is postulated and there is no hole. The probe
is a raw `.agda` file, so it carries no ` ```agda ` fence, counts 0 in-fence
lines, and the ratio bar cannot fire on it. Nothing lands in `src/`.

## VERDICT

**NO-GO on `succ-into-subsets`. The obstruction is
`agents/tasks/LJ-1-549/review-of-succ-into-subsets.md`.**

**THE PROBE IS GREEN, EXIT 0, THREE COLD RUNS** (`runs/final-1.out` to
`runs/final-3.out`). It carries no hole and no postulate, which is deliberate:
a hole makes every reduction in the file a claim, and green makes each one a
measurement. That is `[LJ-1.533]`'s discipline.

THREE findings, and the first one corrects the brief's premise.

1. **THE FREEDOM IN `b` IS WORTH NOTHING.** `SuccIntoSubsets` and B10 are
   EQUIVALENT, both directions, unconditionally and with no model record. So
   this task is B10 itself.
2. **THE METHOD REACHES THE TABLE; TWO OF ITS INPUTS DO NOT EXIST.** The
   assignment, which is the ambient statement `κ⁺ ≤ 2^κ`, and its formula.
   `module Table` builds everything else.
3. **EVERY DELIVERED CODE PRODUCER IS REFUTED AT THIS PAIR, BY A TERM**, and
   there are three of them, not one.

## THE SET b

**THE SET IS `powL κ`, THE POWER SET OF κ INSIDE L, AND IT COSTS NOTHING.**

    powL : S → S
    powL κ = ℩ (hasPowerL κ)

`Probe549.agda:121-122`.

**WHY EVERY MEMBER OF IT IS A SUBSET OF κ.** Because that is what it was
separated by. `hasPowerL` (`src/L/Axioms/Power.lagda.md:187`) separates the
bounding stage by `subFo κ` (`:98`, `:190`), so `℩-spec` reads its membership
as `y ⊆ˢ κ` ON THE NOSE, and `powL-sub` (`Probe549.agda:124-125`) is one
`subst`. The obligation's second conjunct is discharged outright, with no
hypothesis at all.

**WHAT IT COST: NOTHING, AND THAT IS THE FINDING.** `hasPowerL` is
UNCONDITIONAL. It needs no `zf : isZFModel`, so `powL κ` is a term at the
statement's own frame. `powL-is-𝒫` (`Probe549.agda:133-136`) then proves
`powL κ ≡ 𝒫 κ` at ANY model record, because both are `℩` of a proof of the
same `isContr` and `isContr` is a proposition.

**THE OTHER TWO CANDIDATES THE BRIEF NAMED.**

- **A STAGE** fails the second conjunct: a member of `Lset β` is an arbitrary
  L-set, not a subset of κ.
- **A BOUNDED COLLECTION** is `powL κ` restricted, and `[LJ-1.546]`'s
  `code-target-mono` says a restriction can only cost more, never less.
- **AND THE CHEAPEST ONE THE BRIEF DID NOT NAME, `sucʟ κ`, IS A REAL
  CANDIDATE AND IS REFUTED.** `succ-kappa-subsets` (`Probe549.agda:503-510`)
  proves every member of κ⁺¹ is a subset of κ, so it passes the second
  conjunct. `succ-kappa-excluded` (`:541-548`) refutes it as a target: it is a
  member of δ (`succ-kappa-in`, `:514-536`) and `IsCardinalL δ` forbids a code
  into a member of δ (`target-not-below`, `:477-479`).

## THE FORMULA

**IT IS `TableFo`** (`Probe549.agda:234-235`), and it is FOUR CONJUNCTS at
ARITY 1, of which THREE ARE WRITTEN HERE AND ONE HAS NO PRODUCER.

    TableBody : (δ κ : S) → Formula S 3 → Formula S 3
    TableBody δ κ Link =
      prAtL (s2 zero) (suc zero) zero
      ∧̇ ( (var (suc zero) ∈̇ con δ)
        ∧̇ ( (var zero ∈̇ con (powL κ)) ∧̇ Link ) )

    TableFo : (δ κ : S) → Formula S 3 → Formula S 1
    TableFo δ κ Link = ∃̇ (∃̇ (TableBody δ κ Link))

`Probe549.agda:228-235`. The free variable of `TableFo` is the separation
variable `z`. Under the two binders, `var 2` is `z`, `var 1` is the argument
`x`, `var 0` is the value `y`.

| conjunct | says | written from |
|---|---|---|
| 1 | `z` is the ordered pair of `x` and `y` | `prAtL` (`src/L/Coding/Model.lagda.md:122`) |
| 2 | `x` is a member of δ | `var ∈̇ con` |
| 3 | `y` is a subset of κ | `var ∈̇ con (powL κ)`, read by `℩-spec` |
| 4 | `y` is THE value at `x` | **NOTHING. It is a parameter.** |

**I WROTE IT FRESH. `approx-carve` DID NOT SUPPLY IT.** `[LJ-1.537]`'s formula
is `∃̇ ( prAtL (suc zero) zero zero ∧̇ (var zero ∈̇ con m) )`
(`agents/tasks/LJ-1-537/Probe537.agda:153-157`), which carves the DIAGONAL of
`m`: one binder, two conjuncts, no value coordinate at all. That formula could
be written because `[LJ-1.537]`'s D-10 found the function it describes is the
IDENTITY. There is no identity here: the value of this table at an ordinal
`α ∈ δ` is a subset of κ, and a subset of κ is not α.

**MEASURED LINE COUNT.** `TableBody` and `TableFo` together span
`Probe549.agda:228-235`, **7 non-blank lines**, of which the missing conjunct
is the single token `Link`. In the W3 slice the same formula is written
unsplit at `runs/W3.agda:64-68`, **5 lines**. That slice, which carries the
formula alone with its header comment and its imports, is **68 lines**.

**AND THE THREE WRITTEN CONJUNCTS ARE NOT THE COST.** `module Table`
(`Probe549.agda:268-438`) spends them and closes all four `InjCode` conjuncts
from them plus the two readings of `Link`. The cost of the leg is conjunct 4.

## D-10, BEFORE ANY AGDA, AND IT IS THE CHOICE OF `b`

The brief orders the set named at `file:line` before any formula, and it says
"**The freedom in `b` is the whole point of the reduction**, and it is yours to
use."

**IT CANNOT BE USED. THE LARGEST ADMISSIBLE `b` IS ALREADY FREE, SO THERE IS
NO FREEDOM TO SPEND.** Two implications, three lines each, both typechecked:

- `power→subsets` (`Probe549.agda:179-181`): a code at `(δ , powL κ)` gives the
  obligation's conclusion, with `powL-sub` as the second conjunct.
- `subsets→power` (`Probe549.agda:186-190`): the obligation's conclusion gives
  a code at `(δ , powL κ)`, by `[LJ-1.546]`'s `code-target-mono`, IMPORTED and
  not rebuilt.

**SO `SuccIntoSubsets` IS B10.** `power→B10` and `B10→power`
(`Probe549.agda:193-199`) carry the equivalence to `InjL δ (𝒫 zf κ)` itself, at
any model record.

**THE STATEMENT CANNOT HAVE DRIFTED FROM `[LJ-1.546]`'s.** I did not retype it:
I IMPORTED `LJ-1-546.Probe546` (`Probe549.agda:87`), whose verdict is GO and
whose file carries no hole. `statement-is-pointwise` and
`pointwise-is-statement` (`Probe549.agda:169-175`) are the identity function in
both directions between `P546.SuccIntoSubsets` and this task's pointwise form.

**WHAT `[LJ-1.546]`'s REDUCTION DID BUY, AND IT IS REAL:** the `zf` record
leaves the statement. It bought no mathematics. I state this as a correction of
the brief's premise, with terms rather than prose, and the brief's own D-10
clause is what asked for it.

## WHICH INPUT OF `approx-carve` I CANNOT SUPPLY

The brief: "IF `approx-carve` DOES NOT REACH THIS TABLE, SAY SO PRECISELY AND
STOP. Name which of its inputs you cannot supply."

**THE METHOD REACHES THE TABLE. TWO INPUTS DO NOT EXIST.** `module Table`
(`Probe549.agda:268-438`) runs the method at this table and builds every part
of it except its own two parameters.

| `approx-carve`'s input | at this table |
|---|---|
| the `smallDom` bound | **BUILT**, `bnd` (`Probe549.agda:289-290`). It needs `s` and nothing else. |
| `hasSeparationL` | **BUILT**, `G` and `G-mem` (`:301-306`), sealed `opaque` as `[LJ-1.537]` seals its own. |
| the two membership readings | **BUILT**, `graph-in` (`:319-338`), `graph-mem` (`:359-368`), `graph-val` (`:370-385`). |
| the `Formula` | **conjuncts 1 to 3 BUILT, conjunct 4 MISSING.** |
| the ambient assignment | **MISSING.** |

**INPUT 1, `s`, IS NOT A CODING QUESTION AND I MEASURED THAT.** Section 6
(`Probe549.agda:551-600`) reads the three hypotheses on `s` back in both
directions:

    assignment→ambient : ... → ⟪ fst δ ⟫ ↪ ⟪ fst (powL κ) ⟫
    ambient→assignment : ⟪ fst δ ⟫ ↪ ⟪ fst (powL κ) ⟫ → Σ[ s ∈ ... ] ...

`Probe549.agda:565-580` and `:582-600`. **So input 1 IS the ambient statement
`κ⁺ ≤ 2^κ`, exactly, no more and no less.** Nothing in `src/` delivers it:
`[LJ-1.535]` closed the counting-site route
(`agents/tasks/LJ-1-535/lj-1.535-report.md:1`) and the bounded-subset theorem
(`src/L/BoundedSubset.lagda.md:1621`) is the OTHER leg.

**INPUT 2, `Link`, IS `[LJ-1.533]`'s WALL AT ITS THIRD SITE.** Both L-set
generators take a `Formula` (`src/L/Axioms/Full.lagda.md:144`, `:277`) and
`_↪_` carries none (`src/L/Cardinal.lagda.md:47`).

**THE RESIDUE, IN ONE TYPE.** `Residue δ κ` (`Probe549.agda:668-677`) is the
two inputs and their four laws, as one Σ. `residue-suffices` (`:679-681`)
spends it for the obligation; `residue-pays-B10` (`:685-689`) spends it for B10
outright, by composing with `[LJ-1.546]`'s implication. **Nothing in this file
and nothing in `src/` inhabits it.**

## THE LEASTNESS CLAUSE

**THE BRIEF SAID IT IS THE SUSPECT AND ASKED WHETHER I USED IT. I DID NOT, AND
NO TERM IN THIS FILE DOES.** `Residue` does not mention `SuccCardL`, and neither
does `module Table`, `link-suffices`, or any of sections 1 to 3.

**THAT IS NOT GOOD NEWS AND I WILL NOT REPORT IT AS SUCH.** The clause is not
removed from the problem. It is pushed ENTIRELY into input 1, and it is what
makes input 1 true: every member of δ must inject into κ, which is exactly what
"no ordinal L-cardinal strictly between κ and δ" says
(`src/L/GCH.lagda.md:51-52`). The reduction is clean because the whole
difficulty is on the other side of it.

**ONE PLACE `SuccCardL`'s OTHER COMPONENTS ARE SPENT, AND IT IS SECTION 5.**
`IsCardinalL δ`, the second component, is what refutes the shift producer and
the cheapest `b`. So the hypothesis is not inert in this file: its cardinal
clause does work, and only its leastness clause does not.

## THE SWEEP (C-42), MY OWN, AT TODAY'S TREE

C-42 says a refutation measures one site and the next action is the count. My
refutation is "no delivered producer reaches a code whose source is δ". I
counted the producers, and **THE COUNT BY NAME IS WRONG**.

**PRODUCERS OF AN INHABITED `InjCode` IN `src/`: THREE SHAPES, NOT ONE.**
`[LJ-1.546]` grepped for the name `InjCode` and found two sites, both
`shift-coded`. `L.InjChain` delivers the four conjuncts WITHOUT EVER WRITING
THE TYPE'S NAME, so a name sweep does not see it.

| shape | site | the pair | at this obligation |
|---|---|---|---|
| the shift | `src/L/CodedShift.lagda.md:37-40`, `src/L/Absorption.lagda.md:611-626` | `(sucʟ γ , γ)` | **REFUTED**, `no-ordinal-successor` |
| the inclusion | `src/L/InjChain.lagda.md:468` (sv `:518`, ij `:525`, dm `:532`, ran `:544`), opened by `InclGraph` `:575-598` and `OrdIncl` `:604-607` | `(D , C)` for `D ⊆ C` | **REFUTED**, `inclusion-fails` |
| composition | `src/L/InjChain.lagda.md:314` (svK `:380`, ijK `:391`, dmK `:402`, ranK `:420`) | `(D , C)` from two codes | produces nothing alone |

**THE SHIFT REFUTES ITSELF AT THIS SOURCE.** `no-ordinal-successor`
(`Probe549.agda:482-497`): if `δ ≡ sucʟ γ` for an infinite ordinal γ holding
every numeral, `shift-coded` codes δ into γ and `γ ∈ δ`, which `IsCardinalL δ`
forbids. Combined with `[LJ-1.546]`'s `code-source-determined`
(`agents/tasks/LJ-1-546/Probe546.agda:127-133`), which says a table has ONE
source, the shift cannot reach this obligation.

**THE INCLUSION IS THE ONE THAT NEEDED CHECKING, because it needs no ambient
function at all.** `inclusion-fails` (`Probe549.agda:635-648`): δ is not a
subset of `powL κ`, and the witness is `sucʟ κ`, a member of δ that is not a
subset of κ.

**WHY THE CORRECTION MATTERS.** A sweep by name reads as "one shape, refuted"
when in fact two more shapes have to be refuted, and one of them is not
obviously wrong at this pair. I record it so the next sweep does not repeat it.

**SITES IN THE TREE THAT CARRY THIS SHAPE: THREE, and one of them is only
partly measured.** `GCHStatement` (`src/L/GCH.lagda.md:65-68`) needs two codes and B9
needs a third:

- `InjL δ (𝒫 κ)` (`src/L/GCH.lagda.md:68`), this task. Source δ.
- `InjL Lδ δ`, B9 (`agents/tasks/LJ-1-523/Probe523.agda:258-261`). Source
  `Lset δ`. Measured NO-GO by `[LJ-1.533]`.
- `InjL (𝒫 κ) δ` (`src/L/GCH.lagda.md:67`), the hard leg. Source `𝒫 κ`.
  **PARTLY MEASURED, AND NOT AGAINST THE INCLUSION.** `[LJ-1.365]` measured
  that the delivered supplier at that goal is AMBIENT and that the goal refuses
  it: `agents/tasks/LJ-1-365/lj-1.365-report.md:47` reads
  "`F` of `InjL (𝒫 κ) δ` is a set plus a code, and the delivered supplier is the",
  and its CONTROL 2 is exit 42. **What no task I read has priced is whether the
  INCLUSION producer reaches it**, and that is the one route the other two rows
  do not have: `𝒫 κ ⊆ Lset δ` would give an inclusion code by
  `L.InjChain.InclGraph`, and `L.InjChain.Comp` would compose it with B9's
  code. **I did not build that, and the brief forbids me touching B9. I state
  it as a reading of the types and not as a measurement.**

## D-10, THE SECOND ANSWER: IS THE TARGET TRUE?

D-10 orders the truth of the target priced before its proof. **THE TARGET IS
TRUE**, and it is the easy half of GCH: with the L-order every member of
δ = κ⁺ injects into κ, and a well-ordering of κ of order type α is a subset of
κ × κ, which a pairing carries to a subset of κ.

**THE TREE HAS THE FIRST INGREDIENT AND NOT THE OTHER TWO.** The L-order at a
stage IS an L-set: `relL` with `relL-fill` and `relL-rep`
(`src/L/Choice/Table.lagda.md:795`, `:825`, `:829`), made unconditional by the
one line `src/L/Choice/Order.lagda.md:658` that opens `Ordered`. What
is missing is a pairing `κ × κ → κ` said IN THE OBJECT LANGUAGE, and an
object-language recursion that selects the order-type witness. `L.Ordinal.SquareLaw`
and `L.SquareLawClosed` are AMBIENT (`src/L/SquareLawClosed.lagda.md:325-329`),
which is the wrong side of `[LJ-1.533]`'s wall.

**SO THE TARGET IS NOT FALSE AND THIS IS NOT A `[LJ-1.507]`.** The stop is a
missing input, not a bad premise.

## RUNS AND PRICES

Every run deleted the file's `_build/2.8.0/agda/.../*.agdai` first, because Agda
skips a file whose content is unchanged and a run that skips measures nothing.

**THE TABLE BELOW IS ONE COMPARABLE SET, all measured on this pane after the
last edit to any file of this task.** An earlier set, taken while the pane was
busier, read 1.23 to 1.28 s for the W3 slice and 2.71 to 2.81 s for the probe.
**I do not subtract across the two sets and neither should the next brief.**

| run | what the file was | result |
|---|---|---|
| `runs/w3-1.out` to `runs/w3-3.out` | the W3 slice ALONE, TYPE ONLY, 68 lines | exit 0, 0.99 s, 0.98 s, 0.97 s |
| `runs/final-1.out` to `runs/final-3.out` | **the file exactly as this report describes it**, 689 lines, `Probe546` warm | exit 0, 2.53 s, 2.40 s, 2.43 s |
| `runs/baseline-546.out` | `Probe546.agda` ALONE, cold, the dependency this file adds to | exit 0, 1.60 s |
| `runs/full-with-546.out` | this file with `Probe546` ALSO cold | exit 0, 2.46 s |

**THIS FILE'S MARGINAL COST OVER ITS PREDECESSOR IS 0.86 s** (2.46 minus 1.60).
2.40 to 2.53 s is what a reader pays who already has `[LJ-1.546]`'s interface.

The staged runs are kept as the record of how the file was built, and their
seconds are NOT prices, because each checked a partial file against warm
dependencies: `runs/stage-a.out` (sections 0 to 1), `runs/stage-b.out` (to 2),
`runs/stage-c.out` (to 4), `runs/stage-d.out` (to 5), `runs/stage-e.out`
(to 6), `runs/stage-f.out` (to 8). Every one is exit 0.

**HEAP.** Peak resident 528,842,752 bytes, about 504 MiB; peak footprint
468,812,712 bytes, against the 8 GB cap (`runs/final-1.out`). No heap event and
no WALL.

**THE ESTIMATE, AGAINST THE MEASUREMENT.** The brief estimated about 220 lines
in the probe, of which the obligation is about 45, and for W3 about 25 lines
and under 2 minutes. **W3 came in at 68 lines and 0.97 to 0.99 s**, and the
formula itself is 5 of those lines (`runs/W3.agda:64-68`); the rest is the
header comment and the imports. The probe came in at 689 lines, three times
the estimate, and the reason is not the obligation: the obligation is not there.
The 689 lines are six measurements the brief did not ask for and one it did.

**WHAT RESISTED, AND IT WAS NOT THE MATHEMATICS.** FIVE red runs in total, and
every one of them was scope or syntax:

1. `isPropIsContr` lives in `Cubical.Foundations.Prelude`, not in
   `Cubical.Foundations.HLevels` (section 1).
2. `↪-inj` is the repository's own (`src/V/Presentation.lagda.md:37`), not the
   cubical library's (section 1, the same run).
3. `_⊎_` has to be imported to be written, not only `inl` and `inr`
   (section 5).
4. `∈sucV-elim`'s motive is `Type (ℓ-suc ℓ)` and `Empty.⊥` is not, so the
   descending case had to conclude in the goal rather than in `⊥` (section 5).
5. `Σ[_∈_]` at level 2 cannot sit under `_×_` at level 5 without parentheses,
   twice (section 8).

**THE RED RUNS ARE NOT IN `runs/`, AND THAT IS MY ERROR OF METHOD.** I reused
one output path per stage, so each `stage-*.out` holds only that stage's final
green run. The count above is from my own session record and not from a file a
reader can open. A later task should write `stage-N-red.out` before the fix.

**SECTIONS 2, 3, 4 AND 6 TYPECHECKED ON THE FIRST ATTEMPT.** I take that as
evidence about the D-10 answer and not about the difficulty of the conjuncts:
the reduction is cheap BECAUSE everything expensive is on the other side of
`Residue`.

## W2, ANSWERED

The brief did not state W2, and I answer it.

**THE MATHEMATICS IS AT THE GENERIC CARRIER THROUGHOUT.** `module Table` is
parameterized by δ and κ and by the assignment and the link, and it names no
cardinal, no stage and no numeral. `TableFo` takes the link as a parameter, so
one formula serves every producer a later task might write. `link-suffices` (`Probe549.agda:442-456`) and `Residue` (`:668-677`) are
stated at δ and κ with no hypothesis on either.

**THE ONE PLACE THAT IS NOT GENERIC IS SECTION 5, AND IT MUST NOT BE.** The
refutations spend `IsCardinalL δ`, `IsOrd`, the infinitude of κ and the
numerals. They are statements ABOUT a cardinal successor and are false without
it.

## W4, ANSWERED

**NOTHING WAS RETIRED AND NOTHING SHOULD BE.** No module left `src/`, so
`dev/ARCHIVE.md` takes no row from this task.

**PRICED THE OTHER WAY, AS W4 ASKS.** Written fresh today, sections 1, 2, 3 and
6 would be written exactly as they are. Section 4's four `InjCode` conjuncts
would NOT be rebuilt: they are `[LJ-1.414]`'s `code-from-graph`
(`agents/tasks/LJ-1-414/Probe414.agda:115-128`), and the only reason this file
carries its own copy is that `Probe414.agda:139` is a hole by design, so that
file cannot be a dependency of a green probe. **The restatement this suggests
belongs to a task that lands `code-from-graph` where a probe can import it, and
it is not mine to make.**

## WHAT THE NEXT BRIEF NEEDS FROM THIS ONE

1. **DO NOT FUND A TASK THAT SPENDS THE FREEDOM IN `b`.** There is none.
   `Probe549.agda:179-199` proves the statement is B10.
2. **THE RESIDUE IS `Residue δ κ` (`Probe549.agda:668-677`) AND IT IS TWO
   THINGS**: an ambient injection `κ⁺ ↪ 𝒫 κ`, and a `Formula S 3` describing
   it. A brief that asks for only one of the two asks for half a task.
3. **THE FIRST OF THE TWO IS A MATHEMATICS TASK AND NOT A CODING TASK.** It is
   `κ⁺ ≤ 2^κ` in L, it is where `SuccCardL`'s leastness clause is spent, and it
   needs a pairing on κ. `relL` (`src/L/Choice/Table.lagda.md:795`, made
   unconditional at `src/L/Choice/Order.lagda.md:658`) is the one ingredient
   the tree already has, and it is an L-SET, so it is on the right side of
   `[LJ-1.533]`'s wall.
4. **THE HARD LEG `InjL (𝒫 κ) δ` HAS NEVER BEEN PRICED AGAINST THE INCLUSION
   PRODUCER**, and the inclusion is the one route the other two rows do not
   have. `[LJ-1.365]` measured only that the AMBIENT supplier refuses there.
   See the sweep. That is the cheapest unpriced row I found.
5. **THE PRODUCER COUNT IS THREE AND NOT ONE.** Any future brief that reasons
   from "the only producer is `shift-coded`" is reasoning from a name grep.

## GATES RUN

Each exit 0, and each run as `/Users/alsg/Agentic/Bedrock/.venv/bin/python`
because this worktree carries no `.venv`, with the working directory left in
this worktree.

| gate | what it said |
|---|---|
| `scripts/gate/lint-prose.py --check` | clean |
| `scripts/gate/lint-agda.py --check` | clean |
| `scripts/site/weave-i18n.py --check` | clean |
| `scripts/gate/check-glossary.py --check` | clean |
| `scripts/measure/ledger.py --check` | "declaration clean; standing 33,523 lines measured over 100 masters" |
| `scripts/gate/check-probes.py --check` | "clean (6182 tracked files, no probe outside agents/tasks/ and no generated file)" |
| `scripts/pod/check-closure.py --check closure` | "clean (102 masters; closure, archive)" |
| `scripts/gate/check-fences.py --check` | "clean (102 masters, run threshold 3)" |
| `scripts/pod/check-spec-surface.py --check` | "clean (8 surface file(s), 201 declaration(s), 7 guarded rule home(s), 499 in-fence lines)" |
| `scripts/gate/check-rule-ids.py` | clean |

I did NOT run `make typecheck`. `git status --short` shows one entry, the
untracked `agents/tasks/LJ-1-549/`, so no master changed and a whole-tree
typecheck would measure nothing about this task.

**THE STANDING SIZE FIGURE, from the only admissible source
(`scripts/measure/ledger.py --brief`):** "standing 33,523 lines over 100
masters, measured from HEAD". This task changed no master, so it moves that
figure by 0.

I did not commit and did not push.

## ARCHIVE USED

- `archive/dev/JOURNAL-archived.md`: **READ, and it produced evidence for
  finding 1.** `archive/dev/JOURNAL-archived.md:3698` reads
  "  `hasPowerL`). Remaining after that: choice alone. **`[L2.4]` deleted the last".
  I read it to confirm that `hasPowerL` is a DISCHARGED field and not a
  hypothesis: the `[L2.3]` row records the power-set field being deleted from
  the record because the term exists. That is why `powL κ` needs no `zf`, which
  is the whole of finding 1.
- `archive/dev/LJ-dispatch-index.md`: **READ.**
  `archive/dev/LJ-dispatch-index.md:409` reads
  "| LJ-1.359 | Land the CSB corollary at the trophy's own InjL | LANDED GREEN, 34 LINES, exit 0 | The reader's step is now the tree's. It measured TWO of my citations FALSE, one of them stale |".
  I read it for the sweep: it is the only archived row that lands AT `InjL`, and
  it is the Cantor-Bernstein corollary (`src/L/CantorBernstein.lagda.md:51-55`),
  a CONSUMER of two codes and not a producer. It adds no fourth producer shape.
- `archive/dev/DECISIONS-archived.md`: **not used.** It is the archived `D<n>`
  series, which `dev/memos/LJ-4-pod-program-design.md` section 7.1 marks as not
  in force. No row of it bears on a code at a power-set target.
- `archive/dev/ORCHESTRATION.md`: **declined.** It is the orchestrator's
  operating rules, not a mathematical or coding record.
- `dev/ARCHIVE.md`: **READ.** `dev/ARCHIVE.md:89` reads
  "| `archive/src/2026-08-13-probe-sweep/` | **Empty since 2026-08-13.** A tombstone that maps 257 pre-ruling probe paths to their homes in `agents/tasks/<TASK>/` | `archive/src/2026-08-13-probe-sweep/README.md` |".
  I read it to confirm where this task's probe belongs before I wrote one. All
  three `.agda` files of this task are under `agents/tasks/LJ-1-549/`, and
  nothing is retired by this task, so the registry takes no row.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: **READ, and it CONFIRMS `[LJ-1.546]`'s
  item 4 with a sharper quote.** `dev/literature/devlin-II5.md:161` reads
  "> ... The result follows at once.".
  **THAT ELLIPSIS IS THIS TASK'S LEG.** The digest quotes 5.6's proof in full
  as far as `𝒫(κ) ⊆ L_{κ⁺}` and `|L_{κ⁺}| = κ⁺`, which is `2^κ ≤ κ⁺`, and then
  the source elides the other direction. `:164-166` explains only the elided
  step's FIRST half. So the project's literature pins the hard leg and says
  nothing about `κ⁺ ≤ 2^κ`, which is exactly input 1 of the residue. **A brief
  that funds `Residue` should pin that argument in the literature first, the
  way the hard leg is already pinned.**
- `dev/literature/truncation-and-selection.md`: **READ.**
  `dev/literature/truncation-and-selection.md:289` reads
  "1. **Is the goal a proposition?** Then `PT.rec` applies and there is nothing to".
  That is the first question of its decision procedure, and it is why `rec2`,
  `graph-mem` and `graph-val` (`Probe549.agda:342-390`) can unpack two nested
  truncated existentials with no selection at all: each of their goals is
  `hProp`-valued, membership by `snd (_ ∈ _)` and a value equation by
  `setIsSet`. It is also why `Residue` is UNTRUNCATED where the obligation's
  conclusion is truncated: the witness `s` is not unique, so nothing in that
  file un-truncates it, and the truncation is taken once at `link-suffices`.
- `dev/literature/digest.md`: **not used.** It pins the orthodox form of the
  rud route. This task is a coding question inside the Def tower and turns on
  no rud fact.
- `dev/literature/terms-2026-08.md`: **declined.** It is the terminology
  dossier for the owner's naming ruling. This task adds no `dev/glossary.toml`
  entry and coins no term, and the Boundary forbids me choosing one.
- `dev/literature/geology.md`: **not used.** Set-theoretic geology sources for
  `[L6]`. Nothing in it bears on a code at a power-set target.
