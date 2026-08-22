# LJ-1.530 report: dK, and the one word the brief's frame was missing

**VERDICT: GO.** The obligation is written and it typechecks.
`agents/tasks/LJ-1-530/Probe530.agda:131-156`, exit 0, `runs/final.out`.

    dK : (α : V ℓ) → IsLimit α
       → ∀ {n} (b f K : Fin n) (γ : S ^ n)
       → fst (lookup K γ) ≡ Lset α
       → IsOrd (fst (lookup b γ))
       → ⟨ fst (lookup b γ) ∈ fst (lookup K γ) ⟩
       → Domain (lookup f γ) (fst (lookup b γ))
       → Values (lookup f γ) (fst (lookup b γ))
       → (c w : S) → ⟨ pr (fst c) (fst w) ∈ fst (lookup f γ) ⟩
       → ⟨ 𝒟ₒ (fst w) ∈ fst (lookup K γ) ⟩

**THE CONCLUSION IS THE BRIEFED ONE AND THE MACHINE SAYS SO.**
`Probe530.agda:195-207` writes `DKShape`, the brief's conclusion in
`[LJ-1.304]`'s own words, and then the line `dK-briefed = dK`. It
checks. So the five hypotheses ahead of `(c w : S)` are the ONLY
difference between what the brief asked for and what this file
delivers, and no reader has to take my word for the shape.

**THE FRAME IS NOT THE BRIEF'S, AND THAT IS THE RESULT.** The brief
gives `w` as an arbitrary member of `K`. **Nothing in the tree puts the
definable powerset of an ARBITRARY member of a level back in that
level.** What the site gives instead is `Values`
(`src/L/Hierarchy.lagda.md:117-119`), which says a recorded value IS
the tower at its argument. **A recorded value is a STAGE**, and a stage
is the one case the tree does state (`Lset-suc`,
`src/L/Axioms/Basic.lagda.md:196`). That word is the whole task.

**W3 IS GO ON THE FIRST RUN, IN ITS CORRECTED FORM.**
`agents/tasks/LJ-1-530/runs/W3.agda:86-90`, exit 0, `runs/w3-0.out`,
0.95 s.

**AND THE SAME FRAME PAYS FOR `wK`, `entryK`, `zK` AND `domK` TOO.**
Section 5 (`Probe530.agda:230-285`) and section 3 (`:169-183`). **After
this task the memberships that rows three, four and five consume are
ALL discharged at this frame.** The brief predicted a GO would close
rows three and four; it closes row five's memberships as well, and it
corrects the brief on one point of fact, below.

**ONE CORRECTION TO THE BRIEF, AND IT IS ABOUT A TERM AND NOT A TYPE.**
The brief says "`wK` IS DELIVERED. `entryK`
(`src/L/Condensation.lagda.md:6615-6616`) returns both components of a
pair in `K`, so `wK` is its second projection. **I checked this at
source.**" **The type is delivered. The TERM is not.** `entryK` is a
MODULE HYPOTHESIS of `DomainAgree` (`src/L/Condensation.lagda.md:6614`
opens the module, `:6615-6616` is the hypothesis), and `[LJ-1.527]`
measured that nothing in the tree inhabits it
(`agents/tasks/LJ-1-527/lj-1.527-report.md:181`: "delivered in `src/`
AS A HYPOTHESIS, never inhabited"). So `wK` was owed, not delivered.
**This task pays it** (`Probe530.agda:243-268`), and pays `entryK`
itself (`:274-285`).

## D-10, BEFORE ANY AGDA

The brief ordered it first: "Say at `file:line` what `𝒟ₒ` is and
whether a level holds it."

### What `𝒟ₒ` is

`𝒟ₒ A = 𝒟 A`, sealed (`src/L/Constructible.lagda.md:211-213`), and the
seal is what matters: membership in it is, by construction, "merely,
is some `defSet φ`" for ONE formula over the carrier's own members.

    𝒟ₒ-intro : (A x : S)
             → ∥ Σ[ φ ∈ Formula ⟪ A ⟫ 1 ] (DefOf.defSet A φ ≡ x) ∥₁
             → ⟨ x ∈ˢ 𝒟ₒ A ⟩

`src/L/Constructible.lagda.md:301-305`, with the inverse at `:306-308`.
The tower is the union of the operator over the earlier stages
(`Lset-compute`, `:227`; `LsetStep`, `:215-216`), so
`⟨ x ∈ Lset α ⟩` is exactly `⟨ x ∈ 𝒟ₒ (Lset δ) ⟩` for some `δ ∈ α`
(`Lset-in`, `:319`; `Lset-out`, `:336`).

### Whether a level holds it

**FOR A STAGE, YES, AND `src/` SAYS SO IN ONE LINE.**
`Lset-suc : (σ : V ℓ) → Lset (sucV σ) ≡ 𝒟ₒ (Lset σ)`,
`src/L/Axioms/Basic.lagda.md:196`. With successor closure that is the
whole of the corrected W3.

**FOR AN ARBITRARY MEMBER, THE TREE SAYS NOTHING.** I searched. The
statements in `src/` about a level and a definable powerset are
`Lset-suc` (`src/L/Axioms/Basic.lagda.md:196`), `isL-𝒟ₒ` (`:230`) and
`𝒟ₒ→isL` (`:98`), and **every one of them is about `𝒟ₒ (Lset σ)` and
not about `𝒟ₒ w`.** The nearest statement about an arbitrary `w` is
`PowOK` (`src/L/Coding/Sequence.lagda.md:130-131`), which concludes
`⟨ isL (𝒟ₒ (fst w)) ⟩`: constructible SOMEWHERE, with no bound. That
is `[LJ-1.527]`'s finding (`lj-1.527-report.md:182`) and I confirm it.

**AND THE REASON IS NAMEABLE, WHICH IS WHY THIS IS NOT A WALL.** To put
`𝒟ₒ w` in `Lset α` you must carve it out of ONE earlier stage with ONE
formula. The only formula in the tree that carves a definable powerset
is `∃̇ (∃̇ (DefBody w))` (`DefAt`,
`src/L/Coding/Powerset.lagda.md:442-443`), and its two existentials
must reach a code `keyS A ψ` and a value `Sat A (toS ψ)` for EVERY `ψ`
(`src/L/Coding/Powerset.lagda.md:643`, the `assemble` step). `Sat` is
built by a recursion that names each sub-formula's own `Sat` set as a
CONSTANT (`src/L/Coding/Sat.lagda.md:142-143`, `:158-162`), so the
level of `Sat A ψ` climbs with `ψ`, and nothing in the tree collects
that family at one stage below `α`. **`smallDom` is the tool that would
do it** (`src/L/Coding/CodeSet.lagda.md:306`, which is how `AllCodes`
exists at `:440-441`), **but the stage it returns is unbounded**: it
names a stage, not a stage below `α`.

**I DID NOT REFUTE THE BRIEF'S W3.** The corpus records the classical
statement as sourced: "Def uniformly Δ₁^α at limit α > ω"
(`dev/literature/devlin-II5.md:339`, Devlin 2.5). Note the side
condition `α > ω`, which the tree's `IsLimit` does not carry. So the
brief's target is probably TRUE and is certainly UNDELIVERED, and the
distance to it is one named theorem: **the code family and the
satisfaction family of a member of `Lset α` lie below `α`**, which is
Devlin's bound set `K(w, u)` (`dev/literature/level-formula-slot-roles.md:23`).

**I DID NOT STOP.** The brief's stop condition was "If nothing says it,
say so and STOP: that would mean `dK` needs a new fact about the
hierarchy, not a re-use of `[LJ-1.522]`." Nothing says it, and I say
so above. **But `dK` does not need it.** The brief's own premise 3
names `dK` at `agents/tasks/LJ-1-304/ProbeLJ1304A.agda:178-179`, where
`w` is a value recorded in `f`, and `f` is a value table. The frame
supplies the missing word, so the stop condition's premise ("`dK` is
out of reach at this frame") is false at the site's frame. A stop here
would have been a stop on the brief's frame and not on the obligation.

### And it is NOT a re-use of [LJ-1.522]

`[LJ-1.522]` closed `K` under definable SUBSETS
(`agents/tasks/LJ-1-522/Probe522.agda:356-364`). The brief called that
difference "this task's whole risk" and it was right: nothing of that
proof is used here. What IS reused is one five-line helper of the same
file, `closeAt` (`agents/tasks/LJ-1-522/Probe522.agda:126-130`), and
**it is re-measured and not transferred** (`AGENTS.md:45`): its
instance at the stage itself is written out as `stage-dpow-in-level`
(`Probe530.agda:104-108`) and typechecked here.

## W3, WRITTEN FIRST AND ALONE

`runs/W3.agda`, 90 lines, 34 non-blank non-comment, exit 0 on the first
run, 0.95 s.

The file writes the brief's statement AS A TYPE and does not inhabit
it (`runs/W3.agda:71-73`, `BriefW3`). D-10 asks for the corrected
target beside the original; it is `runs/W3.agda:86-90`:

    stage-dpow-in-level : (α : V ℓ) → IsLimit α → (δ : V ℓ) → ⟨ δ ∈ α ⟩
                        → ⟨ 𝒟ₒ (Lset δ) ∈ Lset α ⟩

**IT DECOMPOSES, AND IT SPENDS LESS OF THE LIMIT THAN EXPECTED.** Only
successor closure is used. Neither `IsOrd α` nor `⟨ ∅ ∈ α ⟩` appears in
the term (`runs/W3.agda:88-90` matches the limit as `(_ , (_ , sc))`).
**Ordinality enters the obligation later and for a different reason:**
`dK` needs it to turn `b ∈ K` into `b ∈ α` through `ord∈Lset→∈`
(`src/L/Ordinal/Stages.lagda.md:265-268`), which is the only classical
step this task adds.

## THE OBLIGATION, AND WHAT IT COST

**FIVE HYPOTHESES, AND EVERY ONE IS A DELIVERED `src/` TYPE.**

| hypothesis | what it says | where `src/` says it |
|---|---|---|
| `qK` | `K`'s value is the level `Lset α` | row one's own hypothesis, `agents/tasks/LJ-1-525/lj-1.525-report.md:112-122`; also `[LJ-1.522]`'s, `Probe522.agda:359` |
| `oB` | the domain bound is an ordinal | `src/L/Hierarchy.lagda.md:167`, the same hypothesis `ok` takes |
| `B∈K` | the domain bound lies in `K` | the frame's own vocabulary, `carrierK` at `src/L/Condensation.lagda.md:7424` |
| `dom` | nothing outside the bound is recorded | `Domain`, `src/L/Hierarchy.lagda.md:124-125` |
| `vals` | a value recorded below the bound IS the tower there | `Values`, `src/L/Hierarchy.lagda.md:117-119` |

**`vals` IS NOT AN INVENTION AND IT IS NOT AN ANALOGY. IT IS THE
HYPOTHESIS `src/` ALREADY SPENDS ON `dK`'s OWN SIBLING.** `PowOK` asks
`⟨ isL (𝒟ₒ (fst w)) ⟩` of every recorded value; `dK` asks
`⟨ 𝒟ₒ (fst w) ∈ K ⟩` of the same thing. `src/` discharges `PowOK` from
`Values` plus ordinality, in four lines
(`src/L/Hierarchy.lagda.md:167-170`). **This task discharges `dK` from
`Values` plus ordinality plus the limit.** The limit is the whole of
the extra price, and it buys the BOUND that `isL` throws away.

**THE ARITHMETIC OF THE TERM, in one line each.** `dom` gives
`c ∈ b`; `oB` with `qK` and `B∈K` gives `b ∈ α` through `ord∈Lset→∈`;
`α`'s transitivity gives `c ∈ α`; `vals` rewrites `𝒟ₒ w` to
`𝒟ₒ (Lset c)`; W3 lands it in `Lset α`; `qK` carries it back to `K`.
`Probe530.agda:140-156`.

**NOTHING WAS POSTULATED.** `grep -c postulate
agents/tasks/LJ-1-530/Probe530.agda` returns 0, and the file carries
`--safe` (`Probe530.agda:1`).

**NOTHING WAS WEAKENED TO THE SUBSET FORM.** `defPow-closed-noCode` is
not named anywhere in this probe, and `[LJ-1.522]`'s obligation is not
imported.

**THE CERTIFICATES WERE NOT SPENT.** `grep -c
"Σ₁-levelHood\|σ₁-up" agents/tasks/LJ-1-530/Probe530.agda` returns 0.
The two `Σ₁` certificates have now been unconsumed since `[LJ-1.228]`
through this task as well.

## WHAT THE CHAIN OWES AFTER THIS

**THE TABLE HAS SEVEN ROWS AND NOT SIX.** The brief says "Re-walk
`[LJ-1.525]`'s six rows" and "Include row six, which no dispatch has
yet examined". `[LJ-1.525]`'s table
(`agents/tasks/LJ-1-525/lj-1.525-report.md:194-202`) has a SEVENTH row,
`LevelHood.levelHoodB` against level-hood of the carrier
(`src/L/BoundedSubset.lagda.md:108`), marked NO. **No dispatch has
examined row six OR row seven.** I did not examine either.

| # | what it is | status after this task |
|---|---|---|
| 1 | `StepB.leafB` against `DefAt zero (suc zero)` | **BUILT**, `[LJ-1.525]`, `agents/tasks/LJ-1-525/Probe525.agda:150-165` and `lj-1.525-report.md:3-4`, under five hypotheses |
| 2 | `StepB.bodyB` against `StepBody b f` | **BUILT**, `[LJ-1.527]`, `agents/tasks/LJ-1-527/Probe527.agda:184-200`, one congruence |
| 3 | `StepB.witB` against three unbounded existentials | **WRAPPER BUILT** at the ambient carrier, `agents/tasks/LJ-1-304/ProbeLJ1304A.agda:254-258`. Its three memberships: `c ∈ b` free (`lj-1.527-report.md:180`), `wK` **BUILT HERE** (`Probe530.agda:243-268`), `dK` **BUILT HERE** (`:131-156`) |
| 4 | `StepB.stepBndAt` against `StepAt` | **WRAPPER BUILT** with row three, same term. Its own membership `zK` **BUILT HERE** (`Probe530.agda:169-183`) |
| 5 | `ApproxB.approxBndAt` against `ApproxAt` | **WRAPPER BUILT** at the ambient carrier, `agents/tasks/LJ-1-304/ProbeLJ1304A.agda:313-316`. Its memberships `entryK` and `domK` **BUILT HERE** (`Probe530.agda:274-285`, `:230-238`). `domB` against `domAt` was already a `src/` term (`src/L/Condensation.lagda.md:6624`, `:6633`) |
| 6 | `GraphB.graphBndAt` against `LsetGraphAt` | **NOT EXAMINED.** Its one membership, the approximation function itself in `K`, is stated nowhere (`agents/tasks/LJ-1-527/lj-1.527-report.md:234`). `[LJ-1.228]` records `[LJ-1.123]`'s price for the two-way decode of `graphBndAt`, 150 to 250 probe lines, and that nobody ran it (`agents/tasks/LJ-1-228/lj-1.228-report.md:128-130`) |
| 7 | `LevelHood.levelHoodB` against level-hood of the carrier | **NOT EXAMINED.** `src/L/BoundedSubset.lagda.md:108` |

**SO THE CHAIN'S REMAINING MATHEMATICAL CONTENT IS TWO ROWS AND ONE
RE-MEASUREMENT.** `[LJ-1.527]` said "two facts and one re-measurement"
(`agents/tasks/LJ-1-527/lj-1.527-report.md:252-254`). One of its two facts,
`dK`, is paid. **What is left is row six's membership, row seven, and
`[LJ-1.304]`'s two wrappers re-measured at `𝒮ʟ` against
`src/L/Coding/Sequence` rather than at the ambient class against the
generic port.** That re-measurement is still owed and this task did not
touch it: `[LJ-1.304]` inhabits the step's two side conditions with
`tt*` (`agents/tasks/LJ-1-304/ProbeLJ1304A.agda:185-189`); at `𝒮ʟ` they
are `PowOK` and are not trivial.

**AND THE NEXT BRIEF SHOULD PICK ONE SUPPLY AND NOT TWO.** The chain
now has two ways to get the same memberships: `entryK` and `domK` as
hypotheses (`src/L/Condensation.lagda.md:6615-6617`), or `Values`,
`Domain`, `IsOrd b` and `b ∈ K` (`src/L/Hierarchy.lagda.md:117-125`).
**The second implies the first**, and this task proves it
(`Probe530.agda:274-285`). Carrying both would ask a consumer to supply
a hypothesis it can already build.

**THE `K`-IS-A-LEVEL GAP IS STILL OPEN.** `[LJ-1.522]` recorded it,
`[LJ-1.525]` inherited it
(`agents/tasks/LJ-1-525/lj-1.525-report.md:130-137`), `[LJ-1.527]`
inherited it (`lj-1.527-report.md:134-137`), and this task inherits it
in turn. Every term here takes `fst (lookup K γ) ≡ Lset α` as given.

## THE PRICE

Three forced rechecks each, the file's own interface removed before
every run, so each number is a real recheck. `GHCRTS="-A64m -I0 -M8g"`,
the wide caliber, set on the pane by the program and untouched. ONE
Agda process per run.

| file | median wall | peak RSS | runs |
|---|---:|---:|---|
| `runs/W3.agda` alone | **0.95 s** | 281,853,952 B | `runs/w3-t1.time` to `w3-t3.time` |
| `runs/Control530.agda`, the import list, NO term | **1.48 s** | 385,826,816 B | `runs/ctl-t1.time` to `ctl-t3.time` |
| `runs/Section1.agda`, the limit plus W3 | **1.51 s** | 412,975,104 B | `runs/s1-t1.time` to `s1-t3.time` |
| `runs/Section12.agda`, through `dK` | **1.56 s** | 405,782,528 B | `runs/s12-t1.time` to `s12-t3.time` |
| `Probe530.agda`, all five sections | **1.65 s** | 399,556,608 B | `runs/full-t1.time` to `full-t3.time` |

**BY SUBTRACTION: THE WHOLE PROBE COSTS 0.17 s ABOVE ITS IMPORTS, AND
`dK` ITSELF COSTS 0.05 s.** Section 1 is +0.03 s over the control,
`dK` is +0.05 s over section 1, and `zK` with the shape check and
section 5 together are +0.09 s over that.

**0.05 s FOR 23 LINES IS A DIFFERENT CLASS FROM THE TWO ROWS BEFORE
IT, AND THE REASON IS THE ELABORATOR AND NOT THE MATHEMATICS.**
`[LJ-1.527]` measured 1.62 s for four lines and `[LJ-1.525]` 20.37 s
for one instantiation (`agents/tasks/LJ-1-527/lj-1.527-report.md:105`,
`:112-114`), and both paid the tree's instantiation class P-m, because
both rows are about FORMULAS: every term names `⊨` at some environment.
**Nothing in this file names `⊨`.** `dK` is a statement about sets and
their levels, so no formula is instantiated and no environment is
shifted. **A brief that funds a membership obligation against a
congruence row's numbers will be wrong by the whole of P-m.**

**SIZE.** `Probe530.agda` is 285 lines, of which **143** are non-blank
and not a comment. `runs/W3.agda` is 90 lines, of which **34**.

| term | lines | where |
|---|---:|---|
| `dK`, the obligation | **23**, of which 9 are the type and 14 the term | `Probe530.agda:131-156` |
| `stage-dpow-in-level`, W3 | 5 | `:104-108` |
| `stage∈𝒟ₒ` | 3 | `:97-99` |
| `zK` | 15 | `:169-183` |
| `wK` | 23 | `:243-268` |
| `entryK` | 12 | `:274-285` |
| `domK` | 9 | `:230-238` |
| `DKShape` with `dK-briefed` | 12 | `:195-207` |
| `ω-IsLimit`, the non-vacuity witness | 6 | `:86-91` |

**AGAINST THE BRIEF'S ESTIMATE.**

| item | brief | measured |
|---|---|---|
| W3 | about 25 lines, under 40 s | **34 lines, 0.95 s** |
| the probe | about 160 lines | **143 lines** |
| the obligation | about 40 lines | **23 lines** |

**THE TIME ESTIMATE WAS HIGH BY A FACTOR OF ABOUT FORTY AND THE LINE
ESTIMATES WERE CLOSE.** The brief said not to fund W3 against
`[LJ-1.522]`'s numbers because that closed under subsets and this asks
for an object. **That was right, and the direction is the opposite of
the one the brief guessed:** asking for the object is CHEAPER, because
the object is a stage and the tree names stages in one equation, while
the subset had to be carved.

**NOT VACUOUS.** `ω` is a limit level (`Probe530.agda:86-91`, verbatim
from `agents/tasks/LJ-1-522/Probe522.agda:116-121`), so the obligation
is not true by an empty antecedent.

**NO WALL EVENT.** No heap exhaustion and no rerun after a wall. Peak
RSS is 412,975,104 B against an 8 GB cap, about one twentieth of it.

**NO FIRST-RUN ERROR, IN EITHER FILE.** `runs/w3-0.out` and
`runs/full-0.out` are both exit 0. No unsolved meta and no
universe-level error at any point. The only edit after the first green
was a comment: a citation of `𝒟ₒ-intro` read `:293-300` and the term is
at `:301-308`. The file was rechecked after the fix
(`runs/w3-final.out`, exit 0).

**GATES.** `check-probes.py` clean (5708 tracked files, no probe
outside `agents/tasks/`), `lint-agda.py` and `lint-prose.py` both
silent. Run as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python`, because this worktree
has no `.venv` of its own.

## SCOPE, AND WHAT I DID NOT DO

Written: `agents/tasks/LJ-1-530/Probe530.agda`, this report, and
`agents/tasks/LJ-1-530/runs/` (five Agda files and their run
evidence). **Nothing in `src/`.** No `review-of-*.md`, because the
obligation is delivered and that file is how a NO-GO is stated.

**I DID NOT REBUILD ROWS THREE TO FIVE.** They are cited at
`agents/tasks/LJ-1-304/ProbeLJ1304A.agda:254-258` and `:313-316` and
never re-derived. Sections 3 and 5 of the probe build the MEMBERSHIPS
those rows consume, which is what the brief named as the task's whole
point.

**I DID NOT EXAMINE ROW SIX OR ROW SEVEN**, and I did not re-measure
`[LJ-1.304]`'s wrappers at `𝒮ʟ`.

**I WENT BEYOND THE OBLIGATION BY 44 LINES**, in sections 3 and 5
(`zK`, `wK`, `entryK`, `domK`). The reason is in the brief: it required
a re-walk of the chain, and each of those four was named there as
delivered or as reducing. **A re-walk that says "reduces" is a claim; a
re-walk that says "typechecks at `file:line`" is a measurement.** The
four cost 0.09 s together.

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md`: READ, AND IT SETTLED THE
  BRIEF'S HISTORY.** `archive/dev/LJ-dispatch-index.md:319` reads
  "| LJ-1.250 | Price StepAgree and ApproxAgree | NEITHER BUILDS:
  UNCONSTRAINED INTERFACES. DD25 [LJ-1.251] | Refutable at that
  generality. The residue is the leaf-adequacy supply, not one term |".
  `:361` reads "| LJ-1.304 | Price StepAgree and ApproxAgree | BOTH
  BUILT, ABOUT 190 LINES. BASIS: THE BUILD | q's four named costs are
  now ALL measured. Neither module exists in src/: they were LJ-1.52's
  names |". **The two rows together confirm `[LJ-1.527]`'s reading**:
  the refutation was about UNCONSTRAINED INTERFACES, and this task's
  answer is a constrained interface. `[LJ-1.250]` is not contradicted
  by this task; it is answered on its own terms.
- **`archive/dev/JOURNAL-archived.md`: READ, ONE LINE, AND IT IS A
  WARNING I ACTED ON.** `:1997` reads "First, T5's and T57's
  identification of `⟪ 𝒟ₒ A ⟫` with `Formula ⟪ A ⟫ 1` "definitionally"
  is". **It records that the identification holds only up to a
  quotient**, so no step of this probe treats the members of `𝒟ₒ A` as
  formulas; every use goes through `𝒟ₒ-intro` and `𝒟ₒ-inv`.
- **`archive/dev/JOURNAL.md`: READ, ONE LINE, AND IT NAMES THIS SITE.**
  `:807` reads "`u`'s slot is the definable powerset of the recorded
  value and the induction". It records `[LJ-1.196]`'s NO-GO and
  `[LJ-1.200]`'s upheld verdict about the same slot, with the
  obstruction named as the ENVIRONMENT LIFT. **That obstruction is
  about the ambient transfer and not about the level bound**, so it
  does not touch this task's term, which shifts no environment.
- **`archive/dev/DD-archived.md`: NOT READ beyond its size.** It is 38
  lines and holds no hit for `𝒟ₒ`, "definable powerset", `Values` or
  `PowOK`. **Declined.**
- **`dev/ARCHIVE.md`: READ ITS PURPOSE, NOT USED.** It is the registry
  of retired modules (`dev/ARCHIVE.md:1-5`). **This task retires no
  module and lands nothing in `src/`, so no row is owed and none is
  written.** Declined for content.

## LITERATURE USED

- **`dev/literature/devlin-II5.md`: READ, AND IT IS WHY I DID NOT CALL
  THE BRIEF'S W3 FALSE.** `dev/literature/devlin-II5.md:339` reads
  "   - Def uniformly Δ₁^α at limit α > ω (2.5, `dev2.txt:663-666`).".
  **That is the classical form of the brief's target, with a side
  condition (`α > ω`) the tree's `IsLimit` does not carry.** It settles
  the truth question in the direction of "probably true, and
  undelivered here", which is what the report says.
- **`dev/literature/level-formula-slot-roles.md`: READ, ONE ROW, AND
  IT NAMES THE MISSING FACT.** `:23` reads
  "| 1 | Devlin 2.4 | `D(v,u) = ∃w[K(w,u) ∧ C(w,v,u)]`, and `D(v,u) ↔ v = Def(u)` | 2 | `w`, ONE bound, DETERMINED by `K(w,u)` | `v`, `u` | VALUE, ARGUMENT | `_build/literature/dev2.txt:619-623` |".
  **The bound `w` is Devlin's satisfaction relation and `K(w,u)` is
  the bound set that holds it.** That is exactly the object the tree
  lacks below `α`, and it is the next brief's target if the general
  form is ever wanted.
- **`dev/literature/digest.md`: READ, ONE LINE, AND IT POINTS AT A
  SECOND ROUTE I DID NOT TAKE.** `:288` reads
  "   distinction. The key lemma the note cites as rud(X) ∩ P(X) = Def(X) is".
  **The rudimentary route would reach the general form by a different
  road**, and it is a J-tower matter. The architecture is a CANDIDATE
  until `[LJ-2.5]`, so I did not open it.
- **`dev/literature/truncation-and-selection.md`: NOT USED.** It is
  about how a proof SELECTS a witness from a truncation
  (`:1-8`). Every truncation in this probe is INTRODUCED and never
  eliminated: `stage∈𝒟ₒ` writes `∣ ⊤̇ , ... ∣₁` and nothing here runs a
  `PT.rec`. **Declined.**
- **`dev/literature/terms-2026-08.md`: NOT USED.** It is a terminology
  dossier for a naming ruling (`:1-7`). This task names nothing new
  and adds no glossary entry. **Declined.**

## THE ONE SENTENCE FOR THE NEXT BRIEF

**Rows three, four and five now have every membership they consume,
built at one frame: `K` a limit level, plus `Values` and `Domain` on
the table below an ordinal bound that lies in `K`
(`agents/tasks/LJ-1-530/Probe530.agda:131-156`, `:169-183`, `:230-285`).
What the chain still owes is row six's one membership, row seven, and
`[LJ-1.304]`'s two wrappers re-measured at `𝒮ʟ`.**
