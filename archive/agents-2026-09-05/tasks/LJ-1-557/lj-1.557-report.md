# LJ-1.557 report: an internal code for one member of the successor

## HEAD
head_slot: coder
machine: shared
verdict: GO

The report was written as a skeleton before any Agda and filled as each answer
landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-557/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M8g"`, one Agda process at a time. I did not set
`GHCRTS`. No heap event. Nothing is postulated, the probe carries `--safe`,
and there is no hole. The probe is a raw `.agda` file, so it carries no
` ```agda ` fence, counts 0 in-fence lines, and the ratio bar cannot fire on
it. Nothing lands in `src/`.

## VERDICT

**GO. THE OBLIGATION IS BUILT.**
`agents/tasks/LJ-1-557/Probe557.agda::member-code-into-kappa`,
`Probe557.agda:275-314`.

**THE PROBE IS GREEN, EXIT 0, THREE COLD RUNS** (`runs/final-1.out` to
`runs/final-3.out`, 4.56 s, 4.58 s, 4.59 s). It carries no hole and no
postulate.

The witness meter agrees. The declared obligation:
`pass exit=0 agents/tasks/LJ-1-557/Probe557.agda::member-code-into-kappa`,
`0 UNRESOLVED of 1`, `probe_red=False` (`runs/witness-1.out`). The nineteen
other terms the file delivers also all resolve, `0 UNRESOLVED of 19`
(`runs/witness-2.out`).

**BOTH D-10 CHECKS ARE NO, AND THE OBLIGATION IS STILL BUILT. THAT IS THE
FINDING.** The two checks are about `InternalLeastCard`. The obligation names
no stage and no `orderAt`. The two NOs are not a wall: read together they NAME
THE FRAME THAT WORKS, and moving to that frame is one substitution, not a
chapter.

## THE TWO CHECKS

Both answered at `file:line`, before any Agda, as the brief orders.

### CHECK 1. Does the carved code land in the stage `InternalLeastCard` selects over? **NO.**

The stage is `SiteBound`'s `β` (`src/L/Cardinal.lagda.md:237`, `open SiteBound κ`),
and `SiteBound` is `stageBound` (`src/L/Cardinal.lagda.md:163-169`).
`stageBound a p = bound2 ω (stage a p)` (`src/L/Choice/Stage.lagda.md:366-368`),
so `β` is a bound on `ω` and on the stage of `κ` and on nothing else.

`InternalLeastCard.Good` demands the code as a MEMBER of that stage:
`Good δ = (∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) κ (up δ) ∥₁) , squash₁`
(`src/L/Cardinal.lagda.md:239-240`).

The code is carved over `Carve`'s own bound, a sealed `boundingOrd` on the
stages of the PAIRS (`src/L/InjChain.lagda.md:75-93`), and the pairs appear
above the stage of their members. **The tree states no comparison of the two
bounds.**

**THIS WAS ALREADY MEASURED AT THIS MODULE, AND I DID NOT REDISCOVER IT.**
`[LJ-1.425]` attacked exactly `InternalLeastCard`'s `nonempty` and stopped:
"`internal-nonempty` is a hole at `Probe425.agda:92`. Agda reports
`UnsolvedInteractionMetas` (`runs/final-hole.out`, exit 42, 1.93 s) ... The
`δ` conjunct is paid. The `F` conjunct is not."
(`agents/tasks/LJ-1-425/lj-1.425-report.md:65-71`). Its `## D-10` closes with
"The identity graph as a member of `Lset β` is false at this generality. The
existence claim with that witness is false as written."
(`agents/tasks/LJ-1-425/lj-1.425-report.md:51-53`).

**I RE-MEASURED THE SHAPE AT THIS FRAME RATHER THAN INHERIT IT** (AGENTS.md:45,
a measured cure does not transfer by analogy). `Frame` (`Probe557.agda:98-149`)
writes both demands at a member `a` of δ as TYPES and typechecks them alone
(`runs/W3.agda`, `runs/w3-1.out` to `w3-3.out`, exit 0). One direction is free
and green, `Frame.bridge` (`Probe557.agda:122-123`): a stage-bounded code IS a
code. The other direction is `Frame.Converse` (`Probe557.agda:129-130`), a type
with no inhabitant in this file and no term of this file named after it.

### CHECK 2. Does the leastness of δ refute the bad branch INTERNALLY, the way `member-into-kappa` refutes it ambiently? **NO, NOT THROUGH `InternalLeastCard`. THE ORDER IS WRONG.**

`InternalLeastCard` selects with `leastOf (orderAt β oβ)`
(`src/L/Cardinal.lagda.md:247`), and its leastness field is stated at that same
order: `δ-min : (b : Mem (Lset β)) → ⟨ Good b ⟩ → (SWO._<∙_ (orderAt β oβ) b δ-card → Empty.⊥)`
(`src/L/Cardinal.lagda.md:261-264`).

`orderAt` is the BIRTH order on the members of a stage
(`src/L/Choice/Step.lagda.md:730`; it is `∈-induction famStep`, and `famStep`
is `Family.famOrder` at `src/L/Choice/Step.lagda.md:703-710`, whose comparison
`_≺_` is built from `bornAt`). **It is not ambient membership.**

What the leastness clause of `SuccCardL` consumes is `IsCardinalL c`
(`src/L/GCH.lagda.md:51-52`), and `IsCardinalL` is leastness at MEMBERSHIP:
`IsCardinalL κ = (δ : S) → ⟨ fst δ ∈ fst κ ⟩ → (∥ Σ[ F ∈ S ] InjCode F κ δ ∥₁ → Empty.⊥)`
(`src/L/Cardinal.lagda.md:230-232`). **A refutation at the birth order does not
give one at membership**, and the tree states no equation between the two.

**THE CONTRAST IS INSIDE THE SAME MASTER AND IT IS WHAT PAYS.**
`LeastCardInjL`'s order `w` is sealed (`src/L/Cardinal.lagda.md:90-92`), and
`w-lt` is the one read that opens it:
`w-lt : (m n : ⟪ sucV (fst α) ⟫) → SWO._<∙_ w m n ≡ ⟨ ⟪ sucV (fst α) ⟫↪ m ∈ˢ ⟪ sucV (fst α) ⟫↪ n ⟩`
(`src/L/Cardinal.lagda.md:97-101`). **That comparison IS membership**, which is
why `κ-min-at` (`src/L/Cardinal.lagda.md:140-155`) can state leastness at `∈`
and why `[LJ-1.552]`'s `member-into-kappa`
(`agents/tasks/LJ-1-552/Probe552.agda:158-194`) can spend the fourth component
of `SuccCardL` against it.

I re-measured that too, as a type: `Frame.order-is-membership`
(`Probe557.agda:145-149`) is `M.w-lt` at this frame, green.

### WHAT THE TWO NOs TOGETHER SAY

They are the same module asking for two things the obligation never asks for:
a code inside a stage, and leastness in an order that is not `∈`. **Drop both
and the route closes.** Run the selection at `LeastCardInjL`'s frame,
`⟪ sucV (fst a) ⟫` under the sealed membership order `w`, and take the
predicate to be the obligation's own `∥ Σ[ F ∈ S ] InjCode F a (up γ) ∥₁`,
with `F` over the whole L-carrier. Check 1 then has nothing to ask, because no
term ever demands where the code lives; and check 2 is paid, because the
comparison is membership by `w-lt`. That is `InternalCardOf`
(`Probe557.agda:196-262`), and it is 44 lines of Agda.

**SO `[LJ-1.552]` NAMED THE RIGHT THREE MODULES AND THE WRONG FRAME FOR ONE OF
THEM.** `InclGraph` and `Comp` are used exactly as it said. `InternalLeastCard`
is not used at all; what is reused is its neighbour `LeastCardInjL`, three
fields deep (`up`, `self`/`self-eq`, `w`/`w-lt`).

## WHAT THE OBLIGATION COST

**32 Agda lines for the obligation itself** (`Probe557.agda:275-314`), on top
of `InternalCardOf`'s 44. The probe is 314 lines: 124 comment, 43 blank and
147 Agda, of which 32 are the pragma, the module header and the imports.

The shape is `[LJ-1.552]`'s `member-into-kappa` with every ambient object
replaced by a coded one, and the replacement is one-for-one:

| ambient, `[LJ-1.552]` | internal, here |
|---|---|
| `LeastCardInjL a oa` (`src/L/Cardinal.lagda.md:61`) | `InternalCardOf a oa` (`Probe557.agda:196`) |
| `card-of` + `ambient→internal` (`Probe552.agda:134-146`) | `InternalCardOf.cardL` (`Probe557.agda:257-262`) |
| `ord-emb` + `comp-inj` (`L.BoundedSubset.Devlin55`) | `incl-code` + `comp-code` (`Probe557.agda:164-184`) |
| `M.κ-inj`, an ambient injection | `M.c-code`, a truncated CODE |

**THE ONE STEP THAT IS NOT A TRANSCRIPTION IS `cardL`, AND IT IS THE STEP
CHECK 2 ASKED ABOUT.** Ambiently, `card-of` argues that a smaller target would
beat the selection by COMPOSING ambient injections. Internally the same
argument runs on CODES, and the composition is `Comp`
(`src/L/InjChain.lagda.md:314`): a code `c ↪ d` with `d ∈ c` composes with the
selected code `a ↪ c` to give a code `a ↪ d`, which `c-min-at`
(`Probe557.agda:238-255`) refutes. **No ambient counting argument appears**,
which matters because `[LJ-1.552]`'s `## WHY NO COUNTING ARGUMENT CAN REPLACE
THE CONSTRUCTION` showed the ambient counting leg cannot close.

**WHAT THE SHAPE RESISTED. Two red runs, both kept.**

1. `runs/red-1.out`, exit 42. `Σ≡Prop` is not in scope from `Base.Prelude`
   even though the Prelude re-exports `Cubical.Data.Sigma`
   (`src/Base/Prelude.lagda.md:169`). Agda's own suggestion list names
   `Cubical.Data.Sigma.Σ≡Prop`. Cure: name it in the `using` list.
2. `runs/red-2.out`, exit 42, `UnsolvedMetaVariables` at one site only,
   `Probe557.agda:308.21-46` IN THE FILE AS `red-2` RAN IT, which is five
   lines shorter than the file this report describes. `Σ≡Prop` cannot infer
   its family from a bare
   V-path when the expected type is an L-carrier path under a `subst`. Cure:
   `S-path` (`Probe557.agda:89-90`), written ONCE at top level with an
   explicit signature, and used at both sites.

`runs/red-3.out` is the first green run, exit 0, 4.59 s.

**WHAT I DID NOT HAVE TO WEAKEN.** Nothing. The obligation is the brief's type
character for character, and the witness meter derived it from the brief rather
than from my transcription (`runs/witness-1.out`), so it cannot have drifted.

**WHAT COST NOTHING, AGAINST EXPECTATION.** `[LJ-1.425]` recorded `Carve`'s
private `Small` instance as the 8g warning
(`agents/tasks/LJ-1-425/lj-1.425-report.md:75-77`). It did not fire. The
seals hold: `Carve`'s `incl`/`incl-inj` and `Comp`'s `compFun`/`compFun-inj`
are `opaque` (`src/L/InjChain.lagda.md:549-560`, `:427-433`), and no term of
this file reads them. **I also cut the module applications from four to two**:
`incl-code` is ONE application of `InclGraph` and pays both the identity code
on `a` and the ordinal inclusion `c ⊆ κ`; `comp-code` is ONE application of
`Comp` and pays both compositions. Peak memory footprint 1,232,536,992 bytes,
about 1.15 GiB, against the 8 GB cap.

## POINTWISE AGAINST UNIFORM

Three sentences, as the brief orders.

**MY POINTWISE CODE DOES NOT MAKE THE UNIFORM ASSIGNMENT CLOSER, AND THE GAP
IS EXACTLY THE `Formula` THAT `[LJ-1.554]` COULD NOT BUILD.** Every code this
file produces is produced INSIDE a proof about ONE member `a`: `InternalCardOf`
takes `a` as a module parameter, `leastOf` is applied at `a`'s own frame
`⟪ sucV (fst a) ⟫`, and the result is sealed under `∥_∥₁`, so nothing in the
file gives a function `a ↦ F a` and nothing tries to. To turn the pointwise
existence into the uniform one you must exhibit the family as a SET of L, and
`[LJ-1.552]` measured that there are exactly two generators of a set of L and
both take a `Formula` (`hasSeparationL`, `src/L/Axioms/Full.lagda.md:144`,
`Formula S 1`; `hasReplacementL`, `src/L/Axioms/Full.lagda.md:277`,
`Formula S 2`), so the step from here to the assignment is a formula and not a
choice principle. **I built neither, as the brief forbids**, and I add one
measurement to the price: the formula would now have to describe THIS
selection, `leastOf` at `w` over the code predicate, which is a quantifier over
the whole L-carrier and not over a stage.

## W3, THE WIDEST UNMEASURED TERM

**GO, AND THE SLICE IS GREEN.** `runs/W3.agda`, 97 lines, exit 0. Written
FIRST and typechecked ALONE, before any other Agda of this task. It imports no
probe.

    -- the stage InternalLeastCard selects over, at this frame, TYPE ONLY

The slice is section 1 of the probe (`Probe557.agda:98-149`): the stage
`Frame.site`, the order `Frame.sel`, the demand `Frame.Demand`, the free
bridge `Frame.bridge`, the uninhabited `Frame.Converse`, and the membership
order `Frame.memOrd` with its equation `Frame.order-is-membership`.

**THE BRIEF SAID THE STAGE WOULD SETTLE THE ESTIMATE, AND IT DID, THE OTHER
WAY.** It said "if the stage will not resolve here the rest of the estimate is
void". The stage resolves; what does not resolve is a code INSIDE it, and the
slice makes that a type rather than a sentence.

| run | wall s | peak memory footprint (bytes) |
|---|---|---|
| `runs/w3-1.out` | 1.50 | 338723656 |
| `runs/w3-2.out` | 1.46 | 338723656 |
| `runs/w3-3.out` | 1.48 | 338740040 |

Median wall **1.48 s**, against the brief's ceiling of 90 s. No heap event.

**ESTIMATE AGAINST MEASURED.** The brief said about 15 lines. **MEASURED 97
lines**, of which 41 comment, 17 blank and 39 Agda; 24 of the 39 are the
pragma, the module header and the imports, so **the Agda that answers W3 is 15
lines**. The brief's line figure was right about the answer and not about the
file.

## THE SWEEP (C-42)

My refutation is two demands of one module. C-42 asks for the COUNT of sites
that carry the shape, before any cure is priced.

**SHAPE A: an `InjCode` or graph witness demanded as `Mem (Lset β)` with `β`
from `stageBound`. COUNT IN `src/`: 2.**

| n | site | shape |
|---|---|---|
| 1 | `Canonical.Good` (`src/L/Cardinal.lagda.md:187-190`) | graph `A : Mem (Lset β)` with `svAt`/`domAt`/`injAt` |
| 2 | `InternalLeastCard.Good` (`src/L/Cardinal.lagda.md:239-240`) | `F : Mem (Lset β)` with `InjCode` |

**THIS REPRODUCES `[LJ-1.425]`'s COUNT OF 2 AND I RAN IT AGAIN RATHER THAN
QUOTE IT** (`agents/tasks/LJ-1-425/lj-1.425-report.md:154`). The grep is
`Mem (Lset β)` over `src/`, and outside `src/L/Choice/` every hit is in
`src/L/Cardinal.lagda.md`.

**SHAPE B: a `leastOf` selection whose leastness a consumer needs at `∈` but
which is taken at an order that is not membership. COUNT IN `src/`: 2, AND
THEY ARE THE SAME TWO SITES** (`src/L/Cardinal.lagda.md:195` and `:247`,
both `leastOf (orderAt β oβ)`).

I checked every other `leastOf` call site in `src/` and none carries the shape:
`src/L/Cardinal.lagda.md:117` is `leastOf w`, membership by `w-lt`;
`src/L/BoundedSubset.lagda.md:480`, `:484`, `:1115`, `:1120-1121` are at
`OrdSWO.ordSWO` (its own comment, `src/L/BoundedSubset.lagda.md:1054`);
`src/L/StageCardinal.lagda.md:351-357` is at `OrdSWO.ordSWO` and `:453-456` is
at `natOrder`, whose leastness is declared unused at
`src/L/StageCardinal.lagda.md:412`; `src/L/Hull.lagda.md:81`, `:136`, `:392`,
`:399`, `src/L/Choice/Name.lagda.md:814`, `src/L/Choice/Transversal.lagda.md:215`,
`src/L/Choice/Finite.lagda.md:1002`, `src/L/Absorption.lagda.md:82-86` and
`src/L/Ordinal/SquareLaw.lagda.md:549`, `:558`, `:814` are naming, transversal,
numeral and pairing selections, none of them consumed as a cardinal.

**THE TWO SHAPES ARE CO-LOCATED, AND THAT IS THE FINDING FOR THE NEXT BRIEF.**
One module carries both, and A3's `Canonical` carries both as well. A cure
funded against A4 alone is priced against one of two sites; a cure that moves
only the stage and leaves `orderAt` in place fixes half of one site.

## W2, ANSWERED

The brief did not state W2, and I answer it.

**EVERY TERM OF THIS FILE IS AT THE GENERIC CARRIER.** `Code`, `S-path`,
`incl-code` and `comp-code` name no cardinal, no stage and no numeral.
`InternalCardOf` is generic in ONE L-element and its ordinal certificate,
exactly as `LeastCardInjL` is (`src/L/Cardinal.lagda.md:61`), and `Frame` is
generic in the same pair. `id-code` is at an arbitrary L-element.

**THE ONE PLACE THAT IS NOT GENERIC IS `member-code-into-kappa`, AND IT MUST
NOT BE.** It spends `SuccCardL`, which is a statement about a successor
cardinal and is false without it.

**AND THE GENERALISATION THE FILE DOES MAKE IS THE POINT OF IT.**
`InternalCardOf` is not about a successor cardinal at all: it is the internal
cardinality of ANY L-element ordinal, and `cardL` says it is an internal
cardinal. `member-code-into-kappa` is that term plus one trichotomy.

## W4, ANSWERED

**NOTHING WAS RETIRED AND NOTHING SHOULD BE.** No module left `src/`, so
`dev/ARCHIVE.md` takes no row from this task.

**PRICED THE OTHER WAY, AS W4 ASKS.** Written fresh today,
`src/L/Cardinal.lagda.md`'s A4 would not be written as it is.
`InternalLeastCard` is the only module of the master whose selection is at a
stage rather than at `sucV` of its own argument, it is the only one whose
predicate bounds the code, and it has no consumer in `src/`
(`[LJ-1.425]` measured that at
`agents/tasks/LJ-1-425/lj-1.425-report.md:161-163`, and the string
`InternalLeastCard` still occurs at `src/L/Cardinal.lagda.md:235` only).
**Written fresh, A4's internal least cardinal would be `InternalCardOf`**: the
A1 frame with the code predicate. That is a proposal about a live module and
not a retirement, so it is not mine to make and I do not make it.

## RUNS AND PRICES

Every run deleted the file's own `.agdai` first, because Agda skips a file
whose content is unchanged and a run that skips measures nothing.

| run | what the file was | result |
|---|---|---|
| `runs/w3-1.out` to `w3-3.out` | the W3 slice ALONE, 97 lines | exit 0, 1.50 s, 1.46 s, 1.48 s |
| `runs/red-1.out` | the whole probe, first attempt | exit 42, `NotInScope: Σ≡Prop`, 1.48 s |
| `runs/red-2.out` | `Σ≡Prop` imported | exit 42, `UnsolvedMetaVariables` at one site, 4.46 s |
| `runs/red-3.out` | `S-path` written once | exit 0, 4.59 s, the first green run |
| `runs/final-1.out` to `final-3.out` | **the file exactly as this report describes it**, 314 lines | exit 0, 4.56 s, 4.58 s, 4.59 s |
| `runs/witness-1.out` | the declared obligation, derived from the brief | `0 UNRESOLVED of 1`, `probe_red=False` |
| `runs/witness-2.out` | the nineteen other delivered terms | `0 UNRESOLVED of 19`, `probe_red=False` |
| `runs/confirm.out` | the probe as delivered, the LAST run of all, after every edit to every document of this task | exit 0, 4.22 s |

**`runs/confirm.out` IS 0.36 s FASTER THAN THE SLOWEST `final` RUN AND THE FILE
DID NOT CHANGE BETWEEN THEM.** I report the spread rather than the best number:
the five green whole-file runs are 4.22 s, 4.56 s, 4.58 s, 4.59 s and 4.59 s,
so the price to quote is about 4.6 s and the 4.22 s is warmth and not work
removed.

**THIS FILE DEPENDS ON NO OTHER PROBE**, unlike `[LJ-1.552]`, so 4.58 s is the
whole marginal cost over the delivered tree. The W3 slice is 1.48 s of it, so
sections 2 to 4 cost 3.10 s.

**HEAP.** The largest peak memory footprint of any run is 1,232,537,016 bytes,
about 1.15 GiB, against the 8 GB cap (`runs/final-2.out`). Maximum resident set
size 1,292,255,232 bytes in `runs/final-3.out`. No heap event, no exit 251, and
no WALL.

**THE ESTIMATE, AGAINST THE MEASUREMENT.** The brief estimated about 180 lines
in the probe, of which the obligation is about 45, and for W3 about 15 lines
under 90 seconds. **MEASURED: the probe is 314 lines, of which 147 are Agda;
the obligation is 32 Agda lines and `InternalCardOf`, which the estimate did
not name, is 44; W3 is 97 lines of which 15 are the Agda that answers it, at
1.48 s.** The obligation came in UNDER its estimate and the file came in over,
because the file carries the two D-10 checks as Agda rather than as prose.

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
| `scripts/gate/check-probes.py --check` | "clean (6442 tracked files, no probe outside agents/tasks/ and no generated file)" |
| `scripts/pod/check-closure.py --check closure` | "clean (102 masters; closure, archive)" |
| `scripts/gate/check-fences.py --check` | "clean (102 masters, run threshold 3)" |
| `scripts/pod/check-spec-surface.py --check` | "clean (8 surface file(s), 201 declaration(s), 7 guarded rule home(s), 499 in-fence lines)" |
| `scripts/gate/check-rule-ids.py` | "clean (56 files, 165 lessons, 68 decisions, dev/rules.toml)" |

I did NOT run `make typecheck`. `git status --short` shows one entry, the
untracked `agents/tasks/LJ-1-557/`, so no master changed and a whole-tree
typecheck would measure nothing about this task.

**THE STANDING SIZE FIGURE, from the only admissible source
(`scripts/measure/ledger.py --brief`):** "standing 33,523 lines over 100
masters, measured from HEAD". This task changed no master, so it moves that
figure by 0.

I did not commit and did not push.

## WHAT THE NEXT BRIEF NEEDS FROM THIS ONE

1. **STEP 1 OF `[LJ-1.552]`'s ROUTE IS PAID, AND IT IS PAID WITHOUT
   `InternalLeastCard`.** The reopener it named is `Codes δ κ`
   (`agents/tasks/LJ-1-552/Probe552.agda:295-300`), whose first decomposition
   step was "an INTERNAL injection code `a ↪ κ` for each member `a` of δ".
   That is `member-code-into-kappa` and it is green.
2. **DO NOT FUND A REPAIR OF `InternalLeastCard`'s SITE BOUND FOR THIS
   PURPOSE.** `[LJ-1.425]` section 5 priced a corrected stage
   (`agents/tasks/LJ-1-425/lj-1.425-report.md:135-147`). This task shows the
   obligation does not need one, because the obligation never bounds its code.
   The repair is still owed to A3 and A4 as modules; it is not owed to this
   route.
3. **`InternalCardOf` IS REUSABLE AND HAS NO HOME.** The internal cardinality
   of any L-element ordinal, with `IsCardinalL` on it, in 44 lines over
   `LeastCardInjL`. It is what A4 would be if A4 were written fresh, and any
   later task that must produce an internal cardinal wants it. This is the
   fourth task in a row to report a reusable term with no home (`memSWO`,
   `[LJ-1.552]` item 6; `ambient→internal`, three copies in three tasks,
   `[LJ-1.552]`'s W4).
4. **WHAT `Codes δ κ` STILL NEEDS IS THE OTHER HALF, AND IT IS `[LJ-1.556]`.**
   This task delivers pointwise existence of a code into κ. `Codes` also wants
   the codes SEPARATING and it wants them as members of `powL κ`, which is
   `[LJ-1.552]`'s step 2, the square law inside L. Nothing here touches it, and
   `[LJ-1.552]` item 4 priced it as a chapter and not a task. **That price is
   unchanged by this GO.**
5. **THE POINTWISE-TO-UNIFORM GAP IS A `Formula` AND THIS TASK MADE IT NO
   SMALLER**, and the formula now has to describe a selection quantified over
   the whole L-carrier. See `## POINTWISE AGAINST UNIFORM`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: **READ, and it is why I did not price a
  pairing.** `archive/dev/LJ-dispatch-index.md:1` reads
  "# THE `LJ` DISPATCH INDEX, archived 2026-08-18".
  I opened it to check whether any retired dispatch had already attacked an
  INTERNAL least cardinal, before I wrote `InternalCardOf`. It records the
  pairing dispatches, which are `[LJ-1.552]`'s step 2 and not this task's step
  1, so it gave me nothing to reuse and nothing to contradict.
- `archive/dev/JOURNAL-archived.md`: **not used, declined.**
  `archive/dev/JOURNAL-archived.md:1` reads
  "# Archived journal: the retired route".
  It is the dated record of the retired route. My two checks are about two
  live modules of `src/L/Cardinal.lagda.md` and one live module of
  `src/L/InjChain.lagda.md`, and a retired route's journal is not evidence
  about either.
- `archive/dev/JOURNAL.md`: **not used, declined.**
  `archive/dev/JOURNAL.md:1` reads
  "# ARCHIVED 2026-08-20".
  A per-episode journal, retired three days ago. The record of this task is
  `agents/tasks/LJ-1-557/`.
- `dev/ARCHIVE.md`: **READ.** `dev/ARCHIVE.md:1` reads
  "# ARCHIVE.md: the archive registry".
  I read it to confirm where this task's files belong before I wrote any. Both
  `.agda` files of this task are under `agents/tasks/LJ-1-557/`, nothing is
  retired by this task, and the registry takes no row. My W4 answer says why
  `InternalLeastCard` is NOT a retirement proposal.
- `archive/dev/DD-archived.md`: **not used, declined.** It is the archived `DD`
  ruling series, set aside in that form under amendment A7. No row of it bears
  on which order a selection is taken at.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: **READ, and it is the source-side check that
  my `InternalCardOf` is the right object.**
  `dev/literature/devlin-II5.md:259` reads
  "Requirement: a definable well-order of L_α, used to pick the <_L-least".
  The source's picking device is the definable well-order, which is `orderAt`
  and its relatives. **My selection is NOT that device**, and the check-2
  answer says why: the object I need least is a CARDINAL, and cardinal
  leastness is at `∈`. So the source's requirement is real for the assignment
  and not for this step, which is a second reason the two steps split where
  `[LJ-1.552]` said they do.
- `dev/literature/truncation-and-selection.md`: **READ, and it is why
  `c-code` stays truncated.**
  `dev/literature/truncation-and-selection.md:68` reads
  "**The selection device is a definable well-order plus a universal guard.** The".
  The guard here is `leastOf`'s own uniqueness, which is why `Good` may be an
  `hProp` valued in a truncation and the selection still be choice-free. The
  probe carries `--safe`, imports no choice module, and the only hypothesis in
  scope is the module parameter `lem`.
- `dev/literature/digest.md`: **READ, for one line, and it bounds what this GO
  claims.** `dev/literature/digest.md:241` reads
  "surjection g : α -> J_α^A when α is closed under Gödel pairing (SZ 1.17)."
  The source's counting step is conditioned on closure under Gödel pairing.
  **Nothing in this task pays that condition**, which is why item 4 of the
  handover says the chapter price of the internal square law is unchanged by
  this GO.
- `dev/literature/terms-2026-08.md`: **not used, declined.** It is the
  terminology dossier for the owner's naming ruling. This task coins no term
  and adds no `dev/glossary.toml` entry; the Boundary forbids me choosing one.
- `dev/literature/glossary-review-2026-08.md`: **not used, declined.** It is
  the terminology review for the same ruling, and this task adds no glossary
  entry.
