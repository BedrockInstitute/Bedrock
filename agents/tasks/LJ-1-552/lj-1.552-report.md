# LJ-1.552 report: the assignment at the heart of GCH

## HEAD
head_slot: coder
machine: shared
verdict: NO-GO

The report was written as a skeleton before any Agda and filled as each answer
landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-552/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M8g"`, one Agda process at a time. I did not set
`GHCRTS`. No heap event. Nothing is postulated, the probe carries `--safe`,
and there is no hole. The probe is a raw `.agda` file, so it carries no
` ```agda ` fence, counts 0 in-fence lines, and the ratio bar cannot fire on
it. Nothing lands in `src/`.

## VERDICT

**NO-GO on `succ-assignment`. The obstruction is
`agents/tasks/LJ-1-552/review-of-succ-assignment.md`.**

**THE PROBE IS GREEN, EXIT 0, THREE COLD RUNS**
(`runs/final-1.out` to `runs/final-3.out`). It carries no hole and no
postulate. That is deliberate: a hole makes every reduction a claim, and green
makes each one a measurement.

The witness meter agrees both ways.
`missing exit=42 agents/tasks/LJ-1-552/Probe552.agda::succ-assignment`,
`1 UNRESOLVED of 1`, `probe_red=False` (`runs/witness-1.out`). The ten terms
the file does deliver all resolve, `0 UNRESOLVED of 10`
(`runs/witness-2.out`).

FOUR findings.

1. **W3 IS A GO ON BOTH HALVES.** Every member of δ injects into κ ambiently,
   and `SuccCardL`'s leastness clause is what pays. A choice-free picking
   well-order exists at the members of ANY set of L.
2. **THE CHOOSING IS FREE AND THE POINTWISE EXISTENCE IS THE WHOLE COST.** A
   separating family of codes with pointwise existence buys the obligation,
   and the obligation buys it back.
3. **THE ASSIGNMENT IS FREE BELOW κ AND ONLY BELOW κ**, and `sucʟ κ` is a
   member of δ, so the free part never reaches δ.
4. **THE TWO MISSING INPUTS OF `[LJ-1.549]` ARE NOT INDEPENDENT.** Building
   the assignment past κ needs a `Formula` of its own, for the same reason
   `Link` does. A brief that funds the assignment as pure mathematics and
   `Link` as pure coding has mis-split the work.

## WHAT s IS

**`s k` IS THE L-LEAST MEMBER OF `powL κ` THAT CODES THE MEMBER `k` OF δ.**
That is the D-10 answer, and I state it before the Agda below.

- **The set the value lives in** is `powL κ`, the power set of κ inside L,
  `[LJ-1.549]`'s unconditional term (`agents/tasks/LJ-1-549/Probe549.agda:121`).
  Its membership reads as `⊆ˢ κ` on the nose (`powL-sub`, `Probe549.agda:124`).
- **The term that chooses the well-order is `memSWO`**
  (`Probe552.agda:221-225`), and I built it. It is three delivered terms:
  `stageBound` (`src/L/Choice/Stage.lagda.md:366`) puts every member of a set
  of L inside one stage, `stageOrder` (`src/L/Choice/Step.lagda.md:279`)
  orders that stage, `pullOrder` (`src/L/Choice/Step.lagda.md:242`) pulls the
  order back. `leastOf` (`src/L/WellOrder/Base.lagda.md:158`) then picks.
- **THE CONSTRUCTION IS CHOICE-FREE.** The probe carries `--safe`, imports no
  choice module, and the only hypothesis in scope is the module parameter
  `lem : LEM (ℓ-suc ℓ)`, which `leastOf` takes. This matches `[LJ-1.528]`,
  which the brief named as the standard to try for
  (`agents/tasks/LJ-1-528/Probe528.agda:638-643`).
- **AND THE CODING ITSELF HAS NO PRODUCER.** `s` is not built, because the
  predicate that says "codes `k`" is not inhabited at any member past κ. That
  is the stop.

## D-10, BEFORE ANY AGDA

The brief orders the answer at `file:line` before any building, and it names
the classical argument: every member of δ has L-cardinality at most κ, so it
can be coded by a subset of κ once a well-order is chosen.

**THE CLASSICAL ARGUMENT IS CORRECT AND IT IS THREE STEPS, NOT ONE.**

1. The member `a` of δ injects into κ. **BUILT**, `member-into-kappa`
   (`Probe552.agda:158-194`), and it is where the leastness clause is spent.
2. A well-order of a subset of κ of order type `a` is chosen, IN L. **NOT
   BUILT.** Step 1 gives an AMBIENT injection, and an ambient injection turns
   the ordering into an AMBIENT subset of κ, which is not a member of
   `powL κ`.
3. The subset of κ × κ is carried down to a subset of κ by a pairing, IN L.
   **NOT BUILT.** The tree's square law is ambient at every one of its three
   exports: `sq` (`src/L/Ordinal/SquareLaw.lagda.md:685`), `via-col-square`
   (`:960`), `sq-trunc-closed` (`src/L/SquareLawClosed.lagda.md:325`).

**THE TARGET IS TRUE AND THIS IS NOT A `[LJ-1.507]`.** `[LJ-1.549]` already
priced the truth question and said so
(`agents/tasks/LJ-1-549/lj-1.549-report.md`,
`## D-10, THE SECOND ANSWER: IS THE TARGET TRUE?`). I re-read that answer
rather than repeat its work, and my steps 2 and 3 are the two ingredients it
named as missing. **The stop is a missing input and not a bad premise.**

## W3, THE WIDEST UNMEASURED TERM

**GO ON BOTH HALVES, AND THE SLICE IS GREEN.** `runs/W3.agda`, 167 lines,
exit 0, `runs/w3-1.out` to `runs/w3-3.out`. Written FIRST and typechecked
ALONE, before any other Agda of this task. It imports no probe.

The brief names one term. **IT IS TWO, AND THE SPLIT IS THE FINDING.**

**HALF 1. THE COMPARISON EXISTS.**

    member-into-kappa :
        (δ κ : S) → SuccCardL δ κ
      → (a : S) → ⟨ fst a ∈ˢ fst δ ⟩
      → ∥ ⟪ fst a ⟫ ↪ ⟪ fst κ ⟫ ∥₁

`Probe552.agda:158-194`. The route: `LeastCardInjL`
(`src/L/Cardinal.lagda.md:61`) produces the least ordinal the member's index
injects into; `card-of` (`Probe552.agda:134-138`) shows that ordinal is an
ambient cardinal; `ambient→internal` (`Probe552.agda:144-146`) makes it an
L-cardinal; `SuccCardL`'s fourth component then refutes the only bad case,
because `δ ⊆ c` and `c ⊆ a ∈ δ` give `a ∈ a`.

**IT IS NOT THE FIRST SPEND OF THE FOURTH COMPONENT AND I DO NOT REPORT IT AS
ONE.** `[LJ-1.550]`'s `site-forced`
(`agents/tasks/LJ-1-550/Probe550.agda:385-390`) applies the same clause, at a
HYPOTHESISED ambient cardinal μ, and concludes `δ ⊆ μ`. Here the cardinal is
PRODUCED from the member itself, so the conclusion is an injection.

**HALF 2. THE PICKING WELL-ORDER EXISTS, AND AT MORE THAN A STAGE.**

    memSWO : (b : S) → SWO ⟪ fst b ⟫

`Probe552.agda:221-225`. `orderAt` (`src/L/Choice/Step.lagda.md:730`) orders
the members of a STAGE. This orders the members of any set of L. Nothing in
the tree named that before, and the three terms it is made of are all
delivered.

**ESTIMATE AGAINST MEASURED.** The brief said about 25 lines and under 2
minutes. **MEASURED 167 lines and 3.41 s** (`runs/w3-1.out`). The line figure
is 6.7 times the estimate and the reason is the same one `[LJ-1.515]` and
`[LJ-1.549]` both recorded for their own W3. The 167 lines are 54 comment, 22
blank and 91 Agda, and 32 of the 91 are the pragma, the module header and the
imports. **The Agda that answers W3 is 59 lines.** The time figure is 3.41 s
against a ceiling of 120 s.

## WHAT THE OBLIGATION COST

**THE OBLIGATION IS NOT THERE, SO IT COST NOTHING AND THAT IS THE POINT.**
What the file cost is the measurement of why.

The reduction that names the residue is `Codes δ κ`
(`Probe552.agda:295-300`), and it is spent both ways:

- `codes-suffice` (`Probe552.agda:302-326`): `Codes δ κ → Assignment δ κ`.
  It is half 2 plus `leastOf`, and nothing else.
- `codes-are-the-obligation` (`Probe552.agda:331-361`):
  `Assignment δ κ → ∥ Codes δ κ ∥₁`.

**SO THE RESIDUE IS EXACTLY THE OBLIGATION AND NOT A WEAKENING OF IT.** The
reduction still buys one real thing, and the next brief needs it: **the
truncation and the ambient FUNCTION are not the obstruction.** A brief that
funds work on the choice of `s`, or on the truncation, funds nothing.

**WHAT RESISTED, AND IT WAS NOT THE MATHEMATICS.** Three red runs, all kept:

1. `runs/w3-red-1.out`. `∈sucV-elim`'s motive is `Type (ℓ-suc ℓ)` and
   `Empty.⊥` is not, so the refuted branch had to conclude in `Empty.⊥*`.
   **`[LJ-1.549]` recorded this exact red run as its item 4 and I hit it
   anyway.** A measured cure does not transfer by analogy, but a measured
   TRAP should. I record it again so the next task can grep for it.
2. `runs/w3-red-2.out`. `mem-ord`'s implicit `{A}` is not inferable from
   `IsOrd A`, so both call sites name it.
3. `runs/red-1.out`. `Ω` is `hProp (ℓ-suc ℓ)`, so a Σ over a family valued in
   `Ω` does not live in `Type (ℓ-suc ℓ)`. The cure made the code predicate
   small, `hProp ℓ`, which also drops `leastOf`'s `ℓ''` to `ℓ`.

**SECTIONS 2, 3 AND 4 TYPECHECKED ON THE FIRST ATTEMPT.** I take that as
evidence about where the cost is and not about the difficulty of the
reduction: the reduction is cheap BECAUSE everything expensive is on the far
side of `Codes`.

## WHAT LINK WOULD HAVE TO SAY

**THREE SENTENCES, AS THE BRIEF ORDERS, AND THEY ARE ABOUT THE `s` THE
RESIDUE NAMES, BECAUSE I DID NOT BUILD ONE.**

Given `s k` as "the L-least subset of κ that codes the ordinal `k`", a
`Formula S 3` for `Link` must express three things at once: that `y` is a
subset of κ which, read through a pairing on κ, is a relation; that this
relation well-orders its field with order type `x`; and that `y` is the least
such subset under the tower's own order. **Nothing in `src/FOL/` states any of
the three today**, and nothing in `src/L/Coding/` does either: the delivered
vocabulary is single membership and pair statements (`prAtL`,
`src/L/Coding/Model.lagda.md:122`; `inclFo`, `src/L/InjChain.lagda.md:445`;
`appC`, `src/L/InjChain.lagda.md:196`), plus exactly one formula that
describes a recursion, `LsetGraph` (`src/L/Coding/Sequence.lagda.md:353`),
which describes the L-hierarchy and not an order type. **So `Link` is not one
missing conjunct but three, and the first of the three is the same pairing
that step 3 of my D-10 needs**, which is why finding 4 says the two residue
components are not independent.

## THE SWEEP (C-42)

My refutation is "no delivered term produces an L-subset of κ from an ambient
injection". C-42 asks for the count of sites that carry the shape.

**THE COUNT IS FOUR, and three were already recorded.**

| site | task | what it wanted from an ambient object |
|---|---|---|
| B9, `StageCountedCoded` | `[LJ-1.533]` | a code for `⟪ Lset δ ⟫ ↪ ⟪ δ ⟫` |
| B7, the counting site | `[LJ-1.535]` | a code out of a bare Σ |
| `Link` | `[LJ-1.549]` | a formula describing an ambient assignment |
| this obligation | `[LJ-1.552]` | an L-SET out of an ambient injection |

**AND THE COUNT OF L-SET GENERATORS IS TWO, BOTH TAKING A `Formula`.**
`hasSeparationL` (`src/L/Axioms/Full.lagda.md:144`, `Formula S 1`) and
`hasReplacementL` (`src/L/Axioms/Full.lagda.md:277`, `Formula S 2`).
`hasPowerL` (`src/L/Axioms/Power.lagda.md:187`) is the first of the two at
`subFo`, so it is no third shape. The only route that takes no formula is
picking out of a set that already exists, and `codes-are-the-obligation` shows
that route needs the existence first.

**A SITE I CHECKED AND DID NOT COUNT.** `L.BoundedSubset.CodeSelect`
(`src/L/BoundedSubset.lagda.md:1099`) and `CanonCode` (`:463`) both take an
ambient `SWO ⟪ α ⟫` and deliver something canonical. Neither delivers a SET of
L: `leg2` is `⟪ M ⟫ ↪ ⟪ α ⟫`, an ambient injection, and `canonical` is a term
of the parameter type `Code`. So they are not a fifth producer.

## RUNS AND PRICES

Every run deleted the file's own `.agdai` first, because Agda skips a file
whose content is unchanged and a run that skips measures nothing.

| run | what the file was | result |
|---|---|---|
| `runs/w3-1.out` to `w3-3.out` | the W3 slice ALONE, 167 lines | exit 0, 3.41 s, 3.43 s, 3.41 s |
| `runs/final-1.out` to `final-3.out` | **the file exactly as this report describes it**, 402 lines, `Probe549` warm | exit 0, 3.88 s, 3.89 s, 3.88 s |
| `runs/baseline-549.out` | `Probe549.agda` ALONE, cold, the dependency this file adds to | exit 0, 2.52 s |
| `runs/full-with-549.out` | this file with `Probe549` ALSO cold | exit 0, 4.78 s |

**THIS FILE'S MARGINAL COST OVER ITS PREDECESSOR IS 2.26 s** (4.78 minus
2.52). 3.88 s is what a reader pays who already has `[LJ-1.549]`'s interface.

**HEAP.** The largest peak memory footprint of any run is 886,457,544 bytes,
about 845 MiB, against the 8 GB cap (`runs/full-with-549.out`). Maximum
resident set size 946,307,072 bytes in the same run. No heap event, no exit
251, and no WALL.

**THE RED RUNS ARE KEPT**, which is the method error `[LJ-1.549]` reported
against itself: `runs/w3-red-1.out`, `runs/w3-red-2.out`, `runs/red-1.out`,
each with the failing message in it. `runs/red-2.out` is the first green run
of the whole probe.

**TWO RUN FILES ARE MISNAMED AND I SAY SO RATHER THAN RENAME THEM.**
`runs/w3-red-3.out` is exit 0: it is the first GREEN run of the W3 slice, kept
under the name the edit loop gave it, and its own header line says what it
was. `runs/confirm.out` is exit 0, 3.88 s, and it is the last run of all: the
probe as delivered, after every edit to every document of this task.

**THE ESTIMATE, AGAINST THE MEASUREMENT.** The brief estimated about 200 lines
in the probe, of which the obligation is about 50, and for W3 about 25 lines
and under 2 minutes. **The probe came in at 402 lines and the obligation is
not among them.** The 402 lines are 146 comment, 53 blank and 203 Agda, and 49
of the 203 are the pragma, the module header and the imports. The brief said
its own estimate was uncertain and said why. It was right to.

## W2, ANSWERED

The brief did not state W2, and I answer it.

**EVERY TERM OF THIS FILE IS AT THE GENERIC CARRIER.** `memSWO` is stated at
an arbitrary set of L, not at `powL κ`, and that generality cost nothing:
`MemOrder` (`Probe552.agda:198`) names no cardinal, no stage and no numeral.
`Codes`, `codes-suffice` and `codes-are-the-obligation` are stated at δ and κ
with no hypothesis on either. `card-of` and `ambient→internal` are stated at
an arbitrary L-element.

**THE ONE PLACE THAT IS NOT GENERIC IS `member-into-kappa`, AND IT MUST NOT
BE.** It spends `SuccCardL`, which is a statement about a successor cardinal
and is false without it.

**AND ONE GENERALISATION I DID NOT MAKE.** `card-of` is the ambient
cardinality of an ordinal, and it is generic already, but it is written here
rather than in `src/L/Cardinal.lagda.md` beside `LeastCardInjL`, which is
where a reader would look for it. Landing it is not this task's scope, and the
brief forbids `src/`.

## W4, ANSWERED

**NOTHING WAS RETIRED AND NOTHING SHOULD BE.** No module left `src/`, so
`dev/ARCHIVE.md` takes no row from this task.

**PRICED THE OTHER WAY, AS W4 ASKS.** Written fresh today, sections 0 to 4
would be written as they are. Section 1a would NOT be rebuilt if
`ambient→internal` had a home: this file carries the third copy of that three
line term, after `agents/tasks/LJ-1-528/Probe528.agda:105-107` and
`agents/tasks/LJ-1-550/Probe550.agda:375-377`. **Three copies of one term in
three tasks is the signal W4 asks for**, and the restatement it suggests
belongs to a task that lands `ambient→internal` in `src/L/Cardinal.lagda.md`.
It is not mine to make.

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
| `scripts/gate/check-probes.py --check` | "clean (6315 tracked files, no probe outside agents/tasks/ and no generated file)" |
| `scripts/pod/check-closure.py --check closure` | "clean (102 masters; closure, archive)" |
| `scripts/gate/check-fences.py --check` | "clean (102 masters, run threshold 3)" |
| `scripts/pod/check-spec-surface.py --check` | "clean (8 surface file(s), 201 declaration(s), 7 guarded rule home(s), 499 in-fence lines)" |
| `scripts/gate/check-rule-ids.py` | "clean (56 files, 165 lessons, 68 decisions, dev/rules.toml)" |

I did NOT run `make typecheck`. `git status --short` shows one entry, the
untracked `agents/tasks/LJ-1-552/`, so no master changed and a whole-tree
typecheck would measure nothing about this task.

**THE STANDING SIZE FIGURE, from the only admissible source
(`scripts/measure/ledger.py --brief`):** "standing 33,523 lines over 100
masters, measured from HEAD". This task changed no master, so it moves that
figure by 0.

I did not commit and did not push.

## WHAT THE NEXT BRIEF NEEDS FROM THIS ONE

1. **DO NOT FUND WORK ON THE CHOICE OF `s` OR ON THE TRUNCATION.**
   `codes-suffice` and `codes-are-the-obligation` (`Probe552.agda:302-361`)
   prove the choosing is free and the residue is pointwise.
2. **THE MISSING TERM IS AN L-SET, NOT AN INJECTION.** `member-into-kappa`
   delivers the injection the classical argument asks for. The tree turns no
   ambient injection into a set of L, and there are exactly two generators of
   a set of L, both taking a `Formula`.
3. **THE ASSIGNMENT AND `Link` SHARE ONE WALL AND MUST BE PRICED TOGETHER.**
   This corrects item 3 of `[LJ-1.549]`'s own handover, which priced the
   assignment as "a mathematics task and not a coding task".
4. **THE SQUARE LAW INSIDE L IS A CHAPTER AND IT IS UNBUILT.** The tree's
   square law is ambient at all three exports. The archive records that the
   AMBIENT pairing chapter was itself an owner ruling and a large build
   (`archive/dev/JOURNAL-archived.md:1254`), so the internal one should be
   priced as a chapter and not as a task.
5. **ONE CHEAPER STEP EXISTS AND I DID NOT MEASURE IT.** An INTERNAL injection
   code `a ↪ κ` at each member of δ may be reachable from
   `InternalLeastCard` (`src/L/Cardinal.lagda.md:235`), with
   `L.InjChain.InclGraph` (`src/L/InjChain.lagda.md:575`) for non-emptiness
   and `L.InjChain.Comp` (`src/L/InjChain.lagda.md:314`) to compose down to κ.
   **I DID NOT BUILD IT AND I DO NOT CLAIM IT WORKS.** It does not close this
   obligation on its own, because item 4 still stands.
6. **`memSWO` IS REUSABLE AND HAS NO HOME.** A well-order on the members of
   any set of L, three delivered terms deep. Any later task that must pick a
   set of L out of a set of L wants it.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: **READ, and it produced evidence for
  finding on the pairing.** `archive/dev/LJ-dispatch-index.md:243` reads
  "| LJ-1.167 | The definable power at a general argument, and pairing at a general limit | GAP 2 GO AT 35, GAP 1 NO-GO | Gap 2 sat in the prior dispatch's file. Devlin leaves gap 1 as an exercise |".
  I read it because my D-10 step 3 needs a pairing, and the index is the only
  record of a dispatch that attacked pairing directly. It says the general
  limit case was a NO-GO and that the source leaves it as an exercise. That is
  a second, independent reason to price the internal square law as a chapter.
- `archive/dev/JOURNAL-archived.md`: **READ.**
  `archive/dev/JOURNAL-archived.md:1254` reads
  "cardinal chapter cannot proceed without.** **OWNER RULED 2026-08-04: option B, build the pairing".
  I read it to price item 4 of the handover. The AMBIENT pairing chapter was
  an owner ruling and a named build, not a side effect of another task. An
  internal one should be priced the same way.
- `archive/dev/JOURNAL.md`: **READ.** `archive/dev/JOURNAL.md:661` reads
  "law as `Formula K 1`, pairing at β, not a stronger one, so the fork neither".
  I read it to check whether any fork of the square law was ever stated in the
  OBJECT LANGUAGE. The line says the square law that appears there is at
  `Formula K 1` and is a pairing at β, which is the hull language and not
  `Formula S n`, so it is not a producer for this obligation.
- `dev/ARCHIVE.md`: **READ.** `dev/ARCHIVE.md:1` reads
  "# ARCHIVE.md: the archive registry".
  I read it to confirm where this task's files belong before I wrote any. All
  three `.agda` files of this task are under `agents/tasks/LJ-1-552/`, nothing
  is retired by this task, and the registry takes no row.
- `archive/dev/DD-archived.md`: **not used.** It is the archived `DD` ruling
  series, set aside in that form under amendment A7
  (`archive/dev/DD-archived.md:5` reads "in that form, under amendment A7.").
  No row of it bears on an L-set produced from an ambient injection.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: **READ, and it confirms finding 2 from the
  source side.** `dev/literature/devlin-II5.md:259` reads
  "Requirement: a definable well-order of L_α, used to pick the <_L-least".
  **That is the picking device, and my `memSWO` is it.** The digest lists it
  as a REQUIREMENT of the argument, and the tree meets that requirement
  already. So the source agrees that the picking is not the hard part.
- `dev/literature/truncation-and-selection.md`: **READ.**
  `dev/literature/truncation-and-selection.md:68` reads
  "**The selection device is a definable well-order plus a universal guard.** The".
  This is why `codes-suffice` needs no choice: the goal of the selection is a
  proposition and the guard is `leastOf`'s own uniqueness. It is also why
  `Codes` is UNTRUNCATED where the obligation is truncated, and the truncation
  is taken once, at the end of `codes-suffice`.
- `dev/literature/digest.md`: **READ, and it names the missing ingredient by
  name.** `dev/literature/digest.md:241` reads
  "surjection g : α -> J_α^A when α is closed under Gödel pairing (SZ 1.17)."
  **The source's own counting step is conditioned on closure under Gödel
  pairing.** So the pairing is not a convenience of the classical proof of
  `κ⁺ ≤ 2^κ`. It is a stated hypothesis of the counting lemma the sister
  presentation uses, which is a third reason to price it as a chapter.
- `dev/literature/terms-2026-08.md`: **READ, for one line only.**
  `dev/literature/terms-2026-08.md:37` reads
  "| 8 | square law | 平方律 | no literature under that name; the fact is 无穷基数的平方等于自身；no source uses 平方定理 for it | yes |".
  I read it to be sure that "square law" is this project's own name for the
  fact I say is missing internally, so that a reader does not search the
  literature for a chapter under that title. I coin no term and I add no
  `dev/glossary.toml` entry.
- `dev/literature/glossary-review-2026-08.md`: **not used.** It is the
  terminology review for the owner's naming ruling. This task adds no glossary
  entry and coins no term, and the Boundary forbids me choosing one.
