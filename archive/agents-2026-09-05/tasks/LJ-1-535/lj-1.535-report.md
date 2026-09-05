# LJ-1.535 report: the formula reaches the site, not the value

## HEAD
head_slot: coder
machine: shared
verdict: NO-GO

The report was written as a skeleton before any Agda and filled as each answer
landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-535/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. No heap event. Nothing is postulated. The probe is a raw `.agda`
file, so it carries no ` ```agda ` fence, counts 0 in-fence lines, and the
ratio bar cannot fire on it.

## VERDICT

**NO-GO on `stage-card-upper-coded`.** The obstruction is
`agents/tasks/LJ-1-535/review-of-stage-card-upper-coded.md`.

**THE PROBE IS GREEN, EXIT 0, SIX RUNS.**
`agents/tasks/LJ-1-535/Probe535.agda`, `runs/full-1.out` to `runs/full-3.out`
and `runs/final-1.out` to `runs/final-3.out`. `runs/final-3.out` is the state
this report describes. No hole, no postulate. Green on
purpose (the `[LJ-1.533]` discipline): a hole would make every line a claim,
green makes each one a measurement.

**THE BRIEF'S OBLIGATION HAS TWO HALVES AND THEY DO NOT LAND TOGETHER.**

1. "a Formula-carrying restatement of `stage-card-upper`'s injection":
   **BUILT AND GREEN.** `stage-card-upper-with-formula`
   (`Probe535.agda:228-232`) inhabits `StageCardUpperCodedᵀ` (`:122-133`).
2. "from which an `InjCode` is reachable": **NOT REACHABLE**, by a type
   argument.

Because half 2 fails the term does not carry the obligation's name, so the
obligation count does not move. That is the `[LJ-1.533]` shape and it is
deliberate.

## W3, AND IT RAN FIRST

**THE QUESTION.** "The `Formula` that `formula-bound` is applied to, at its
`file:line`, still in scope where the injection is formed."

**THE ANSWER, IN ONE SENTENCE. IT IS IN SCOPE AT THE SITE AND IT IS NOT IN THE
VALUE.**

**WHERE IT IS.** `formula-bound` (`src/L/StageCardinal.lagda.md:177-185`) has
domain `Formula K 1`, and at the recursive site `K = ⟪ Lset (⟪ α ⟫↪ m) ⟫`:
that is `LimitStep.F` (`:285-286`) and `cnt` (`:288-289`). The formula is bound
inside `class-pred` (`:319-323`) under `∥_∥₁`, and it is produced by `𝒟ₒ-inv`
through `nonempty`'s `toWitness` (`:325-348`).

**THE TRUNCATION IS NOT A WALL, AND THIS IS THE TASK'S ONE POSITIVE FINDING.**
At a FIXED value the witness is a PROPOSITION: `pair-inj` (`:71-75`) recovers
`m`, and `cnt-inj` (`:291-292`) recovers `φ` up to the transport `cnt-stable`
(`:294-297`). `isPropWit` (`Probe535.agda:196-214`) is that argument, and it is
the same computation `h-inj` (`src/L/StageCardinal.lagda.md:353-394`) already
runs. `SC.extract` (`:419-420`) spends `lem` once and hands the witness back
untruncated: `witness` (`Probe535.agda:221-222`).

**SO FOR EVERY MEMBER `x` OF `Lset α` THE RESTATEMENT DELIVERS**, untruncated:
`m : ⟪ α ⟫`, `φ : Formula ⟪ Lset (⟪ α ⟫↪ m) ⟫ 1`,
`defSet (Lset (⟪ α ⟫↪ m)) φ ≡ x`, and `pack m φ ≡ f x` with `pack m` injective
(`Probe535.agda:187-190`).

**WHERE IT IS NOT: THE VALUE.** `count-bound`
(`src/L/StageCardinal.lagda.md:124-129`) computes `f x` from three ingredients.

| ingredient | its type | carries a `Formula`? |
|---|---|---|
| `code ψ` | `Formula (⊥* {ℓ}) k → ℕ` (`src/FOL/Count.lagda.md:81`) | domain is the parameter-FREE shape, and `ℕ` is what leaves |
| `tuple-g g k cs` | `g : Σ[ f ∈ (K → ⟪ β ⟫) ] injective` (`src/L/StageCardinal.lagda.md:100-102`) | NO |
| `pair` | the module parameter `sq`, the same bare Σ (`:17-19`) | NO |

**AND THAT BARE Σ IS `[LJ-1.533]`'s OBJECT.** `TupleInputᵀ`
(`Probe535.agda:263-264`) is `_↪_` (`src/L/Cardinal.lagda.md:47-48`) with the
carriers renamed. `branch-is-ambient` (`Probe535.agda:269-271`) typechecks the
chapter's own `ih` AT that type, and `sq-is-ambient` (`:276-280`) does the same
for `sq`, so the identification is the elaborator's and not a sentence I wrote.

**THE WALL IS THEREFORE INSIDE THE TERM AND NOT AT THE CHAPTER'S EDGE.** Two of
the three ingredients that compute the injection's value are exactly the object
`[LJ-1.533]` refuted, and the formula I extracted does not change either one's
type.

**AND THE FORMULA IS THE WRONG KIND ANYWAY.** `hasSeparationL` takes
`Formula S 1` (`src/L/Axioms/Full.lagda.md:144`) and `hasReplacementL` takes
`Formula S 2` (`:277`), both over the L-CARRIER, each used to define ONE set.
The chapter's formula is over `⟪ Lset δ ⟫`, the members of a lower stage, and it
names ONE MEMBER of the injection's domain. **A formula per member of the domain
is not a formula for the graph**, and no term in the tree turns the first into
the second.

**COST OF W3.** 20 minutes of reading and 1.20 s of Agda under the pane's
caliber (`runs/final-2.out`). The brief estimated about 20 lines of reading and
under 30 seconds of Agda. The reading estimate held; the Agda estimate was
generous because the tree's interfaces were warm and only the probe elaborated.

## WHAT A GO WOULD HAVE NEEDED, AND WHERE THE TREE ALREADY DOES IT

**`L.Absorption` IS THE EXEMPLAR AND IT IS NOT THIS CHAPTER.** One module,
one object-language formula, two exports:

    shiftFo     : S → S → S → S → Formula S 1                 (src/L/Absorption.lagda.md:224)
    absorbs     : ... → ⟪ sucV (fst γ) ⟫ ↪ ⟪ fst γ ⟫          (:635-638)
    shift-coded : ... → ∥ Σ[ F ∈ S ] InjCode F (sucʟ γ) γ ∥₁  (:611-614)

Both come from `ShiftGraph`. **That is what "build coded at the chapter's own
site" means**, and `L.StageCardinal` has no term of the first line's shape: it
imports `Formula` (`src/L/StageCardinal.lagda.md:21`) and uses it only at
`⟪ Lset δ ⟫` and at `⊥*`.

**SO THE PRICE THE MATHEMATICIAN MUST CARRY** is an object-language formula for
the counting graph at `L.StageCardinal`'s site, written fresh. That is not a
restatement of anything delivered.

## DOES THIS SERVE B7 AND B10

Required section. **I did not build either row.**

**B7, `AbsorbsAt` (`agents/tasks/LJ-1-523/Probe523.agda:234-238`). NO DELIVERED
SHADOW AT ITS OWN SHAPE, AND IT WANTS NO CODE.** Its conclusion is
`⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫`, an AMBIENT injection.

- The tree's only term of that exact shape is a HYPOTHESIS, not a delivery:
  `(absorbs : ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫)` is a parameter of
  `BoundedSubsetAt` (`src/L/BoundedSubset.lagda.md:1392`).
- The near neighbour `absorbs` (`src/L/Absorption.lagda.md:635-638`) is a
  DIFFERENT shape, and `[LJ-1.523]` says so itself at `Probe523.agda:230-233`.
  C-42 forbids reading one as the other and I have not.
- **That neighbour IS built from a formula**, `shiftFo`
  (`src/L/Absorption.lagda.md:224`), and it already has its coded twin
  `shift-coded` (`:611-614`). **So B7's neighbourhood answers the brief's
  question YES**, and `[LJ-1.533]` was right that B7 itself meets no coding
  wall.

**B10, `SuccIntoPower` (`agents/tasks/LJ-1-523/Probe523.agda:266-269`). I DID
NOT FIND A SHADOW.** Its conclusion is `InjL δ (𝒫 κ)`. The only occurrences of
that shape in `src/` are the trophy statement's own conjuncts,
`src/L/GCH.lagda.md:67-68`, which are goals and not shadows. `[LJ-1.523]`'s own
note says the bounded-subset theorem "says nothing about it: it is not on this
bridge at all" (`Probe523.agda:264-265`). **So B10 has no formula to inherit and
no shadow to restate: it is an unbuilt leg, not a blocked one.**

**THE ARITHMETIC THE BRIEF ASKED FOR.** A GO would have turned six unpaid inputs
into three. It does not. What the NO-GO settles instead: **B9 needs one new
object-language formula; B7 needs none, because its neighbour already has one;
B10 needs a proof that nobody has started.** That is three different prices, not
one.

## WHAT MY TERM STILL OWES `[LJ-1.524]`, `[LJ-1.529]` AND `[LJ-1.531]`

Those three are building `InjCode`'s conjuncts over a different carve, and
AD12 gives this brief one obligation, so I built none of them.

**MY TERM OWES THEM EVERYTHING THEY ARE BUILDING, AND ONE THING MORE.**
`InjCode F a b` (`src/L/Cardinal.lagda.md:223-229`) needs an L-ELEMENT `F`
before any conjunct can be stated at it. `stage-card-upper-with-formula`
produces no L-element: it produces a function `⟪ Lset α ⟫ → ⟪ α ⟫`, a counting
map, and a per-member formula. **So the conjunct work of `[LJ-1.524]`,
`[LJ-1.529]` and `[LJ-1.531]` cannot consume my term as it stands.** It needs
the graph set first, and the graph set needs the formula this report prices.

## WHAT I DID NOT DO

- I did not inhabit `stage-card-upper-coded`, at any type.
- I did not rebuild `stage-card-upper`. It is INSTANTIATED at
  `Probe535.agda:144-146` and used as the induction hypothesis of the chapter's
  own `Upper.branch` at `:153-154` and `:177-178`.
- I did not build `InjCode`, and I did not weaken it.
- I did not build B7 or B10.
- I did not postulate, and I added no axiom and no `src/` change.
- **I did not prove that my restatement's `f` is the delivered
  `stage-card-upper α` on the nose.** It is ONE union step of the chapter's own
  `Upper.step` over the delivered theorem at the members of `α`. Proving the
  identity needs `∈-induction` to unfold and the tree gives no lemma for it. I
  priced nothing against such an identity, and the probe says so at
  `Probe535.agda:234-239`.
- I did not measure whether the internal-syntax tower under `src/L/Coding/`
  could render the counting graph. That is a real question and it is the
  mathematician's, not a coder's: `src/L/Coding/Sat.lagda.md:8` says of its own
  chapter "Nothing here is internal."

## THE NUMBERS

| item | estimate | measured |
|---|---|---|
| probe, total | about 190 lines | 307 lines, 112 non-blank non-comment |
| the obligation-shaped term | about 55 lines | 49 non-blank (`Probe535.agda:175-232`), of which `isPropWit` is 19 |
| W3 | about 20 lines read, under 30 s Agda | held for the reading; 1.20 s Agda |
| typecheck | not estimated | 1.20 to 1.24 s, peak RSS 374 MB (`runs/full-2.out`) |

The typecheck figures are the probe alone with the tree's interfaces warm. They
are not a chapter price and must not be quoted as one.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: **READ AND USED.** `:190` is
  "| LJ-1.114 | Thread the truncation from StageCardinal to Devlin55 | WALL, ROUTE-LEVEL | Upper's h-inj needs ONE honest injection; two truncation eliminations collide. Reverted; the cause is proved |".
  That is the warning I designed against: `witness` performs exactly ONE
  elimination, at a FIXED value where the witness is a proposition, so no second
  elimination collides with it. `:379` is
  "| LJ-1.324 | Transplant stage-card-upper | REFUTED, THE FIRST INGREDIENT IS THE GOAL. DD25 review not needed: it closes a lead and funds nothing | The generic engine survives, tower-blind |",
  a prior refusal at this same term, and it is why I restated rather than
  transplanted.
- `archive/dev/JOURNAL-archived.md`: **DECLINED.** `:1` is
  "# Archived journal: the retired route". B9 is on the live route. Not used.
- `archive/dev/JOURNAL.md`: **DECLINED.** `:1` is "# ARCHIVED 2026-08-20". The
  per-episode journal is retired in favour of `agents/tasks/<CODE>/`, and the
  predecessor evidence this task needed was in those task directories. Not used.
- `dev/ARCHIVE.md`: **DECLINED.** `:1` is "# ARCHIVE.md: the archive registry".
  It is the registry of retired MODULES. This task retires none. Not used.
- `archive/dev/DECISIONS-archived.md`: **DECLINED.** `:1` is
  "# Archived decisions: the D series". A bare `D<n>` is not a rule in force.
  Not used.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`: **READ AND USED.** `:143` is
  "the reason: \"a proposition-valued goal absorbs the truncation\"". That is
  the law behind the task's one positive finding: `isPropWit` makes the witness
  proposition-valued at a fixed value, and `SC.extract` then absorbs the
  truncation `class-pred` carries.
- `dev/literature/devlin-II5.md`: **READ AND USED.** `:1` is
  "# Devlin II.5: the Condensation Lemma and the GCH in L". It is the source of
  the counting leg this chapter discharges, and I read it to confirm that the
  source states a CARDINALITY fact and offers no coded injection to inherit. It
  gives B9 no formula.
- `dev/literature/terms-2026-08.md`: **DECLINED.** `:1` is
  "# The terminology dossier: fourteen renderings for the owner's ruling". This
  report names no new term and adds no glossary entry. Not used.
- `dev/literature/digest.md`: **DECLINED.** `:1` is
  "# Digest: the orthodox form of the rud route, pinned from the collected literature".
  B9 sits on the `Def` tower's counting leg and no claim here turns on a rud
  fact. Not used.
- `dev/literature/geology.md`: **DECLINED.** `:1` is
  "# Geology dossier: set-theoretic geology sources and the five questions".
  Nothing in this task touches grounds or mantles. Not used.
