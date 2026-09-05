# LJ-1.435: the limit step from a POINTWISE truncated branch family

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-435/Probe435.agda`:

    limit-step-trunc :
        (α : S) → ⟨ α ∈ˢ sucV α₀ ⟩ → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
      → ((m : ⟪ α ⟫) → ∥ ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫ ∥₁)
      → ∥ ⟪ Lset α ⟫ ↪ ⟪ α ⟫ ∥₁

It is the chapter's `limit-step` (`src/L/StageCardinal.lagda.md:396-400`) with
the branch family truncated POINTWISE and the conclusion truncated once.

**THE PAIRING STAYS DATA.** It is the module's own `sq α α∈suc infα`
(`src/L/StageCardinal.lagda.md:283`), exactly as the chapter has it. This task
does not truncate the pairing and it must not.

**WHAT MOVES, AND IT IS ONE THING.** The branch witness moves INSIDE the class
predicate (`src/L/StageCardinal.lagda.md:319-323`), which is already an hProp
under `∥ ∥₁`, so the least-value selection at `:350-351` still runs.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-435/Probe435.agda::limit-step-trunc"]

## SCOPE (write)
- agents/tasks/LJ-1-435/Probe435.agda
- agents/tasks/LJ-1-435/lj-1.435-report.md
- agents/tasks/LJ-1-435/review-of-limit-step-trunc.md

## PREMISES
- The limit step takes the branch family as DATA and returns an injection as data. Basis: src/L/StageCardinal.lagda.md:396
- Inside it, the family is read ONLY to build a count of formulas and that count's injectivity. Basis: src/L/StageCardinal.lagda.md:288
- The count's injectivity is the second projection of the same bound. Basis: src/L/StageCardinal.lagda.md:291
- The class predicate is ALREADY a truncation and it is an hProp by `squash₁`. Basis: src/L/StageCardinal.lagda.md:319
- The value is the least member of that class, selected by `leastOf` over the ordinal own well-order. Basis: src/L/StageCardinal.lagda.md:351
- Injectivity of the value opens the class predicate TWICE and compares two witnesses. Basis: src/L/StageCardinal.lagda.md:353
- That comparison splits the packed value with the pairing's injectivity. Basis: src/L/StageCardinal.lagda.md:382
- It then closes with the count's injectivity at ONE stage index. Basis: src/L/StageCardinal.lagda.md:390
- The chapter's own comment says no transport coherence of the branch family is needed. Basis: src/L/StageCardinal.lagda.md:275
- `[LJ-1.408]` REFUTED moving the PAIRING inside that same truncation, and the refutation is green. Basis: agents/tasks/LJ-1-408/Probe408.agda:95
- Its reason was that two readings of the truncation may take two different pairings. Basis: agents/tasks/LJ-1-408/lj-1.408-report.md:26
- The pairing is a Sigma, so a second inhabitant exists whenever one does. Basis: src/L/Ordinal/SquareLaw.lagda.md:685
- THE ARCHIVE RECORDS A TRUNCATION WALL OF THIS SHAPE, AND A CURE: the least-witness pattern absorbed a truncated membership into a proposition-valued goal. Basis: archive/dev/JOURNAL-archived.md:1433
- The same entry names that wall on a descent and says the cure came from a re-home probe. Basis: archive/dev/JOURNAL-archived.md:1442
- A truncated square law at initial ordinals was DELIVERED on the retired route. Basis: archive/dev/TASKS-archived.md:82
- The architecture is a CANDIDATE and only a measurement settles it. Basis: dev/pod/screen.toml:10

## WHAT IS DELIVERED ALREADY

**THE UNTRUNCATED LIMIT STEP.** `LimitStep.h` and `LimitStep.h-inj`
(`src/L/StageCardinal.lagda.md:350-393`) are green in the tree, and `limit-step`
(`:396-400`) is their packaging.

**THE DEVICE THAT UNTRUNCATES.** `h` is a `leastOf` over an hProp
(`src/L/StageCardinal.lagda.md:350-351`), which is how the chapter already turns
a truncated class into a value. Nothing new is needed for `h` itself.

**A DELIVERED REFUTATION OF THE NEIGHBOURING MOVE.** `[LJ-1.408]` proved that
the PAIRING may not move into this truncation, and left the obligation as a
hole by design (`agents/tasks/LJ-1-408/Probe408.agda:64`). **This task moves a
DIFFERENT object into the same truncation, so C-42 applies: that refutation
measures the pairing's site and it does not measure this one.**

## WHAT IS MISSING

**THE ONE PLACE WHERE A POINTWISE TRUNCATION COULD BE ABSORBED, AND NOBODY HAS
TRIED IT.** `[LJ-1.407]` delivers the square law as a FAMILY OF TRUNCATIONS. Any
induction that consumes it pointwise hits the same shape one level up: the branch
family is a Pi over `⟪ α ⟫`, and a Pi of truncations is not a truncated Pi.

**BUT THE LIMIT STEP DOES NOT NEED THE FAMILY AS A FAMILY.** It reads `ih m` at
ONE index inside a truncation that is already there (`:319-323`), and its
injectivity proof compares two witnesses that already carry their own `m₁` and
`m₂` (`:368-378`). So the branch witness can be carried in the witness, beside
`m` and `φ`, without changing the shape of the predicate.

**WHAT IS AT RISK IS INJECTIVITY AND ONLY INJECTIVITY.** With the witness
carrying its own injection, `h-inj` compares `cnt` values built from TWO possibly
different injections `g₁` and `g₂`, and the chapter step at `:379-390` uses
`cnt-inj` at ONE injection. **That is the term this task measures.**

## THE REASONING

**D-10, BEFORE ANY AGDA.** Write in the report, at `file:line`, every use of the
`ih` parameter inside `module LimitStep`, and for each one say whether it sits
under the class predicate's truncation or outside it. **There are two uses and
you must find both.** If the two are not `cnt` and `cnt-inj`, say what you found
instead and stop.

**STEP ONE, W3, THE VALUE.** See below. Typecheck it ALONE.

**STEP TWO, THE OBLIGATION.** Only if step one closes. Carry the injection in
the class predicate's witness:

    class-pred' : (x : ⟪ Lset α ⟫) → ⟪ α ⟫ → hProp (ℓ-suc ℓ)
    class-pred' x y = ( ∥ Σ[ m ∈ ⟪ α ⟫ ] Σ[ g ∈ (⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫) ]
                          Σ[ φ ∈ F m ]
                          ( ( D (⟪ α ⟫↪ m) φ ≡ ⟪ Lset α ⟫↪ x )
                          × ( B.pair m (cnt-of g φ) ≡ y ) ) ∥₁
                      , squash₁ )

with `cnt-of g = fst (B.formula-bound g)` and `cnt-of-inj g = snd (B.formula-bound g)`.
Rebuild the nonemptiness from `Lset-out` and the pointwise truncated family, as
the chapter does at `:325-345`. Then build `h'`, then `h'-inj`, then wrap the
pair in `∣ ∣₁`.

**A REQUIRED REPORT SECTION, `## WHERE TWO WITNESSES MEET`.** State, as a type,
what `h'-inj` needs when the two opened witnesses carry `g₁` and `g₂`. **Name at
`file:line` the chapter's step that assumes one injection**, and say whether the
tree delivers the cross form. **Do not assert the cross form is false unless you
refute it in Agda**, and if you do refute it, name the refutation and follow
`[LJ-1.408]`'s shape (`agents/tasks/LJ-1-408/Probe408.agda:95-104`).

**THE ARCHIVE HAS THE SHAPE AND YOU MUST RE-MEASURE IT.**
`archive/dev/JOURNAL-archived.md:1430-1443` records a truncation wall on a
descent, cured by the least-witness pattern which absorbs a truncated membership
into a proposition-valued goal. **That is a comparable of SHAPE and nothing may
be funded against it.** A measured cure does not transfer by analogy: read the
entry, name in `## ARCHIVE USED` what the cure absorbed there, and say in one
line whether the object it absorbed was a MEMBERSHIP (an hProp already) or a
FUNCTION. **The object this task must absorb is an injection, which is not an
hProp**, and that difference is the whole risk.

**W2 (DD4).** Generic in `α`. Do not fix a band ordinal and do not add an
infiniteness hypothesis the chapter does not have.

**DO NOT EDIT `src/`.** Rebuild what you need inside the probe, or import the
chapter and use `limit-step`, `Bound`, `OrdSWO` and `fin-inj` from it. Do not
weaken the conclusion below `∥ ⟪ Lset α ⟫ ↪ ⟪ α ⟫ ∥₁`.

**W3, THE WIDEST UNMEASURED TERM.**

    h-trunc :
        (α : S) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩) (oα : IsOrd α)
        (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
      → ((m : ⟪ α ⟫) → ∥ ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫ ∥₁)
      → ⟪ Lset α ⟫ → ⟪ α ⟫

**THE PROBE.** Typecheck `h-trunc` ALONE, with the obligation omitted, before
anything else. It is the VALUE half with no injectivity: the least member of
`class-pred'`. **If the value half does not close, the injectivity half is not
worth writing and the task is a NO-GO at once.** Report wall seconds and peak RSS
at the caliber the program set on your pane, one Agda process, three forced
rechecks, and the median. Quote the elaborator at `file:line`. A heap event is a
WALL event: report it and stop.

ESTIMATE for the Agda: about 110 code lines. BASIS:
`src/L/StageCardinal.lagda.md:277-393` is `module LimitStep` in 117 lines, and
this probe restates it with one extra component in the witness. **Comparables of
SHAPE and never of size, and nothing may be funded against them.**

## WHAT GO AND NO-GO EACH EARN

**A GO IS THE ONE MOVE THAT MAKES THE TRUNCATED ROUTE POSSIBLE.** It says the
limit step absorbs a pointwise truncated branch family, and the induction above
it can then run at a truncated motive with no choice principle. Say plainly that
this task closes the STEP and not the INDUCTION.

**A NO-GO IS WORTH AS MUCH AND IT IS THE SECOND HALF OF `[LJ-1.408]`.** It names
the cross-injectivity the chapter's counting needs, as a type, and it says the
branch witness is as unmovable as the pairing. That closes the truncated route at
its one candidate site and hands `[LJ-2.5]` a measured reason.

## BRANCHES
```toml pod-branches
[[branch]]
id = "go"
priority = 10
action = "done"
outcome = "go"

  [branch.when]
  exit_code = 0
  obligations_delta_max = -1
  heap_wall = false

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-435/Probe435.agda"]
  changed_files_none = ["agents/tasks/LJ-1-435/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-435/review-of-*.md"]

[[branch]]
id = "heap-wall-escalate"
priority = 30
action = "escalate"
head_slot = "coder_adversarial"

  [branch.when]
  heap_wall = true

[[branch]]
id = "ran-long-and-changed-little"
priority = 50
action = "park"

  [branch.when]
  seconds_min = 3600.0
  changed_files_count_max = 1
```

## YOUR ROLE (program-generated, do not edit)

**You write the Agda this brief names, and the probe it names (A21).** The mathematician specifies; you build it and make it typecheck. Your report is the other half of that channel, so write what the next brief will need.

**THE RATIO BAR IS LIVE AND IT IS 0.0123 SECONDS PER IN-FENCE LINE.** A green return at or above that rate is ESCALATED to a critic by row `sys-dd24-ratio-bar`, which is DD24 restored by amendment A10. The divisor is fact 7, the in-fence line count of THIS task's write scope, counted the ledger's way: non-blank lines inside ` ```agda ` fences. **A raw `.agda` probe carries no fence and counts 0**, so the bar cannot fire on a probe and it binds the moment you write a `.lagda.md` master under `src/`. Design for it rather than discovering it: the number comes from `dev/pod/table.toml` at brief build, and its measured basis is in `dev/ledger.toml [ratio]`.

## LAWS (program-generated, do not edit)

MANDATORY for kind `recon` (read-only: an audit, a design pass, a history dig. It writes a report and nothing else. The sweep C-42 demands is a recon action, so this is that law's home bundle.):

- **D-10. Price the truth of a recorded residue before pricing its proof**
  **Rule:** A residue recorded under the wall protocol names a TARGET, and a target can be false; before dispatching a discharge batch, spend the five minutes checking the target's truth at the intended generality (a Tarskian or cardinality obstruction is the usual killer), and record the corrected target beside the original.
  Full entry: dev/LESSONS.md:1375
- **C-22. A dispatched agent writes its deliverable incrementally, never at the end**
  **Rule:** When an agent's deliverable is a file, the brief must require it WRITTEN EARLY as a skeleton and filled incrementally, saving after each answer lands. An agent that researches for its whole budget and leaves the writing to the end returns nothing when the budget runs out, and its research dies with it. A partial dossier is a real deliverable; an unwritten perfect one is not.
  Full entry: dev/LESSONS.md:2297
- **P-l. A statement may be ABOUT a concrete stage without dragging that stage's PRESENTATION into its type**
  **The law.** Being about a concrete position is not what costs. Naming a transparent construction in a statement's TYPE is. If the tower's stage values are `opaque` upstream, a theorem may quantify over, hypothesize about and conclude at `Sset ω` freely, because the stage is an ATOM to the elaborator and nothing unfolds. If instead the type mentions a transparent presentation, such as `⟪ sucV (...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2357
- **D-26. A well-founded key on a tower needs generation data, or it needs syntax**
  **Rule:** When a route must well-order a cumulative tower's stage, ask first what the stage's members CARRY. A stage built as the values of finitely many total operations carries its own generation data, so a well-founded key exists with NO syntax at all: the operation index, then the arguments, ordered recursively. A stage built as a definable power carries nothing: its members are sets, not c...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:1735
- **C-42. A refutation measures the site it names, and it never measures how far that site extends**
  **Rule:** A refutation is a measurement of ONE site. It says the statement there is false. **It says nothing about how many other sites carry the same false shape.** So when a refutation lands, the next action is not the cure. **It is the sweep: search the tree for the shape, and report the COUNT before you price the cure.** A cure funded against the named site is priced against a number nobody...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:3752

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev, archive/scripts, dev/ARCHIVE.md:
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 159.796)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 138.476)
- CANDIDATE dev/ARCHIVE.md  (score 126.414)
- CANDIDATE archive/dev/JOURNAL.md  (score 122.950)
- CANDIDATE archive/dev/DD-archived.md  (score 100.723)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 84.669)
- CANDIDATE dev/literature/devlin-II5.md  (score 50.926)
- CANDIDATE dev/literature/digest.md  (score 37.368)
- CANDIDATE dev/literature/terms-2026-08.md  (score 35.531)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 31.036)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
