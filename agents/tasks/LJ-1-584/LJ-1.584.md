# LJ-1.584: the formula for the stage-cardinality bound

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-584/Probe584.agda`:

    stage-bound-definable :
      <`[LJ-1.568]`'s `Def a b g` at `g := stage-card-upper α ordα _ α∉ω`>

that is, **a formula, with parameters in L, that describes the injection
`⟪ Lset α ⟫ ↪ ⟪ α ⟫`** (`src/L/StageCardinal.lagda.md:564-566`). Land nothing
in `src/`.

**`[LJ-1.580]` IS A NO-GO, UPHELD, AND ITS REOPENER IS THIS AND ONLY THIS.** In
its own words: **"An internal stage-cardinality bound: a formula, with
parameters in L, that describes an injection of `Lset β` into α. The tree has
the AMBIENT one... It does not have the formula."**

**AND `src/` HAS NO PRODUCER, COUNTED AND NOT ESTIMATED.** `[LJ-1.580]` grepped
`InjCode` over `src/` at today's tree and found **exactly TWO producers, both
delivering the single shape `InjCode F (sucʟ γ) γ`**
(`src/L/Absorption.lagda.md:611-614`, `src/L/CodedShift.lagda.md:40`).
**Neither is a stage bound.**

**`[LJ-1.568]` ALREADY SETTLED WHAT SUCH A PRODUCER NEEDS, AND PROVED THERE IS
NOTHING WEAKER.** `Def` (`agents/tasks/LJ-1-568/Probe568.agda:189-190`) is
sufficient by `def-restricted` (`:252-253`), and `weakest` (`:377-381`) proves
**EVERY sufficient hypothesis implies it.**

**A PREDECESSOR ON THE NEIGHBOURING TERM TIMED OUT.** `[LJ-1.572]` closed
`sys-timeout-escalate` and left no report. **Measure the floor before you prove
anything, the way `[LJ-1.559]` did**: it recorded 1.39 s warm and 4.12 s cold in
a trimmed frame and used that to rule the frame out as a cause.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-584/Probe584.agda::stage-bound-definable"]

## SCOPE (write)
- agents/tasks/LJ-1-584/Probe584.agda
- agents/tasks/LJ-1-584/lj-1.584-report.md
- agents/tasks/LJ-1-584/review-of-stage-bound-definable.md
- agents/tasks/LJ-1-584/runs/

## PREMISES

1. `[LJ-1.580]` is a NO-GO and its critic upheld it. Basis: agents/tasks/LJ-1-580/review-of-beta-into-alpha-coded.md:11
2. Its reopener is the internal stage-cardinality bound. Basis: agents/tasks/LJ-1-580/review-of-beta-into-alpha-coded.md:117
3. It counted two `InjCode` producers in `src/`, both at one shape. Basis: agents/tasks/LJ-1-580/review-of-beta-into-alpha-coded.md:103
4. `stage-card-upper` is the ambient bound. Basis: src/L/StageCardinal.lagda.md:564
5. `Def` is stated at its probe. Basis: agents/tasks/LJ-1-568/Probe568.agda:189
6. `Def` is sufficient. Basis: agents/tasks/LJ-1-568/Probe568.agda:252
7. Every sufficient hypothesis implies `Def`. Basis: agents/tasks/LJ-1-568/Probe568.agda:377
8. `InjCode` is a proposition at today's tree. Basis: agents/tasks/LJ-1-576/Probe576.agda:77
9. `hasSeparationL` takes an arbitrary formula. Basis: src/L/Axioms/Full.lagda.md:144
10. `[LJ-1.572]` closed on a timeout and left no report. Basis: agents/tasks/LJ-1-572/LJ-1.572.md:1
11. `[LJ-1.559]` measured a floor in a trimmed frame. Basis: agents/tasks/LJ-1-559/lj-1.559-report.md:1
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

An ambient stage bound proved by `∈-induction` (`src/L/StageCardinal.lagda.md:566`),
an exact characterisation of what coding it needs, and a proof that nothing
weaker will do. **No formula.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE FLOOR.** State `stage-bound-definable`
with a hole in the smallest import set that holds it, and record the typecheck
time and peak RSS. **Report both.** `[LJ-1.572]` was cut off with nothing to
show; do not be the second.

**THEN READ THE INDUCTION.** `stage-card-upper` is `∈-induction step`
(`src/L/StageCardinal.lagda.md:566`). **Say at `file:line` what `step` does**,
because the formula has to describe the SAME function, and an induction is where
a description usually breaks.

**THE PARAMETERS MAY BE ARBITRARY L-SETS AND THAT IS FREE.** `[LJ-1.568]`
records that the constants of `Formula S 3` are the L-sets themselves. **Use
that rather than trying to eliminate parameters.**

**DO NOT LOOK FOR A LEVY GRADE, A STAGE OR A SIZE BOUND.** `[LJ-1.568]` measured
that `Def` needs none of them. **If you find yourself needing one, that
contradicts a measurement and you must say so at `file:line`.**

**DO NOT ATTEMPT ROW 1 OR ROW 4 THEMSELVES.** `[LJ-1.585]` measures whether one
formula pays both. AD12 gives this brief one obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE FLOOR`.** Empty-body time and peak RSS, and
the finished term's if you get there. **Numbers you measured.**

**REQUIRED REPORT SECTION `## THE FORMULA`.** Written out, with its arity, and
how you proved it describes the injection in BOTH directions.

ESTIMATE: about 210 lines in the probe, of which the obligation is about 55.
BASIS: `[LJ-1.568]` built `Def` and its two directions at a comparable size.
**Uncertain: this is the formula four dispatches have failed to produce, and the
neighbouring attempt timed out.** Comparables are of SHAPE and nothing may be
funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is `step`, the body of the induction.

    -- stage-card-upper's `step`, re-ascribed alone, TYPE ONLY

**Write it FIRST and typecheck it ALONE.** If `step` cannot be described by a
formula, neither can the injection, and you will know in the first hour.
ESTIMATE: about 15 lines, and time it.

## WHAT GO AND NO-GO EACH EARN

**A GO IS THE SINGLE MOST VALUABLE RESULT AVAILABLE TODAY**, because
`[LJ-1.580]`'s reopener and row 4 of the bill name the same object, and one
formula would answer both.

**A NO-GO THAT SHOWS `step` IS NOT DESCRIBABLE IS A RULING**, and the owner will
hear it in the hour it lands.

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
id = "accept-failed"
priority = 14
action = "escalate"
head_slot = "coder_adversarial"

  [branch.when]
  exit_code = 1
  # DELTA KEY ADDED 2026-08-22. Without it this row matches an acceptance
  # failure that delivered NOTHING, escalates, and matches again: MEASURED on
  # LJ-1.497, four times to attempt_max in six minutes, every one exit 1 with
  # delta 0. The row exists for the LJ-1.469 case, where the obligation WAS
  # delivered (delta -1) and acceptance failed. Keep it to that case.
  obligations_delta_max = -1
  changed_files_none = ["agents/tasks/LJ-1-584/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-584/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-584/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-584/Probe584.agda"]
  changed_files_none = ["agents/tasks/LJ-1-584/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-584/review-of-*.md"]

[[branch]]
# PARK, NOT ESCALATE. MEASURED on LJ-1.534, 2026-08-22: this row matched
# a heap wall FOUR times, exit 251 each, to attempt_max. A critic
# re-runs the same probe and re-hits the same wall, so an escalation can only
# loop. **A heap wall is a resource fact and no critic can adjudicate it.**
id = "heap-wall-park"
priority = 30
action = "park_and_split"

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 208.470)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 180.435)
- CANDIDATE archive/dev/JOURNAL.md  (score 176.162)
- CANDIDATE dev/ARCHIVE.md  (score 137.982)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 123.279)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 60.563)
- CANDIDATE dev/literature/digest.md  (score 47.389)
- CANDIDATE dev/literature/geology.md  (score 46.877)
- CANDIDATE dev/literature/devlin-II5.md  (score 45.218)
- CANDIDATE dev/literature/terms-2026-08.md  (score 35.845)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
