# LJ-1.579: StageHigh once more, in a frame that fits under the cap

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-579/Probe579.agda`:

    stage-high : <the statement `[LJ-1.536]` carried>
      (`agents/tasks/LJ-1-536/Probe536.agda:350-352`)

Land nothing in `src/`.

**`[LJ-1.565]` HIT THE HEAP WALL AND PARKED.** Its row is
`task-lj-1-565-heap-wall-park`. **That is not a refutation and I do not treat it
as one.** The question it was sent to answer is still open.

**AND THE QUESTION IS SHARPER THAN IT WAS.** `[LJ-1.562]` is GO and measured
that **BOTH of `AtStage`'s hypotheses are payable at the formula `[LJ-1.536]`
actually needed**: the formula is Δ₀ by two constructors, and `[LJ-1.536]` had
already typechecked the witness at its own `runs/W3.agda:156-157` and never
reported it. **So the door is not what blocks `StageHigh`.**

**THE HEAP IS THE RISK AND IT IS MEASURABLE.** `[LJ-1.545]` measured the heap
LINEAR in field count at one caliber, 28 fields at 12.46 percent of the 8 GiB
cap (`agents/tasks/LJ-1-545/lj-1.545-report.md`, `## THE CURVE`). `[LJ-1.559]`
measured a floor of 1.39 s warm and 4.12 s cold in a TRIMMED frame and used that
to rule the frame out as a cause of two timeouts. **Do the same here: measure
the floor before you prove anything.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-579/Probe579.agda::stage-high"]

## SCOPE (write)
- agents/tasks/LJ-1-579/Probe579.agda
- agents/tasks/LJ-1-579/lj-1.579-report.md
- agents/tasks/LJ-1-579/review-of-stage-high.md
- agents/tasks/LJ-1-579/runs/

## PREMISES

1. `[LJ-1.565]` parked at the heap wall. Basis: dev/pod/transitions/2026-08.jsonl:3169
2. `[LJ-1.536]`'s obligation is stated at its probe. Basis: agents/tasks/LJ-1-536/Probe536.agda:350
3. `[LJ-1.562]` is GO and both door hypotheses are payable. Basis: agents/tasks/LJ-1-562/lj-1.562-report.md:1
4. The Δ₀ witness is typechecked in `[LJ-1.536]`'s own runs. Basis: agents/tasks/LJ-1-536/runs/W3.agda:156
5. `𝒟ₒ-intro` is the one route into a stage. Basis: src/L/Constructible.lagda.md:301
6. `AtStage` is the one external-to-inner bridge. Basis: src/L/Axioms/Separation.lagda.md:119
7. `[LJ-1.545]` measured the heap linear in field count. Basis: agents/tasks/LJ-1-545/lj-1.545-report.md:1
8. `[LJ-1.559]` measured a floor in a trimmed frame. Basis: agents/tasks/LJ-1-559/lj-1.559-report.md:1
9. `[LJ-1.75]` measured a trimmed telescope better than proportional. Basis: archive/dev/LJ-dispatch-index.md:142
10. `[LJ-1.541]` and `[LJ-1.547]` left nothing when they timed out. Basis: dev/pod/transitions/2026-08.jsonl:2996
11. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
12. A stop is a deliverable. Basis: AGENTS.md:43
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

`[LJ-1.536]`'s probe, its `runs/W3.agda` with an unreported Δ₀ witness, and a
measurement that the door is payable. **Three attempts and no term.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE FLOOR.** Write the smallest import set
under which `stage-high` can be STATED, and record its typecheck time and peak
RSS on an empty body. **Report both numbers.** If the floor is already near the
cap, the obligation cannot be met in this frame and you say so at once.

**TRIM. `[LJ-1.75]`'S CURE IS MEASURED**: each partial gets only the facts its
rows use, 41.6 percent cheaper for a 37.7 percent smaller telescope
(`archive/dev/LJ-dispatch-index.md:142`). **That is an old price at an old tree
and nothing may be funded against it**, but the method is the method.

**WRITE THE REPORT AS A SKELETON FIRST AND FILL IT AS RUNS LAND.** `[LJ-1.541]`
and `[LJ-1.547]` left nothing at all, including a seven-file bisection.
**`[LJ-1.565]` left a park and no report. Do not be the fourth.**

**DO NOT SET `GHCRTS` YOURSELF.** Use the caliber the program sets on your pane,
one Agda process at a time, and say so.

**IF THE REAL BLOCKER IS AN UNBOUNDED SEARCH, SAY SO AND STOP.** `[LJ-1.560]` is
GO and its reflection step was an instantiation of something already in the
tree (`agents/tasks/LJ-1-560/Probe560.agda:165-176`). **Try it here: nobody
has.**

**DO NOT BUILD A REFLECTION PRINCIPLE FROM SCRATCH.** AD12 gives this brief one
obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE FLOOR`.** Empty-body time and peak RSS,
finished-term time and peak RSS if you get there. **Numbers you measured.**

**REQUIRED REPORT SECTION `## WHAT ACTUALLY BLOCKED IT`.** One paragraph with
`file:line`, now that the door is known payable.

ESTIMATE: about 170 lines in the probe, of which the obligation is about 40.
**The heap, not the line count, is the risk, and that is why the floor comes
first.** Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the floor itself.

    -- stage-high, STATED with a hole, in the trimmed frame, timed and sized

**Write it FIRST and measure it.** ESTIMATE: about 15 lines; the numbers are
what you are measuring and I do not estimate them.

## WHAT GO AND NO-GO EACH EARN

**A GO UNSTICKS THE CONDENSATION LEG'S ROW SIX** after four attempts.

**A NO-GO THAT REPORTS THE FLOOR IS STILL A RESULT**, because no number exists
for what this term costs and three dispatches have now been spent without one.

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
  changed_files_none = ["agents/tasks/LJ-1-579/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-579/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-579/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-579/Probe579.agda"]
  changed_files_none = ["agents/tasks/LJ-1-579/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-579/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 207.665)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 205.917)
- CANDIDATE archive/dev/JOURNAL.md  (score 174.679)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 161.956)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 152.868)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 43.339)
- CANDIDATE dev/literature/digest.md  (score 39.271)
- CANDIDATE dev/literature/devlin-II5.md  (score 38.098)
- CANDIDATE dev/literature/geology.md  (score 37.281)
- CANDIDATE dev/literature/terms-2026-08.md  (score 32.275)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
