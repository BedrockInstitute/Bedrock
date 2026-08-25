# LJ-1.608: ingredient (iv) at the limit, in a frame that fits under the cap

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-608/Probe608.agda`:

    rec-graph-at-infinite : <the graph of ingredient (iv)'s recursion at an
                             INFINITE member stage, as a `Formula`, both
                             directions>

Land nothing in `src/`. **The `ω`-base is done and is not yours.**

**`[LJ-1.603]` HIT THE HEAP WALL AND PARKED.** That is not a refutation and I do
not treat it as one. The obligation is unchanged and the question is still open.

**THE HEAP IS THE RISK ON THIS ONE, NOT THE DEADLINE, AND THE TWO ARE DIFFERENT.**
A heap wall is `rc 251` or Agda's own "Heap exhausted"; a deadline kill is the
coder's cap at full CPU with resident set nowhere near the caliber. **Measure and
report PEAK RSS as the primary number here**, and seconds second.

**`[LJ-1.601]` IS GO AND IT NARROWED THIS INGREDIENT TO ONE HALF.** The finite
base HAS a formula, given by the table term in its `Probe601.agda` section 2. Its
words: **"what remains unmeasured in (iv) is the recursion at infinite member
stages."**

**REUSE THE SHAPE AND THE TERM BY IMPORT.** `[LJ-1.601]` worked in `[LJ-1.597]`'s
`Graph` shape (`agents/tasks/LJ-1-597/Probe597.agda:269`): a `Formula S 2`, value
variable first and index second, both directions. **R-42 (`dev/LESSONS.md`)
measures a cross-file respelling of one object at 1.74 s against 155.02 s.**

**THIS TASK IS OUTSIDE THE CIRCLE AND THAT IS WHY IT IS QUEUED.** `[LJ-1.605]` is
a NO-GO showing that ingredient (iii), the pairing, IS the square law at the
band, which `[LJ-1.593]` had already made a corollary of B9, whose formula needs
the pairing. **Ingredient (iv) does not enter that circle**, and `[LJ-1.601]`
paid half of it without touching the pairing.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-608/Probe608.agda::rec-graph-at-infinite"]

## SCOPE (write)
- agents/tasks/LJ-1-608/Probe608.agda
- agents/tasks/LJ-1-608/lj-1.608-report.md
- agents/tasks/LJ-1-608/review-of-rec-graph-at-infinite.md
- agents/tasks/LJ-1-608/runs/

## PREMISES

1. `[LJ-1.603]` parked at the heap wall. Basis: dev/pod/transitions/2026-08.jsonl:3592
2. `[LJ-1.601]` is GO and the finite base has a formula. Basis: agents/tasks/LJ-1-601/lj-1.601-report.md:1
3. It names the remainder as the recursion at infinite member stages. Basis: agents/tasks/LJ-1-601/lj-1.601-report.md:1
4. `finite-stage-inj` is the finite base. Basis: src/L/StageCardinal.lagda.md:485
5. The `Graph` shape is `[LJ-1.597]`'s. Basis: agents/tasks/LJ-1-597/Probe597.agda:269
6. `Recursion`'s condition is the graph alone. Basis: src/L/Recursion.lagda.md:259
7. `[LJ-1.605]` is a NO-GO and puts the pairing inside a circle. Basis: agents/tasks/LJ-1-605/review-of-uniform-pairing.md:90
8. `[LJ-1.593]` made the square law a corollary of B9. Basis: agents/tasks/LJ-1-593/review-of-square-coded.md:73
9. `[LJ-1.545]` measured the heap linear in field count. Basis: agents/tasks/LJ-1-545/lj-1.545-report.md:1
10. `[LJ-1.75]` measured a trimmed telescope better than proportional. Basis: archive/dev/LJ-dispatch-index.md:142
11. R-42 rules the respelling cost. Basis: dev/LESSONS.md:4404
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

A measured formula for the finite base, a fixed shape to write the other half
in, and one parked attempt that left no report.

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE FLOOR IN RSS.** State the obligation with
a hole in the smallest import set that holds it. **Record peak RSS and seconds
and report both.** If the floor is already near the caliber, say so at once: that
is the measurement and it costs one hour.

**TRIM. `[LJ-1.75]`'S CURE IS MEASURED**, 41.6 percent cheaper for a 37.7 percent
smaller telescope (`archive/dev/LJ-dispatch-index.md:142`). **An old price at an
old tree, nothing funded against it, but the method is the method.**

**DO NOT SET `GHCRTS` YOURSELF.** Use the caliber the program sets on your pane,
one Agda process at a time, and say so.

**WRITE THE REPORT AS A SKELETON FIRST AND FILL IT AS RUNS LAND.** `[LJ-1.603]`
left nothing.

**IF THE LIMIT CASE REACHES `sq`, SAY SO AND STOP.** Five tasks have now arrived
at that parameter. **A sixth arrival would put (iv) inside the circle too**, and
that is a result the mathematician needs in the hour it lands.

**CAP EVERY TYPECHECK ON A WALL CLOCK YOU SET AND REPORT THE CAP.**

**DO NOT ATTEMPT (i), (ii), (iii) OR (v).** AD12 gives this brief one obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE FLOOR`.** Peak RSS first, seconds second, for
the empty body and for the finished term if you reach it.

**REQUIRED REPORT SECTION `## DOES (iv) REACH sq`.** Two sentences, yes or no,
with the site.

ESTIMATE: about 170 lines in the probe, of which the obligation is about 45.
BASIS: `[LJ-1.601]` did the sibling half. **The heap, not the line count, is the
risk.** Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the limit case's own index.

    -- the recursion's index at an infinite member stage, TYPE ONLY, capped

**Write it FIRST, typecheck it ALONE, cap it, and report peak RSS.** ESTIMATE:
about 12 lines, cap at two minutes.

## WHAT GO AND NO-GO EACH EARN

**A GO COMPLETES INGREDIENT (iv)** and does it from OUTSIDE the circle
`[LJ-1.605]` closed, which is the only place work is currently paying.

**A NO-GO THAT SHOWS THE LIMIT CASE REACHES `sq` PUTS (iv) INSIDE THE CIRCLE**,
and then the mathematician has one blocker and not two to take to the owner.

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
  changed_files_none = ["agents/tasks/LJ-1-608/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-608/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-608/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-608/Probe608.agda"]
  changed_files_none = ["agents/tasks/LJ-1-608/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-608/review-of-*.md"]

[[branch]]
# PARK, NOT ESCALATE. MEASURED on LJ-1.534, 2026-08-22: this row matched
# a heap wall FOUR times, exit 251 each, to attempt_max. A critic
# re-runs the same probe and re-hits the same wall, so an escalation can only
# loop. **A heap wall is a resource fact and no critic can adjudicate it.**
id = "heap-wall-park"
priority = 30
action = "park"

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
  Full entry: dev/LESSONS.md:2307
- **P-l. A statement may be ABOUT a concrete stage without dragging that stage's PRESENTATION into its type**
  **The law.** Being about a concrete position is not what costs. Naming a transparent construction in a statement's TYPE is. If the tower's stage values are `opaque` upstream, a theorem may quantify over, hypothesize about and conclude at `Sset ω` freely, because the stage is an ATOM to the elaborator and nothing unfolds. If instead the type mentions a transparent presentation, such as `⟪ sucV (...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2367
- **D-26. A well-founded key on a tower needs generation data, or it needs syntax**
  **Rule:** When a route must well-order a cumulative tower's stage, ask first what the stage's members CARRY. A stage built as the values of finitely many total operations carries its own generation data, so a well-founded key exists with NO syntax at all: the operation index, then the arguments, ordered recursively. A stage built as a definable power carries nothing: its members are sets, not c...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:1735
- **C-42. A refutation measures the site it names, and it never measures how far that site extends**
  **Rule:** A refutation is a measurement of ONE site. It says the statement there is false. **It says nothing about how many other sites carry the same false shape.** So when a refutation lands, the next action is not the cure. **It is the sweep: search the tree for the shape, and report the COUNT before you price the cure.** A cure funded against the named site is priced against a number nobody...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:3762

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev, archive/scripts, dev/ARCHIVE.md:
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 229.797)
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 226.991)
- CANDIDATE archive/dev/JOURNAL.md  (score 217.406)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 165.758)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 162.893)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 68.434)
- CANDIDATE dev/literature/digest.md  (score 53.772)
- CANDIDATE dev/literature/terms-2026-08.md  (score 52.311)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 46.648)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 39.229)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
