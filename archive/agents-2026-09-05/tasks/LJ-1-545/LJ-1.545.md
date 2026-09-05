# LJ-1.545: join the three measured families, and find out what LJ-1.534 really hit

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-545/Probe545.agda`:

    three-families-inhabited : <the union of the three telescopes>

the extra hypotheses of `[LJ-1.538]`'s nine env forms, `[LJ-1.539]`'s seven
`subK` forms and `[LJ-1.542]`'s twelve `numK` forms collected as ONE telescope,
with a witness at `KValue`'s frame. **28 fields in one value.** Land nothing in
`src/`.

**THE HEAP IS FLAT IN FIELD COUNT, AND THE LARGEST FAMILY WAS THE CHEAPEST.**
`[LJ-1.542]` measured all three at one caliber
(`agents/tasks/LJ-1-542/lj-1.542-report.md:190-206`):

| task | family | fields | seconds | peak RSS | extra hypotheses |
|---|---|---|---|---|---|
| `[LJ-1.538]` | env forms | 9 | 3.56 | 722,698,240 B | 1 |
| `[LJ-1.539]` | `subK` | 7 | 3.49 | 749,125,632 B | 1 |
| `[LJ-1.542]` | `numK` | 12 | 2.65 | 649,183,232 B | **0** |

**TWELVE FIELDS COST LESS THAN SEVEN.** Each run sits near 7.6 percent of the
8 GiB cap. **That is why this task exists**: `[LJ-1.534]` tried to collect
sixteen hypotheses at once and parked at a heap wall, and the three figures
above say the wall was NOT the field count. This task finds out what it was.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-545/Probe545.agda::three-families-inhabited"]

## SCOPE (write)
- agents/tasks/LJ-1-545/Probe545.agda
- agents/tasks/LJ-1-545/lj-1.545-report.md
- agents/tasks/LJ-1-545/review-of-three-families.md
- agents/tasks/LJ-1-545/runs/

## PREMISES

1. `[LJ-1.542]` is GO and its telescope is EMPTY. Basis: agents/tasks/LJ-1-542/lj-1.542-report.md:1
2. Its three-family table is measured at one caliber. Basis: agents/tasks/LJ-1-542/lj-1.542-report.md:190
3. It states the caveat that two figures came from other worktrees. Basis: agents/tasks/LJ-1-542/lj-1.542-report.md:208
4. `[LJ-1.538]` built the nine env forms. Basis: agents/tasks/LJ-1-538/lj-1.538-report.md:26
5. `[LJ-1.539]` built the seven `subK` forms. Basis: agents/tasks/LJ-1-539/lj-1.539-report.md:28
6. `[LJ-1.534]` is parked and delivered no report. Basis: agents/tasks/LJ-1-534/LJ-1.534.md:1
7. `KFacts` has 29 fields. Basis: src/L/Condensation.lagda.md:6079
8. `KValue` delivers a `KFacts` value at this frame. Basis: src/L/Condensation.lagda.md:7411
9. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
10. Evidence is `file:line`. Basis: AGENTS.md:41
11. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

Three probes, three families, 28 fields, all GO, all under 8 percent of the heap
cap. **What is NOT delivered is any of them in the same file as another.**

## THE REASONING

**D-10, BEFORE ANY AGDA.** Read the three predecessor probes and say at
`file:line` whether their telescopes SHARE a hypothesis, CONFLICT on one, or are
disjoint. `[LJ-1.538]` carries `ω∈σ`, `[LJ-1.539]` carries `valSub`,
`[LJ-1.542]` carries none. **If the two named hypotheses are compatible at one
frame the union is one value; if they are not, say so and stop.**

**MEASURE THE HEAP AND REPORT IT AS A NUMBER.** Use the caliber the program sets
on your pane and ONE Agda process. **Do not set `GHCRTS` yourself.** Report peak
RSS and seconds beside `[LJ-1.542]`'s three figures.

**THE POINT OF THE TASK IS THE CURVE, NOT THE VALUE.** If 28 fields cost about
what 12 did, the family-by-family method scales and `[LJ-1.512]`'s stranded
census can be finished by collection. If 28 fields blow the cap, the growth is
superlinear and the report must say between which counts it turned.

**RE-RUN THE TWO IMPORTED FIGURES IF YOU CAN DO IT INSIDE THE ESTIMATE.**
`[LJ-1.542]` flagged that it did not verify the other two worktrees' `_build`
state. **If a re-run costs more than the estimate, do not do it: say you did
not.**

**DO NOT BUILD A `TFacts` VALUE. DO NOT COLLECT A FOURTH FAMILY.** AD12 gives
this brief one obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE CURVE`.** Four rows: 7, 9, 12, 28 fields
against peak RSS. Say in one sentence whether the growth is flat, linear or
worse, and **say it only about the numbers you measured yourself.**

**REQUIRED REPORT SECTION `## WHAT THIS SAYS ABOUT LJ-1.534`.** Three sentences.
`[LJ-1.534]` parked at a heap wall collecting sixteen hypotheses. **Say whether
this task's numbers make that wall likely to be field count, or something else,
and name the something else if you can see it.** You have no report from it, so
reason from its brief and your own numbers, and say that is what you did.

ESTIMATE: about 200 lines in the probe, of which the obligation is about 40, and
under 20 seconds of Agda. BASIS: the three predecessors are 3.56, 3.49 and 2.65
seconds each. Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is whether the two named hypotheses can hold at one frame at all.

    -- ω∈σ and valSub, stated together at KValue's frame, and inhabited

**Write it FIRST and typecheck it ALONE.** If it does not typecheck, the union
is refuted before any field is collected and that is a full result. ESTIMATE:
about 20 lines, under 10 seconds.

## WHAT GO AND NO-GO EACH EARN

**A GO SAYS THE CENSUS CAN BE FINISHED BY COLLECTION**, and it unstrands
`[LJ-1.512]`, which has been parked since its own census could not be carried.

**A NO-GO NAMES THE COUNT AT WHICH THE HEAP TURNS**, which prices every
remaining family task and tells the mathematician the maximum size of a
collection brief. That is a number nobody has.

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
  changed_files_none = ["agents/tasks/LJ-1-545/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-545/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-545/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-545/Probe545.agda"]
  changed_files_none = ["agents/tasks/LJ-1-545/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-545/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 214.003)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 195.706)
- CANDIDATE archive/dev/JOURNAL.md  (score 170.956)
- CANDIDATE dev/ARCHIVE.md  (score 136.125)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 127.521)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/digest.md  (score 43.563)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 40.431)
- CANDIDATE dev/literature/devlin-II5.md  (score 36.492)
- CANDIDATE dev/literature/geology.md  (score 30.393)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 24.139)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
