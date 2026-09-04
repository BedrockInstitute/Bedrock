# LJ-1.746-SPLIT-SPLIT: graph-mirror, the green spelling packaged

## HEAD
head_slot: coder
machine: shared
agda_tier: wide

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-746-SPLIT-SPLIT/Probe746SplitSplit.agda`:

    graph-mirror :
        StepKilledGen → ApproxSlot × StepSlot

`StepKilledGen` is `agents/tasks/LJ-1-746-SPLIT/runs/Amb7.agda:55-62`. `ApproxSlot` and `StepSlot` are `agents/tasks/LJ-1-746-SPLIT/runs/PT.agda:63-69`. The body is `approx-split gen , step-split gen` (`PT.agda:72-82`). Import `LJ-1-746-SPLIT.runs.PT`. Do not rebuild `PT`, `Amb7`, or `EraseIrr`. Do not inhabit `GraphAt`. Do not inhabit `bound-in-stage-at-empty`. Do not inhabit `Completeness`. Do not inhabit `completeness-from-pack`. Land nothing in `src/`.

ONE Agda process at a time, pane caliber. Floor first. Stay wide. Do not retry the `GraphAt` assembly in any spelling. Do not retry a reading-level `≡` conversion against `CntS.erase` of the graph or matrix.

**NAME ANY FILE THAT CANNOT TYPECHECK `.agda.txt`, NEVER `.agda`.**

**BEFORE YOU RETURN, RUN `.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-746-SPLIT-SPLIT` AND PASTE ITS OUTPUT.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-746-SPLIT-SPLIT/Probe746SplitSplit.agda::graph-mirror"]

## SCOPE (write)
- agents/tasks/LJ-1-746-SPLIT-SPLIT/Probe746SplitSplit.agda
- agents/tasks/LJ-1-746-SPLIT-SPLIT/lj-1.746-SPLIT-SPLIT-report.md
- agents/tasks/LJ-1-746-SPLIT-SPLIT/review-of-graph-mirror.md
- agents/tasks/LJ-1-746-SPLIT-SPLIT/runs/

## PREMISES

1. **`[LJ-1.746-SPLIT]` DID NOT INHABIT `bound-in-stage-at-empty`.** Candidate 1's spelling module is green. The assembly is fatal. Basis: agents/tasks/LJ-1-746-SPLIT/lj-1.746-SPLIT-report.md:11
2. **`PT.agda` IS GREEN.** Import it. Do not rebuild it. Basis: agents/tasks/LJ-1-746-SPLIT/lj-1.746-SPLIT-report.md:28
3. **DO NOT RETRY THE `GraphAt` ASSEMBLY.** Identical spellings die. Basis: agents/tasks/LJ-1-746-SPLIT/lj-1.746-SPLIT-report.md:123
4. **D-10: THE EMPTY INSTANCE IS STILL TRUE.** The wall is elaboration, not a false target. Basis: agents/tasks/LJ-1-732/lj-1.732-report.md:126
5. **DO NOT INHABIT `bound-in-stage-at-empty`.** The chain behind that name is closed at wide. Basis: agents/tasks/LJ-1-746-SPLIT/lj-1.746-SPLIT-report.md:88

## MEASURED TODAY

- dependents: L.Hierarchy => 7
- supply: graph-mirror => 0

## WHAT IS DELIVERED ALREADY

`PT.agda`: `ApproxSlot`, `StepSlot`, `approx-split`, `step-split`. This obligation has supply 0. `bound-in-stage-at-empty` stays the parent name, still open.

## THE REASONING

This is not a second `GraphAt`. The neighbour is 746-SPLIT's fatal assembly. The obligation is the green spelling packaged at the name the meter reads. Named reading about 10k tokens at 4 B per token: this brief; 746-SPLIT report HEAD and next-brief; PT.agda:63-82. No bare master over 40 kB.

## W3, THE WIDEST UNMEASURED TERM

Whether the packaged alias still converts in a fresh file. Estimate 20 to 80 lines. Basis: agents/tasks/LJ-1-746-SPLIT/lj-1.746-SPLIT-report.md:28

## WHAT GO AND NO-GO EACH EARN

**GO** is the named mirror later briefs may consume without spelling `GraphAt`. **NO-GO** names the binder the PT file hid. Do not inhabit `GraphAt`. Do not inhabit `bound-in-stage-at-empty`. Do not ask for heavy.

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
id = "transfer-park"
priority = 11
action = "park_and_split"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  heap_wall = false
  changed_files_any = ["agents/tasks/LJ-1-746-SPLIT-SPLIT/lj-1.746-SPLIT-SPLIT-report.md"]
  changed_files_none = ["agents/tasks/LJ-1-746-SPLIT-SPLIT/review-of-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-746-SPLIT-SPLIT/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-746-SPLIT-SPLIT/review-of-LJ-*-*.md"]

[[branch]]
id = "lint-back-to-author"
priority = 13
action = "escalate"
head_slot = "coder"

  [branch.when]
  exit_code = 1
  error_class_in = ["lint"]

[[branch]]
id = "accept-failed"
priority = 14
action = "escalate"
head_slot = "coder_adversarial"

  [branch.when]
  exit_code = 1
  obligations_delta_max = -1
  changed_files_none = ["agents/tasks/LJ-1-746-SPLIT-SPLIT/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-746-SPLIT-SPLIT/Probe746SplitSplit.agda"]
  changed_files_none = ["agents/tasks/LJ-1-746-SPLIT-SPLIT/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-746-SPLIT-SPLIT/review-of-*.md"]

[[branch]]
id = "heap-wall-park"
priority = 30
action = "park_and_split"

  [branch.when]
  heap_wall = true

[[branch]]
id = "no-go-bare"
priority = 40
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
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

## STANDING (program-generated, do not edit)

The records every dispatch may need. They are NOT candidates, they are not the answer to any search, and no return has to account for them. The search below spends its whole budget on what is not here.

- STANDING archive/dev/JOURNAL-archived.md
- STANDING dev/literature/truncation-and-selection.md
- STANDING dev/literature/devlin-II5.md
- STANDING dev/literature/digest.md
- STANDING archive/dev/LJ-dispatch-index.md
- STANDING archive/dev/JOURNAL.md
- STANDING dev/literature/terms-2026-08.md
- STANDING dev/ARCHIVE.md
- STANDING dev/literature/geology.md
- STANDING archive/dev/DECISIONS-archived.md

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev, archive/scripts, dev/ARCHIVE.md:
- CANDIDATE archive/dev/DD-archived.md  (score 193.400)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 193.329)
- CANDIDATE archive/dev/PLAN-archived.md  (score 182.340)
- CANDIDATE archive/dev/TASKS-archived.md  (score 167.950)
- CANDIDATE archive/dev/STATUS-archived.md  (score 155.926)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-errata.md  (score 37.639)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 33.005)
- CANDIDATE dev/literature/primary-sources.md  (score 29.913)
- CANDIDATE dev/literature/rudimentary-functions.md  (score 26.325)
- CANDIDATE dev/literature/BIBLIOGRAPHY.md  (score 26.087)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
