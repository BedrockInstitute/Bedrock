# LJ-1.590: StageOfCode, row 2's reflection step

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-590/Probe590.agda`:

    stage-of-code : <`[LJ-1.583]`'s `StageOfCode`>
      (`agents/tasks/LJ-1-583/Probe583.agda:259-262`)

Land nothing in `src/`.

**`[LJ-1.583]` IS GO AND IT PAID HALF OF ROW 2'S REMAINDER.** `[LJ-1.576]` had
stated the bill as four items; `[LJ-1.583]` measured at today's tree that **two
of the four are gone**:

| item | after `[LJ-1.583]` | at |
|---|---|---|
| 1 `IdCoded` | **PAID** | `Probe583.agda:123-126` |
| 2 `CodeBounded` | **OPEN, restated as `StageOfCode`** | `Probe583.agda:259-262` |
| 3 `CodedComp` | **PAID** | `Probe583.agda:169-180` |
| 4 the coded factor | **OPEN, as `SquareCoded`** | `Probe583.agda:195-196` |

**Its own summary: "SO ROW 2 NOW COSTS TWO THINGS AND NEITHER IS A
PRINCIPLE."** This brief takes the first. `[LJ-1.591]` asks about the second.

**`[LJ-1.576]` CALLED THIS ITEM "A REFLECTION STEP", AND THE TREE HAS ONE.**
`[LJ-1.560]` is GO and its obligation turned out to be an **INSTANTIATION** of
something already in `src/L/Reflect.lagda.md`
(`agents/tasks/LJ-1-560/Probe560.agda:165-176`). **Nobody has tried it against
this item.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-590/Probe590.agda::stage-of-code"]

## SCOPE (write)
- agents/tasks/LJ-1-590/Probe590.agda
- agents/tasks/LJ-1-590/lj-1.590-report.md
- agents/tasks/LJ-1-590/review-of-stage-of-code.md
- agents/tasks/LJ-1-590/runs/

## PREMISES

1. `[LJ-1.583]` is GO. Basis: agents/tasks/LJ-1-583/lj-1.583-report.md:1
2. It restates the open item as `StageOfCode`. Basis: agents/tasks/LJ-1-583/Probe583.agda:259
3. It paid `IdCoded`. Basis: agents/tasks/LJ-1-583/Probe583.agda:123
4. It paid `CodedComp`. Basis: agents/tasks/LJ-1-583/Probe583.agda:169
5. `[LJ-1.576]` called the item a reflection step. Basis: agents/tasks/LJ-1-576/lj-1.576-report.md:1
6. `[LJ-1.560]` is GO and its obligation was an instantiation. Basis: agents/tasks/LJ-1-560/Probe560.agda:165
7. `Ladder` is in the reflection chapter. Basis: src/L/Reflect.lagda.md:256
8. `InjCode` is a proposition at today's tree. Basis: agents/tasks/LJ-1-576/Probe576.agda:77
9. `[LJ-1.573]` proved `SqCollect` is `SetChoice`. Basis: src/Base/Choice.lagda.md:55
10. `[LJ-1.587]` delivered a composite-pair producer at arbitrary L-elements. Basis: agents/tasks/LJ-1-587/Probe587.agda:259
11. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
12. A stop is a deliverable. Basis: AGENTS.md:43
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

Half of row 2's remainder, a reflection step that turned out to be already in
the tree, and a composite-pair producer. **No term of this shape.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE INSTANTIATION TEST.** Re-ascribe
`[LJ-1.560]`'s obligation (`agents/tasks/LJ-1-560/Probe560.agda:165-176`) at
`StageOfCode`'s frame and say at `file:line` whether it applies. **If it does,
report that and finish early**: `[LJ-1.560]` found its own estimate far too high
for exactly this reason, and saying so is a good outcome.

**IF IT DOES NOT APPLY, SAY WHAT IS DIFFERENT.** A reflection step that bounds a
search over the L-carrier is not automatically one that bounds a CODE. **Name
the difference at `file:line`.**

**DO NOT REACH FOR AN AMBIENT CHOICE PRINCIPLE.** `[LJ-1.573]` proved row 2's
parent is `SetChoice` and stopped rather than assume it. This development is
PROVING `L ⊨ AC`. **Do not add an axiom and do not postulate.**

**DO NOT BUILD `SquareCoded`.** `[LJ-1.591]` asks about it. AD12 gives this brief
one obligation.

**DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## DID THE REFLECTION STEP APPLY`.** Yes or no, at
`file:line`, with what you had to change.

**REQUIRED REPORT SECTION `## WHAT ROW 2 NOW COSTS`.** One item or two.
**Do not read a discharge into anything you did not inhabit.**

ESTIMATE: about 150 lines in the probe, of which the obligation is about 35.
**If `[LJ-1.560]`'s term applies, far less, and I would rather be wrong that way
than fund a rebuild.** Comparables are of SHAPE and nothing may be funded
against them.

## W3, THE WIDEST UNMEASURED TERM

It is `[LJ-1.560]`'s obligation re-ascribed here.

    -- LJ-1.560's search-bounds, at StageOfCode's frame, TYPE ONLY

**Write it FIRST and typecheck it ALONE.** ESTIMATE: about 12 lines, under 2
minutes.

## WHAT GO AND NO-GO EACH EARN

**A GO LEAVES ROW 2 WITH ONE ITEM.**

**A NO-GO NAMING THE DIFFERENCE BETWEEN BOUNDING A SEARCH AND BOUNDING A CODE
IS A DISTINCTION THE WHOLE CAMPAIGN NEEDS**, because three other rows want a
code and one task has now bounded a search.

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
  changed_files_none = ["agents/tasks/LJ-1-590/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-590/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-590/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-590/Probe590.agda"]
  changed_files_none = ["agents/tasks/LJ-1-590/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-590/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 166.169)
- CANDIDATE archive/dev/JOURNAL.md  (score 153.024)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 143.992)
- CANDIDATE archive/dev/DD-archived.md  (score 119.038)
- CANDIDATE dev/ARCHIVE.md  (score 118.200)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 45.438)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 38.446)
- CANDIDATE dev/literature/digest.md  (score 31.955)
- CANDIDATE dev/literature/terms-2026-08.md  (score 29.043)
- CANDIDATE dev/literature/geology.md  (score 27.112)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
