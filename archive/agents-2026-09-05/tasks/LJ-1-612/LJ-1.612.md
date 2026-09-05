# LJ-1.612: the rehoming defect, which is cheap and costs the campaign its own archive

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-612/Probe612.agda`:

    rehomed-import-works : <a rehomed probe whose top module name predates
                            `[LJ-1.142]`, imported through the library and
                            used>

Land nothing in `src/`.

**`[LJ-1.607]` FOUND THIS WHILE DOING SOMETHING ELSE AND SAID IT IS CHEAP.** Its
own words:

> "**The rehoming defect is cheap to fix and worth a row in a W4 pass**: rehomed
> probes whose top module name predates `[LJ-1.142]` cannot be imported through
> the library (`runs/p136-1.out`). **No mathematical content is at risk**; the
> flags or a copy restore them, as `runs/cold/` shows."

**IT MATTERS MORE THAN IT LOOKS, AND HERE IS WHY.** This campaign has twice been
saved by reading a predecessor's probe: `[LJ-1.572]`'s recovered stop is cited
by three live briefs, and `[LJ-1.160]`'s `crossOut` is the named precedent for a
face queued this hour. **A probe that cannot be imported is a probe that can only
be read, never reused**, and R-42 measures re-typing an object across files at
1.74 s against 155.02 s.

**THIS IS NOT MATHEMATICS AND THE BRIEF DOES NOT PRETEND IT IS.** It is a
plumbing repair with a measured symptom and a named cure. **It is queued because
it is cheap, real, and blocks reuse of work the campaign has already paid for.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-612/Probe612.agda::rehomed-import-works"]

## SCOPE (write)
- agents/tasks/LJ-1-612/Probe612.agda
- agents/tasks/LJ-1-612/lj-1.612-report.md
- agents/tasks/LJ-1-612/review-of-rehomed-import.md
- agents/tasks/LJ-1-612/runs/

## PREMISES

1. `[LJ-1.607]` names the defect and calls it cheap. Basis: agents/tasks/LJ-1-607/lj-1.607-report.md:186
2. Its symptom is reproduced by a checked probe. Basis: agents/tasks/LJ-1-607/runs/cold/P136Cold.agda:1
3. Its cure is shown by a cold run. Basis: agents/tasks/LJ-1-607/lj-1.607-report.md:186
4. `[LJ-1.160]`'s probe is on disk and is a live precedent. Basis: agents/tasks/LJ-1-160/ProbeLJ1160A.agda:71
5. `[LJ-1.572]`'s recovered stop is cited by live briefs. Basis: agents/tasks/LJ-1-572/review-of-b9-g-definable.md:1
6. R-42 measures the cost of re-typing an object across files. Basis: dev/LESSONS.md:4404
7. `[LJ-1.559]` re-measured a floor after losing a predecessor's work. Basis: agents/tasks/LJ-1-559/lj-1.559-report.md:1
8. Never commit a generated file. Basis: AGENTS.md:71
9. Every file under `_build/` declares its lifecycle. Basis: AGENTS.md:72
10. A stop is a deliverable. Basis: AGENTS.md:43
11. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
12. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

A measured symptom, a named cure and a cold run showing the cure works. **No
repair.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE SYMPTOM.** Read
`agents/tasks/LJ-1-607/runs/p136-1.out` and `runs/cold/`, and say at
`file:line` **what fails and what the cold run did differently.** If the symptom
does not reproduce here, say so and stop: that is a full result.

**PICK ONE REHOMED PROBE AND NAME IT.** Do not attempt a sweep. **One probe
imported and used is the obligation**; a survey of how many are affected is a
useful report section but not the deliverable.

**THE CURE IS "THE FLAGS OR A COPY" AND THOSE ARE NOT THE SAME.** Say which you
used and why. **A copy duplicates content and R-42 says duplication of one
object across files is what costs**; prefer the flags if they work, and say so
if they do not.

**DO NOT EDIT ANY EXISTING PROBE.** Other tasks' directories are theirs. **Work
in your own and import.**

**DO NOT LAND IN `src/`. DO NOT POSTULATE. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE SYMPTOM AND THE CURE`.** Both at `file:line`,
with which cure you used.

**REQUIRED REPORT SECTION `## HOW MANY PROBES ARE AFFECTED`.** A count you
measured by grep over `agents/tasks/`. **Never conclude a count from a command
containing `head`.** Do not fix them; just say how many.

ESTIMATE: about 90 lines in the probe, of which the obligation is about 20, and
under a minute of Agda. BASIS: `[LJ-1.607]` calls it cheap and shows a working
cold run. Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the failing import itself.

    -- one rehomed probe's module, imported, TYPE ONLY, capped

**Write it FIRST, typecheck it ALONE, cap it.** If it imports cleanly, the
defect does not reproduce and you say so at once. ESTIMATE: about 8 lines, cap
at one minute.

## WHAT GO AND NO-GO EACH EARN

**A GO RESTORES REUSE OF EVERY PROBE THIS CAMPAIGN HAS PAID FOR**, and two
briefs queued this week already depend on reading predecessors' probes.

**A NO-GO SAYING THE CURE DOES NOT WORK IS WORTH KNOWING CHEAPLY**, because the
campaign would then be relying on reads it cannot mechanise.

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
  changed_files_none = ["agents/tasks/LJ-1-612/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-612/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-612/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-612/Probe612.agda"]
  changed_files_none = ["agents/tasks/LJ-1-612/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-612/review-of-*.md"]

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
- CANDIDATE archive/dev/JOURNAL.md  (score 251.248)
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 248.144)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 246.416)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 200.948)
- CANDIDATE archive/dev/DD-archived.md  (score 192.213)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 61.626)
- CANDIDATE dev/literature/digest.md  (score 59.739)
- CANDIDATE dev/literature/devlin-II5.md  (score 56.388)
- CANDIDATE dev/literature/terms-2026-08.md  (score 41.466)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 36.595)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
