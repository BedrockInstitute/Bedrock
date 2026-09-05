# LJ-1.619: what does it cost merely to LOAD what a landing needs

## HEAD
head_slot: coder
machine: exclusive

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-619/Probe619.agda`:

    import-floor : <a module that imports exactly what `CardAboveL` needs and
                    defines ONE trivial term, with its peak RSS measured>

**This is a MEASUREMENT and not a landing.** Land nothing in `src/`. **Do not
state `CardAboveL`. Do not run `make check`.**

**TWO LANDING ATTEMPTS HAVE NOW WALLED AT THE SAME PLACE AND MY FIX DID NOT
MOVE IT.** `[LJ-1.599]` heap-walled at **18.79 s** with zero runs and no report.
I diagnosed that as my own W3 ordering `make check` first, and `[LJ-1.616]`
reversed the order to typecheck the new master alone first. **It walled at
19.32 s with zero runs and no report.**

**SO THE WALL IS NOT `make check` AND IT IS NOT THE ORDER I WROTE.** Two runs,
half a second apart, neither producing a single output file. **Whatever walls,
walls before anything the brief asks for can start.**

**THE HYPOTHESIS THIS TASK TESTS, AND IT IS MINE:** the import closure alone
exceeds the caliber. `CardAboveL`'s dependencies are eleven modules by
`[LJ-1.555]`'s count, including `L.Cardinal`, `L.BoundedSubset`,
`L.CantorBernstein` and `L.InjChain`. **If loading them is already at the cap,
no brief I write can land anything and the defect is not in my ordering.**

**I AM NOT REACHING FOR THAT AS AN EXCUSE.** I wrote "Land nothing in `src/`"
into 94 of my 126 briefs this campaign, and that is a separate failure that this
measurement does not touch. **But the campaign has no number for the import
floor, and without it nobody can tell a bad brief from a hard cap.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-619/Probe619.agda::import-floor"]

## SCOPE (write)
- agents/tasks/LJ-1-619/Probe619.agda
- agents/tasks/LJ-1-619/lj-1.619-report.md
- agents/tasks/LJ-1-619/review-of-import-floor.md
- agents/tasks/LJ-1-619/runs/

## PREMISES

1. `[LJ-1.599]` heap-walled with zero runs. Basis: agents/tasks/LJ-1-599/LJ-1.599.md:1
2. `[LJ-1.616]` heap-walled with zero runs after the order was reversed. Basis: agents/tasks/LJ-1-616/LJ-1.616.md:1
3. `[LJ-1.555]` lists `CardAboveL`'s eleven dependencies. Basis: agents/tasks/LJ-1-555/review-of-CardAboveL-landing.md:56
4. `L.BoundedSubset` imports `L.StageCardinal`. Basis: src/L/BoundedSubset.lagda.md:882
5. And instantiates it. Basis: src/L/BoundedSubset.lagda.md:1397
6. `[LJ-1.528]` built `CardAboveL` in a probe. Basis: agents/tasks/LJ-1-528/Probe528.agda:638
7. `[LJ-1.545]` measured the heap linear in field count at one caliber. Basis: agents/tasks/LJ-1-545/lj-1.545-report.md:1
8. `[LJ-1.559]` measured a floor in a trimmed frame. Basis: agents/tasks/LJ-1-559/lj-1.559-report.md:1
9. `[LJ-1.566]` measured a floor at 1.67 s. Basis: agents/tasks/LJ-1-566/lj-1.566-report.md:1
10. `[LJ-1.75]` measured a trimmed telescope better than proportional. Basis: archive/dev/LJ-dispatch-index.md:142
11. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
12. A stop is a deliverable. Basis: AGENTS.md:43
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

Two heap walls, both silent, and no number for what an import closure costs.

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE LADDER.** Do not import all eleven at
once. **Import them ONE AT A TIME, typechecking a trivial term after each, and
record peak RSS at every rung.** The deliverable is the LADDER, not the top.
**If it walls at rung k, that names the module that costs**, and that is worth
more than a single failure figure.

**RECORD PEAK RSS AS THE PRIMARY NUMBER AND SECONDS AS THE SECOND.** This is a
heap wall (rc 251 or Agda's own "Heap exhausted"), not a deadline kill, and the
two are different failure modes with different evidence.

**WRITE EACH RUNG'S NUMBER TO `runs/` AS YOU GO, BEFORE ATTEMPTING THE NEXT.**
Both predecessors left ZERO files. **A rung recorded is a rung the campaign
keeps even if you are cut off**, and that is the whole point of this task.

**DO NOT SET `GHCRTS` YOURSELF.** Use the caliber the program sets on your pane.
**Report what that caliber is**, because no report in this campaign states it for
a landing.

**DO NOT STATE `CardAboveL` AND DO NOT RUN `make check`.** Either would
reintroduce the thing being measured against. AD12 gives this brief one
obligation and it is the floor.

**DO NOT POSTULATE. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE LADDER`.** One row per rung: module added,
peak RSS, seconds, exit. **Numbers you measured.**

**REQUIRED REPORT SECTION `## CAN ANYTHING LAND AT THIS CALIBER`.** Two
sentences. **Say whether a new master over these imports is possible at all**,
and if not, say at which rung it stops being possible.

ESTIMATE: about 60 lines of probe across eleven rungs, and the time is what you
are measuring. BASIS: `[LJ-1.559]` and `[LJ-1.566]` measured floors of this
shape at seconds each, **but neither carried this import closure.** Comparables
are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is rung one.

    -- a module importing ONLY L.Cardinal, with one trivial term, peak RSS recorded

**Do this FIRST and write its number to `runs/` before adding rung two.**
ESTIMATE: unmeasured, and that is the point.

## WHAT GO AND NO-GO EACH EARN

**A GO GIVES THE CAMPAIGN THE NUMBER IT HAS NEVER HAD**, and every future
landing brief is priced against it instead of guessed.

**A NO-GO THAT NAMES THE RUNG WHERE THE CLOSURE EXCEEDS THE CAP IS THE BETTER
RESULT**, because it would say landing is blocked by the caliber and not by the
brief, and the mathematician would take that to the owner rather than write a
fourth landing attempt.

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
  changed_files_none = ["agents/tasks/LJ-1-619/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-619/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-619/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-619/Probe619.agda"]
  changed_files_none = ["agents/tasks/LJ-1-619/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-619/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 251.577)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 234.171)
- CANDIDATE archive/dev/JOURNAL.md  (score 224.940)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 207.894)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 205.631)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 57.725)
- CANDIDATE dev/literature/devlin-II5.md  (score 52.237)
- CANDIDATE dev/literature/digest.md  (score 48.078)
- CANDIDATE dev/literature/fine-structure.md  (score 38.094)
- CANDIDATE dev/literature/terms-2026-08.md  (score 32.818)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
