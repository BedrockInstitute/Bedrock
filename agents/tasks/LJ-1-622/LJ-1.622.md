# LJ-1.622: bisect what actually walls in CardAboveL, now that the imports are cleared

## HEAD
head_slot: coder
machine: exclusive

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-622/Probe622.agda`:

    landing-bisection : <the part of `CardAboveL`'s own elaboration that exceeds
                         the caliber, named, with peak RSS per part>

**This is a MEASUREMENT, not a landing.** Land nothing in `src/`. **Do not run
`make check`.**

**`[LJ-1.619]` IS GO AND IT CLEARED THE IMPORTS, WHICH WAS MY HYPOTHESIS AND WAS
WRONG.** Its ladder ran all eleven modules, every rung exit 0, and the top of the
closure with one trivial term peaks at **634,322,944 bytes (605 MiB) of the
2,147,483,648 byte (`-M2g`) cap, 3.01 s: 29.5 percent of the heap, with 1.36 GB
of headroom.** Its verdict: **"A new master over these imports is therefore
possible at this caliber, and it stopped being possible at NO rung."**

**SO THREE CAUSES ARE NOW EXCLUDED BY MEASUREMENT, AND TWO OF THE THREE WERE
MINE.**

- **Not `make check`**: `[LJ-1.616]` reversed the order I blamed and walled anyway.
- **Not my ordering**: `[LJ-1.599]` at 18.79 s and `[LJ-1.616]` at 19.32 s walled
  half a second apart under opposite instructions.
- **Not the import closure**: `[LJ-1.619]`, same caliber, 29.5 percent of cap.

**WHAT IS LEFT IS `CardAboveL`'s OWN ELABORATION**, and `[LJ-1.555]` measured
that master at 587 lines. **1.36 GB of headroom is not enough for it, and nobody
knows which part costs.**

**THE CALIBER IS `-M2g` AND NOT `-M8g`.** `[LJ-1.619]` reports it. Several
earlier reports in this campaign quote `-M8g`, so **state the caliber your pane
gives you and do not assume either figure.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-622/Probe622.agda::landing-bisection"]

## SCOPE (write)
- agents/tasks/LJ-1-622/Probe622.agda
- agents/tasks/LJ-1-622/lj-1.622-report.md
- agents/tasks/LJ-1-622/review-of-landing-bisection.md
- agents/tasks/LJ-1-622/runs/

## PREMISES

1. `[LJ-1.619]` is GO and cleared the import closure. Basis: agents/tasks/LJ-1-619/lj-1.619-report.md:1
2. Its ladder reached the full closure at 29.5 percent of cap. Basis: agents/tasks/LJ-1-619/lj-1.619-report.md:1
3. `[LJ-1.599]` walled at 18.79 s with zero runs. Basis: agents/tasks/LJ-1-599/LJ-1.599.md:1
4. `[LJ-1.616]` walled at 19.32 s after the order was reversed. Basis: agents/tasks/LJ-1-616/LJ-1.616.md:1
5. `[LJ-1.555]` measured the master at 587 lines. Basis: agents/tasks/LJ-1-555/review-of-CardAboveL-landing.md:81
6. It read the import graph over 102 masters. Basis: agents/tasks/LJ-1-555/review-of-CardAboveL-landing.md:56
7. `[LJ-1.528]` built `CardAboveL` in a probe under `--safe`. Basis: agents/tasks/LJ-1-528/Probe528.agda:638
8. `[LJ-1.526]` proved the reduction it discharges. Basis: agents/tasks/LJ-1-526/lj-1.526-report.md:1
9. `[LJ-1.545]` measured the heap linear in field count. Basis: agents/tasks/LJ-1-545/lj-1.545-report.md:1
10. `[LJ-1.75]` measured a trimmed telescope better than proportional. Basis: archive/dev/LJ-dispatch-index.md:142
11. R-42 rules the respelling cost. Basis: dev/LESSONS.md:4404
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

A cleared import floor with 1.36 GB of headroom, a 587-line master that walls
inside it, and two silent failures that kept nothing.

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE SPLIT.** `[LJ-1.528]`'s probe holds the
term. **Divide `CardAboveL` into parts you can typecheck separately, and say at
`file:line` what each part is** before measuring any of them.

**MEASURE PART BY PART AND WRITE EACH NUMBER TO `runs/` BEFORE THE NEXT.**
`[LJ-1.599]` and `[LJ-1.616]` each left ZERO files, so the campaign kept nothing
from either. **A part recorded is a part kept even if you are cut off**, and
that is the whole design of this brief.

**PEAK RSS IS THE PRIMARY NUMBER, SECONDS IS THE SECOND.** This is a heap wall,
`rc 251` or Agda's own "Heap exhausted", not a deadline kill.

**DO NOT SET `GHCRTS` YOURSELF** and **state the caliber your pane gives you.**

**IF ONE PART DOMINATES, NAME IT AND STOP.** That is the deliverable. **Do not
then try to land the whole thing**: `[LJ-1.75]`'s measured cure is that trimming
is better than proportional, and a named hot part is what a trimming brief needs.

**DO NOT LAND IN `src/` AND DO NOT RUN `make check`.** AD12 gives this brief one
obligation and it is the bisection.

**DO NOT POSTULATE. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE PARTS`.** One row per part: what it is, peak
RSS, seconds, exit.

**REQUIRED REPORT SECTION `## WHAT A LANDING BRIEF SHOULD NOW SAY`.** Three
sentences. **Given the hot part, say what a brief that lands `CardAboveL` must
carry.** That sentence is what I will write the next landing from, and the last
three landing briefs were written from my guesses.

ESTIMATE: about 120 lines of probe across the parts, and the time is what you
are measuring. BASIS: `[LJ-1.619]` measured an eleven-rung ladder at 3.01 s
total. Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the smallest part of `CardAboveL` that still typechecks alone.

    -- one part, typechecked alone over the cleared imports, peak RSS recorded

**Do this FIRST and write its number to `runs/` before adding a second part.**
ESTIMATE: unmeasured, and that is the point.

## WHAT GO AND NO-GO EACH EARN

**A GO NAMES THE PART THAT COSTS**, and the campaign's first landing becomes a
trimming problem with a target instead of a fourth guess.

**A NO-GO SHOWING NO SINGLE PART DOMINATES IS ALSO A RESULT**, because it would
say the 587 lines are uniformly expensive and the master must be split into two
chapters rather than trimmed.

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
  changed_files_none = ["agents/tasks/LJ-1-622/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-622/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-622/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-622/Probe622.agda"]
  changed_files_none = ["agents/tasks/LJ-1-622/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-622/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 255.201)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 240.067)
- CANDIDATE archive/dev/JOURNAL.md  (score 222.841)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 189.784)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 187.791)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/digest.md  (score 45.301)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 43.076)
- CANDIDATE dev/literature/devlin-II5.md  (score 42.554)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 34.198)
- CANDIDATE dev/literature/formalizations-landscape.md  (score 31.987)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
