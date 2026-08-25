# LJ-1.578: build CoHyps, at the price its predecessor measured

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-578/Probe578.agda`:

    cohyps-supplied : <`[LJ-1.550]`'s `CoHyps` INHABITED at the frame
                       `gch-from-five` calls it>

which is row 3 of the bill (`agents/tasks/LJ-1-550/Probe550.agda:215-230`,
`src/L/BoundedSubset.lagda.md:1555-1558`). Land nothing in `src/`.

**`[LJ-1.570]` IS GO ON THE INVENTORY AND EXPLICITLY NOT ON THE ROW.** Its own
verdict line reads **"obligation INHABITED; `CoHyps` NOT SUPPLIED."** It did the
survey this brief now builds against, and it did not let me read a discharge
into it.

**AND IT REPLACED A FOUR-HUNDRED-DISPATCH-OLD NUMBER WITH A MEASURED ONE.** It
re-landed `[LJ-1.52]`'s `matrix-decode` and `adeq-decode` at today's tree and
counted **41 non-blank non-comment lines** over `Probe570.agda:251-337`,
against `[LJ-1.304]`'s inferred "about 40"
(`agents/tasks/LJ-1-304/lj-1.304-report.md:332-335`). **The measurement agrees
with the inference.**

**THAT NUMBER IS WHY THIS TASK IS QUEUED AND NOT DEFERRED.** The archive priced
this pair as a wall at 1.0k lines (`archive/dev/LJ-dispatch-index.md:222`) and
at 2.8k to 3.3k for a level-hood certificate (`:198`). **Those are old prices at
an old tree and NOTHING MAY BE FUNDED AGAINST THEM.** `[LJ-1.570]`'s 41 is a
measurement at today's tree and it is much smaller than the shape those numbers
suggest.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-578/Probe578.agda::cohyps-supplied"]

## SCOPE (write)
- agents/tasks/LJ-1-578/Probe578.agda
- agents/tasks/LJ-1-578/lj-1.578-report.md
- agents/tasks/LJ-1-578/review-of-cohyps-supplied.md
- agents/tasks/LJ-1-578/runs/

## PREMISES

1. `[LJ-1.570]` is GO on the inventory and did not supply `CoHyps`. Basis: agents/tasks/LJ-1-570/lj-1.570-report.md:1
2. It measured 41 lines at today's tree. Basis: agents/tasks/LJ-1-570/Probe570.agda:251
3. `[LJ-1.304]` inferred about 40. Basis: agents/tasks/LJ-1-304/lj-1.304-report.md:332
4. `CoHyps` is `Co`'s two parameters. Basis: src/L/BoundedSubset.lagda.md:1555
5. Row 3 of the bill is `CoHyps`. Basis: agents/tasks/LJ-1-550/Probe550.agda:215
6. `[LJ-1.564]`'s bill is five rows. Basis: agents/tasks/LJ-1-564/Probe564.agda:456
7. `[LJ-1.146]` priced the pair at about 1.0k lines at an old tree. Basis: archive/dev/LJ-dispatch-index.md:222
8. `[LJ-1.121]` priced a level-hood certificate at 2.8k to 3.3k. Basis: archive/dev/LJ-dispatch-index.md:198
9. `[LJ-1.560]` is GO and its obligation was an instantiation. Basis: agents/tasks/LJ-1-560/lj-1.560-report.md:1
10. `[LJ-1.543]` found a sibling row did not need the theorem at all. Basis: agents/tasks/LJ-1-543/lj-1.543-report.md:1
11. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
12. A stop is a deliverable. Basis: AGENTS.md:43
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

An inventory of what `levelIn` and `cover` ask for today, and one re-landed
41-line piece. **The row itself is not supplied.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS `[LJ-1.570]`'s INVENTORY.** Read its report's
`## WHAT EACH ASKS FOR TODAY` and say at `file:line` what it marked supplied,
suppliable and not. **Build against its marks, not against the archive's
prose.**

**RE-USE ITS 41 LINES RATHER THAN REBUILDING THEM.** `Probe570.agda:251-337` is
committed. **Import or copy it and say in the report which lines you took.**

**`[LJ-1.560]`'s REFLECTION STEP IS THE UNTRIED CANDIDATE.** Its obligation is at
`agents/tasks/LJ-1-560/Probe560.agda:165-176` and it turned out to be an
INSTANTIATION of something already in the tree. **`[LJ-1.570]` was told to try it
against this pair; say at `file:line` whether it did and what happened.**

**IF THE ROW STILL WILL NOT GO, PRICE THE REMAINDER IN LINES YOU MEASURED.**
That is the NO-GO deliverable, and it must be your number and not an inherited
one.

**DO NOT BUILD A LEVEL-HOOD CERTIFICATE.** If that is what is left, name it and
stop. This brief does not fund it.

**DO NOT ATTEMPT ROWS 1, 2, 4 OR 5.** AD12 gives this brief one obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## WHAT I TOOK FROM LJ-1.570`.** The lines, at
`file:line`, and what you changed.

**REQUIRED REPORT SECTION `## WHAT THIS DOES TO THE BILL`.** Which rows you
paid, which you did not. **Do not read a discharge into anything you did not
inhabit.** Two predecessors held that line this week and it is the standard now.

ESTIMATE: about 190 lines in the probe, of which the obligation is about 50.
BASIS: `[LJ-1.570]`'s 41 measured lines plus the two hypotheses' own statements.
Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is whichever of `levelIn` and `cover` `[LJ-1.570]` marked hardest.

    -- that one, re-ascribed at gch-from-five's frame, TYPE ONLY

**Write it FIRST and typecheck it ALONE.** ESTIMATE: about 12 lines, under 90
seconds.

## WHAT GO AND NO-GO EACH EARN

**A GO TAKES THE BILL FROM FIVE ROWS TO FOUR AND CLOSES A WALL THAT HAS STOOD
SINCE `[LJ-1.7]`.**

**A NO-GO WITH A MEASURED REMAINDER IS THE FIRST HONEST PRICE THIS PAIR HAS HAD
IN FOUR HUNDRED DISPATCHES.**

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
  changed_files_none = ["agents/tasks/LJ-1-578/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-578/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-578/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-578/Probe578.agda"]
  changed_files_none = ["agents/tasks/LJ-1-578/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-578/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 248.456)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 231.387)
- CANDIDATE archive/dev/JOURNAL.md  (score 230.783)
- CANDIDATE archive/dev/DD-archived.md  (score 189.864)
- CANDIDATE archive/dev/PLAN-archived.md  (score 187.673)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 70.906)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 53.300)
- CANDIDATE dev/literature/digest.md  (score 44.958)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 41.455)
- CANDIDATE dev/literature/geology.md  (score 38.622)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
