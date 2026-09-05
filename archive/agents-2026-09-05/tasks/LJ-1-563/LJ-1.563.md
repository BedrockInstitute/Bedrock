# LJ-1.563: the last three of the sixteen

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-563/Probe563.agda`:

    last-three-collected :
      <the three `TFacts` fields that ask for something the record does not
       give and are NOT memberships in K, collected at KValue's frame>

Land nothing in `src/`.

**THE FRONT HAS BEEN CLOSING AND THIS IS WHAT IS LEFT.** `[LJ-1.512]` counted 54
honest forms of 59, of which 16 ask for more. `[LJ-1.551]` collected the 38 clean
ones and read all sixteen at first hand, finding **13 of them ask for a
membership in `K`**. `[LJ-1.553]` is GO and discharged those thirteen from one
supplied membership. **Three remain, and `[LJ-1.551]` named them in its
`## WHAT THE 16 WOULD COST` section.**

**READ THAT SECTION AND TAKE ITS THREE, NOT MINE.** I do not name them here
because `[LJ-1.551]` measured them and I did not.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-563/Probe563.agda::last-three-collected"]

## SCOPE (write)
- agents/tasks/LJ-1-563/Probe563.agda
- agents/tasks/LJ-1-563/lj-1.563-report.md
- agents/tasks/LJ-1-563/review-of-last-three.md
- agents/tasks/LJ-1-563/runs/

## PREMISES

1. `[LJ-1.512]` counted 54 honest forms of which 16 ask for more. Basis: agents/tasks/LJ-1-512/lj-1.512-report.md:1
2. `[LJ-1.551]` is GO and collected the 38 clean forms. Basis: agents/tasks/LJ-1-551/lj-1.551-report.md:1
3. It read all sixteen at first hand and grouped 13 as `K` memberships. Basis: agents/tasks/LJ-1-551/lj-1.551-report.md:1
4. `[LJ-1.553]` is GO and discharged thirteen from one membership. Basis: agents/tasks/LJ-1-553/lj-1.553-report.md:1
5. `TFacts` has 59 fields. Basis: src/L/Condensation/TwelveAgree.lagda.md:129
6. `KFacts` has 29 fields. Basis: src/L/Condensation.lagda.md:6079
7. `KValue` delivers a `KFacts` value at this frame. Basis: src/L/Condensation.lagda.md:7411
8. `[LJ-1.545]` measured the heap linear in field count. Basis: agents/tasks/LJ-1-545/lj-1.545-report.md:1
9. `[LJ-1.71]` shipped a module whose telescope was uninhabited at every frame. Basis: archive/dev/LJ-dispatch-index.md:135
10. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
11. Evidence is `file:line`. Basis: AGENTS.md:41
12. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

38 clean fields in one value, and thirteen more discharged from a single
membership. **Three fields have never been collected by anybody.**

## THE REASONING

**D-10, BEFORE ANY AGDA.** Name the three at `file:line` from `[LJ-1.551]`'s
section and say what each asks for. **If you find that the count is not three,
report the number you measured and take yours.**

**GUARD AGAINST VACUITY FIRST.** `[LJ-1.71]` shipped a module whose telescope was
uninhabited at every frame (`archive/dev/LJ-dispatch-index.md:135`). **Inhabit
before you collect. That is W3.**

**THREE FIELDS MAY ASK FOR THREE DIFFERENT THINGS, AND THAT IS ALLOWED.** Do not
force a common hypothesis on them the way `[LJ-1.553]` could for the thirteen.
**If they do not share one, say so and collect them side by side.**

**IF ONE OF THE THREE IS NOT SATISFIABLE AT THIS FRAME, STOP ON THAT ONE AND
COLLECT THE OTHERS.** Say which and why. `[LJ-1.512]` recorded that two fields of
the 59 had no honest form anywhere, so an unsatisfiable row here would not be a
surprise.

**DO NOT RE-COLLECT THE 38 OR THE 13.** AD12 gives this brief one obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE THREE, NAMED`.** Each at `file:line`, what it
asks for, and whether you collected it.

**REQUIRED REPORT SECTION `## WHAT THE FRONT NOW STANDS AT`.** Of the 59
`TFacts` fields, say how many are now covered by a collected value and how many
are not. **Count, do not estimate.**

ESTIMATE: about 140 lines in the probe, of which the obligation is about 30, and
under 10 seconds of Agda. BASIS: `[LJ-1.551]` collected 38 fields and
`[LJ-1.553]` thirteen. Comparables are of SHAPE and nothing may be funded
against them.

## W3, THE WIDEST UNMEASURED TERM

It is whether the three hypotheses hold together at one frame.

    -- the three fields' extra hypotheses, at KValue's frame, INHABITED

**Write it FIRST and typecheck it ALONE.** ESTIMATE: about 18 lines, under 30
seconds.

## WHAT GO AND NO-GO EACH EARN

**A GO CLOSES THE HONEST-FORM FRONT**, and the mathematician can then price what
`TFacts` still costs as a single number for the first time.

**A NO-GO NAMES THE FIELD THAT WILL NOT JOIN**, which is the seam in the record.

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
  changed_files_none = ["agents/tasks/LJ-1-563/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-563/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-563/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-563/Probe563.agda"]
  changed_files_none = ["agents/tasks/LJ-1-563/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-563/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 142.545)
- CANDIDATE archive/dev/JOURNAL.md  (score 136.536)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 134.769)
- CANDIDATE dev/ARCHIVE.md  (score 114.010)
- CANDIDATE archive/dev/PLAN-archived.md  (score 104.974)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/digest.md  (score 42.764)
- CANDIDATE dev/literature/devlin-II5.md  (score 34.811)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 33.268)
- CANDIDATE dev/literature/terms-2026-08.md  (score 25.961)
- CANDIDATE dev/literature/rudimentary-functions.md  (score 23.600)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
