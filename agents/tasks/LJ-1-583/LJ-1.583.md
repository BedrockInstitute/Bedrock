# LJ-1.583: the sealed projections LJ-1.576 could not answer

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-583/Probe583.agda`:

    sealed-gaps-closed : <the named GAPS among `[LJ-1.576]`'s five sealed
                          projections, answered>

Land nothing in `src/`.

**READ `[LJ-1.576]`'s `## WHAT ROW 2 NOW COSTS` AND TAKE ITS GAPS, NOT MINE.**
It reports that each of the five sealed projections of `LeastCardInjL` is
answered at `agents/tasks/LJ-1-576/Probe576.agda:327-382` **with a term or a
named gap**. **I do not name the gaps in this brief, because it measured them
and I did not.** Take the ones it left open. **If it left none open, say so and
stop: that is a full result and it means row 2 is further along than I think.**

**`[LJ-1.576]` IS GO AND IT OPENED ROW 2.** `[LJ-1.573]` had proved
`SqCollect` IS the axiom of choice over a set-indexed family
(`src/Base/Choice.lagda.md:55-56`) and asked whether `LeastCardInjL` could be
restated over the CODED injection. **`[LJ-1.576]` re-measured the archived claim
this turns on rather than inheriting it**: `isPropInjCode`
(`agents/tasks/LJ-1-576/Probe576.agda:77-84`) is green, so `[LJ-1.314]`'s
verdict survives at today's tree and `leastOf` untruncates the code.

**AND THE DOWNSTREAM BILL IS SMALL AND COUNTED.** `grep -rn "LeastCardInjL" src/`
returns 8: the module header (`src/L/Cardinal.lagda.md:61`), an import and a
comment (`src/L/SquareLawClosed.lagda.md:37`, `:65`), and the five sealed
projections (`:74`, `:77`, `:80`, `:84`, `:89`). **Nothing outside one file
reads the module.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-583/Probe583.agda::sealed-gaps-closed"]

## SCOPE (write)
- agents/tasks/LJ-1-583/Probe583.agda
- agents/tasks/LJ-1-583/lj-1.583-report.md
- agents/tasks/LJ-1-583/review-of-sealed-gaps.md
- agents/tasks/LJ-1-583/runs/

## PREMISES

1. `[LJ-1.576]` is GO. Basis: agents/tasks/LJ-1-576/lj-1.576-report.md:1
2. It answers the five projections with a term or a named gap. Basis: agents/tasks/LJ-1-576/Probe576.agda:327
3. `isPropInjCode` is green at today's tree. Basis: agents/tasks/LJ-1-576/Probe576.agda:77
4. `[LJ-1.573]` proved `SqCollect` is `SetChoice`. Basis: src/Base/Choice.lagda.md:55
5. `LeastCardInjL` is a module in `Cardinal`. Basis: src/L/Cardinal.lagda.md:61
6. Its ambient `Inj` was the blocker. Basis: src/L/Cardinal.lagda.md:63
7. The five sealed projections are in one file. Basis: src/L/SquareLawClosed.lagda.md:74
8. `readL` turns a code into an ambient injection. Basis: src/L/CantorBernstein.lagda.md:33
9. `InjL` is a truncated `InjCode`. Basis: src/L/GCH.lagda.md:37
10. `[LJ-1.314]` named the cure at an old tree. Basis: archive/dev/LJ-dispatch-index.md:371
11. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
12. A stop is a deliverable. Basis: AGENTS.md:43
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

A coded restatement, a green `isPropInjCode`, and five projections each answered
or named. **The named ones are not answered.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE GAP LIST.** Read `Probe576.agda:327-382`
and say at `file:line` **which of the five are terms and which are named gaps.**
Report the count. **Build only the gaps.**

**DO NOT REBUILD WHAT `[LJ-1.576]` ANSWERED.** Import its terms.

**DO NOT REACH FOR AN AMBIENT CHOICE PRINCIPLE.** `[LJ-1.573]` was forbidden it
and stopped honestly rather than taking it. The same rule binds here: this
development is PROVING `L ⊨ AC` and must not assume it ambiently. **Do not add
an axiom and do not postulate.**

**IF A GAP NEEDS THE AMBIENT `Inj` BACK, SAY SO AND STOP.** That would mean the
coded restatement does not reach that projection, and the mathematician must
know which one.

**DO NOT BUILD `SqCollectAt` ITSELF.** If the gaps close, say what row 2 now
costs and stop. AD12 gives this brief one obligation.

**DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE FIVE, ONE ROW EACH`.** Term or gap, then
closed or not, each at `file:line`.

**REQUIRED REPORT SECTION `## WHAT ROW 2 NOW COSTS`.** What remains before
`SqCollectAt` is payable. **Do not read a discharge into anything you did not
inhabit.**

ESTIMATE: about 170 lines in the probe, of which the obligation is about 45.
BASIS: `[LJ-1.576]` answered five projections at a comparable size and this
takes the subset it left. **If it left one gap, far less: report what you found
before you spend.** Comparables are of SHAPE and nothing may be funded against
them.

## W3, THE WIDEST UNMEASURED TERM

It is the gap count itself.

    -- the five projections, each marked term or gap, from Probe576.agda:327-382

**Read it FIRST and report the count before any Agda.** This is the one W3 in
the queue whose value is a list rather than a type. ESTIMATE: one read, under 10
minutes.

## WHAT GO AND NO-GO EACH EARN

**A GO CLOSES ROW 2'S REMAINDER WITHOUT A CHOICE PRINCIPLE.**

**A NO-GO NAMING THE PROJECTION THAT WANTS THE AMBIENT `Inj` BACK TELLS THE
MATHEMATICIAN THE CODED RESTATEMENT IS PARTIAL**, and exactly where.

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
  changed_files_none = ["agents/tasks/LJ-1-583/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-583/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-583/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-583/Probe583.agda"]
  changed_files_none = ["agents/tasks/LJ-1-583/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-583/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 238.928)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 229.849)
- CANDIDATE archive/dev/JOURNAL.md  (score 229.282)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 174.054)
- CANDIDATE archive/dev/DD-archived.md  (score 173.570)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 69.307)
- CANDIDATE dev/literature/digest.md  (score 63.668)
- CANDIDATE dev/literature/devlin-II5.md  (score 56.003)
- CANDIDATE dev/literature/geology.md  (score 49.799)
- CANDIDATE dev/literature/terms-2026-08.md  (score 45.640)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
