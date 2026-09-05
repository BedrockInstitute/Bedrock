# LJ-1.547: verify what LJ-1.566 delivered, and close. DO NOT RE-PROVE IT.

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Bind ONE name in `agents/tasks/LJ-1-547/Probe547.agda`:

    injcode-assembled : <the type LJ-1.566 gave it>

**by IMPORTING `[LJ-1.566]`'s delivered term and binding it. NOT by proving it
again.** Land nothing in `src/`.

**THIS BRIEF IS A REWRITE AND THE OLD ONE IS VOID.** `[LJ-1.547]` parked at
`attempt_max` after four 1800 s timeouts. The owner authorized closing it. **The
obligation it was sent for IS ALREADY DELIVERED, at the same obligation name**,
by `[LJ-1.566]`: `agents/tasks/LJ-1-566/Probe566.agda:492-495`.

**AND `[LJ-1.566]` MEASURED WHAT IT COSTS.** Floor 1.67 s, finish **9.66 s**,
exit 0 (`agents/tasks/LJ-1-566/lj-1.566-report.md`, `## THE FLOOR AND THE
FINISH`, `runs/floor-1.out`, `runs/full-final.out`). **This task spent four
1800 s runs failing at a term that typechecks in under ten seconds.**

**YOUR JOB IS A BOOKKEEPING CLOSE, NOT A PROOF.** Do not re-derive the term. Do
not execute the old brief's plan, which is what produced the four timeouts.

**THE HAZARD IS R-42.** `dev/LESSONS.md` R-42 rules that a carve output compared
across two spellings costs by the UNFOLDING, not the size: one unfolding, and
the arguments syntactically identical after it. **It was written from
`[LJ-1.541]`'s measurement and this task's own `## THE WALL, RE-MEASURED HERE`
is cited in it as the independent confirmation.**

**SO: IMPORT AND BIND. DO NOT RE-ASCRIBE AT THIS TASK'S OLD FRAME.** If the
imported term's type does not match on the nose, **STOP AND SAY SO.** A stop
here is a full result and much cheaper than a fifth timeout.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-547/Probe547.agda::injcode-assembled"]

## SCOPE (write)
- agents/tasks/LJ-1-547/Probe547.agda
- agents/tasks/LJ-1-547/lj-1.547-report.md
- agents/tasks/LJ-1-547/review-of-injcode-assembled.md
- agents/tasks/LJ-1-547/runs/

## PREMISES

1. `[LJ-1.566]` delivered the term. Basis: agents/tasks/LJ-1-566/Probe566.agda:492
2. It is GO. Basis: agents/tasks/LJ-1-566/lj-1.566-report.md:1
3. Its floor is 1.67 s and its finish 9.66 s. Basis: agents/tasks/LJ-1-566/lj-1.566-report.md:1
4. R-42 rules the respelling cost. Basis: dev/LESSONS.md:4404
5. R-41 is its sibling for a level or index in a type. Basis: dev/LESSONS.md:4762
6. This task's artifacts were salvaged into the main tree. Basis: agents/tasks/LJ-1-547/lj-1.547-report.md:1
7. Its own wall section re-measured the same shape. Basis: agents/tasks/LJ-1-547/lj-1.547-report.md:246
8. `InjCode` has four conjuncts. Basis: src/L/Cardinal.lagda.md:223
9. `InjCode` is a proposition at today's tree. Basis: agents/tasks/LJ-1-576/Probe576.agda:77
10. `[LJ-1.559]` built the fourth conjunct. Basis: agents/tasks/LJ-1-559/Probe559.agda:336
11. A stop is a deliverable. Basis: AGENTS.md:43
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

**The obligation itself, by `[LJ-1.566]`.** Nothing about it is open.

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE TYPE COMPARISON.** Put `[LJ-1.566]`'s
type and this task's old type side by side and say at `file:line` whether they
are identical. **If they are, bind and finish. If they are not, STOP** and name
the difference. **Do not bridge them.**

**THE OLD BRIEF'S W3 AND PLAN ARE VOID.** Your predecessor's report is in the
tree now and its `## THE WALL, RE-MEASURED HERE` is worth reading, **but do not
execute its plan.**

**BUDGET: THIS SHOULD TAKE MINUTES.** `[LJ-1.566]` finished in 9.66 s. **If your
run passes two minutes, the approach is wrong and not the machine: stop and
report the number.**

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## WHAT I BOUND AND FROM WHERE`.** The import at
`file:line`, and the typecheck time.

**REQUIRED REPORT SECTION `## WHY THIS IS NOT A PROOF`.** Two sentences saying
plainly that the mathematics was done by `[LJ-1.566]` and this task closed a
parked row. **Claim no credit for the term.**

ESTIMATE: about 40 lines in the probe and under 30 seconds of Agda. BASIS:
`[LJ-1.566]`'s measured 9.66 s finish. Comparables are of SHAPE and nothing may
be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is whether the two types are identical on the nose.

    -- LJ-1.566's injcode-assembled, imported, ascribed at ITS OWN type, TYPE ONLY

**Write it FIRST and typecheck it ALONE.** ESTIMATE: about 10 lines, under 30
seconds.

## WHAT GO AND NO-GO EACH EARN

**A GO CLOSES A PARKED ROW THE OWNER AUTHORIZED CLOSING.**

**A NO-GO NAMING A FRAME DIFFERENCE IS EQUALLY GOOD**, because it would say the
assembled code does not sit at this task's frame.

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
  changed_files_none = ["agents/tasks/LJ-1-547/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-547/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-547/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-547/Probe547.agda"]
  changed_files_none = ["agents/tasks/LJ-1-547/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-547/review-of-*.md"]

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
  Full entry: dev/LESSONS.md:2299
- **P-l. A statement may be ABOUT a concrete stage without dragging that stage's PRESENTATION into its type**
  **The law.** Being about a concrete position is not what costs. Naming a transparent construction in a statement's TYPE is. If the tower's stage values are `opaque` upstream, a theorem may quantify over, hypothesize about and conclude at `Sset ω` freely, because the stage is an ATOM to the elaborator and nothing unfolds. If instead the type mentions a transparent presentation, such as `⟪ sucV (...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2359
- **D-26. A well-founded key on a tower needs generation data, or it needs syntax**
  **Rule:** When a route must well-order a cumulative tower's stage, ask first what the stage's members CARRY. A stage built as the values of finitely many total operations carries its own generation data, so a well-founded key exists with NO syntax at all: the operation index, then the arguments, ordered recursively. A stage built as a definable power carries nothing: its members are sets, not c...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:1735
- **C-42. A refutation measures the site it names, and it never measures how far that site extends**
  **Rule:** A refutation is a measurement of ONE site. It says the statement there is false. **It says nothing about how many other sites carry the same false shape.** So when a refutation lands, the next action is not the cure. **It is the sweep: search the tree for the shape, and report the COUNT before you price the cure.** A cure funded against the named site is priced against a number nobody...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:3754

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev, archive/scripts, dev/ARCHIVE.md:
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 214.570)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 213.692)
- CANDIDATE archive/dev/JOURNAL.md  (score 208.366)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 195.154)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 186.039)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 63.683)
- CANDIDATE dev/literature/digest.md  (score 47.913)
- CANDIDATE dev/literature/geology.md  (score 38.994)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 38.376)
- CANDIDATE dev/literature/terms-2026-08.md  (score 30.428)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
