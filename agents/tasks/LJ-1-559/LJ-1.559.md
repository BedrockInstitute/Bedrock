# LJ-1.559: domAt again, in the smallest frame that can hold it

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-559/Probe559.agda`:

    domAt-at-carve : <the domAt conjunct of InjCode, over the rank carve,
                      with Q instantiated>

the same obligation `[LJ-1.541]` carried
(`agents/tasks/LJ-1-541/LJ-1.541.md`). Land nothing in `src/`.

**`[LJ-1.541]` TIMED OUT, AND SO DID `[LJ-1.547]` FIVE TIMES.** Both closed on
`sys-timeout-escalate`, and `[LJ-1.547]` reached `attempt_max`. **Neither is a
mathematical refutation and I do not treat them as one.** `domAt` is the fourth
of `InjCode`'s four conjuncts (`src/L/Cardinal.lagda.md:226`); the other three
are built (`[LJ-1.524]`, `[LJ-1.529]`, `[LJ-1.531]`), so this one term is what
stands between the coding leg and an assembled `InjCode`.

**THE CURE IS MEASURED AND IT IS IN THE ARCHIVE.** `[LJ-1.75]` gave each partial
only the facts its rows use and got **41.6 percent cheaper for a 37.7 percent
smaller telescope, better than proportional**
(`archive/dev/LJ-dispatch-index.md:142`). **That is the method this brief
orders.** `[LJ-1.545]` separately measured the heap linear in field count with a
per-family constant, so the cost is in what you import, not in how much you
prove.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-559/Probe559.agda::domAt-at-carve"]

## SCOPE (write)
- agents/tasks/LJ-1-559/Probe559.agda
- agents/tasks/LJ-1-559/lj-1.559-report.md
- agents/tasks/LJ-1-559/review-of-domAt.md
- agents/tasks/LJ-1-559/runs/

## PREMISES

1. `[LJ-1.541]` carried this obligation. Basis: agents/tasks/LJ-1-541/LJ-1.541.md:1
2. It closed on a timeout, not a refutation. Basis: dev/pod/transitions/2026-08.jsonl:2996
3. `[LJ-1.547]` reached `attempt_max` on timeouts. Basis: dev/pod/transitions/2026-08.jsonl:3003
4. `domAt` is `InjCode`'s second conjunct by position. Basis: src/L/Cardinal.lagda.md:226
5. `[LJ-1.524]` closed `svAt`. Basis: agents/tasks/LJ-1-524/lj-1.524-report.md:1
6. `[LJ-1.529]` closed the range clause. Basis: agents/tasks/LJ-1-529/lj-1.529-report.md:1
7. `[LJ-1.531]` proved the rank injective. Basis: agents/tasks/LJ-1-531/lj-1.531-report.md:1
8. `[LJ-1.537]` built `approx-carve` and pinned its type. Basis: agents/tasks/LJ-1-537/lj-1.537-report.md:16
9. `[LJ-1.75]` measured trimming better than proportional. Basis: archive/dev/LJ-dispatch-index.md:142
10. `[LJ-1.545]` measured the heap linear in field count. Basis: agents/tasks/LJ-1-545/lj-1.545-report.md:1
11. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
12. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

Three of `InjCode`'s four conjuncts, and `approx-carve` under it. **The fourth
has been attempted and never finished.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE IMPORT LIST.** Before you prove anything,
write the smallest set of imports under which `domAt-at-carve` can even be
STATED, and record its typecheck time on an empty body. **Report that number.**
It is the floor, and if the floor is already near the timeout the obligation
cannot be met in this frame and you say so at once.

**BUILD IT IN THE TRIMMED FRAME AND NOWHERE ELSE.** Do not import
`[LJ-1.524]`'s, `[LJ-1.529]`'s or `[LJ-1.531]`'s probes for convenience: those
are the other three conjuncts and this brief does not assemble them.
**`[LJ-1.547]` timed out five times trying to hold four conjuncts at once.**

**NOTHING OF `[LJ-1.541]` SURVIVED, SO THERE IS NOTHING TO REUSE.** Its
transition record names a probe, a report and seven bisection files as changed
(`dev/pod/transitions/2026-08.jsonl:2996`), and `agents/tasks/LJ-1-541/runs/` is
EMPTY in this tree. It ran 1800.01 seconds on its last attempt with
`heap_wall: false`, so it was time and not memory. **Start cold and do not go
looking for its bisection.**

**MEASURE AS YOU GO AND WRITE THE REPORT AS A SKELETON FIRST.** If you are cut
off, a report with the floor number and a partial account is worth much more
than nothing, which is what the two predecessors left.

**DO NOT ASSEMBLE `InjCode`. DO NOT TOUCH B9.** AD12 gives this brief one
obligation. Assembly is a separate task and it will be re-queued only after this
one closes.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE FLOOR`.** The minimal import set, its
typecheck time on an empty body, and the time of the finished term. **Three
numbers, measured.**

**REQUIRED REPORT SECTION `## WHY THE PREDECESSORS RAN LONG`.** Three sentences.
You have no report from either. **Reason from your own floor number and say so**,
and say whether an assembly of all four conjuncts looks affordable at the
numbers you measured.

ESTIMATE: about 130 lines in the probe, of which the obligation is about 35.
BASIS: the three sibling conjuncts. **The time, not the line count, is the risk
here, and that is why the floor is measured first.** Comparables are of SHAPE
and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the floor itself.

    -- domAt-at-carve, STATED with a hole, in the trimmed frame, timed

**Write it FIRST and time it.** This is the one W3 this week whose value is a
number rather than a type. ESTIMATE: about 15 lines; the time is what you are
measuring and I do not estimate it.

## WHAT GO AND NO-GO EACH EARN

**A GO GIVES THE CODING LEG ITS FOURTH CONJUNCT**, and B9 becomes reachable for
the first time since `[LJ-1.548]` stopped on a missing predecessor.

**A NO-GO THAT REPORTS THE FLOOR IS STILL A RESULT**, because no number exists
today for what this term costs, and two dispatches have been spent finding that
out the expensive way.

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
  changed_files_none = ["agents/tasks/LJ-1-559/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-559/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-559/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-559/Probe559.agda"]
  changed_files_none = ["agents/tasks/LJ-1-559/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-559/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 219.328)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 200.116)
- CANDIDATE archive/dev/JOURNAL.md  (score 178.202)
- CANDIDATE dev/ARCHIVE.md  (score 164.951)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 151.995)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 44.823)
- CANDIDATE dev/literature/digest.md  (score 44.267)
- CANDIDATE dev/literature/devlin-II5.md  (score 43.739)
- CANDIDATE dev/literature/geology.md  (score 36.087)
- CANDIDATE dev/literature/terms-2026-08.md  (score 35.938)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
