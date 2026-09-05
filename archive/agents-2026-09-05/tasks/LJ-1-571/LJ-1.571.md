# LJ-1.571: row 2, SqAt, and the collection that is not inhabited

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-571/Probe571.agda`:

    sqat-or-what-it-wants :
      <`SqAt` at the frame `gch-from-five` calls it, or a term naming
       precisely the input it lacks>

`SqAt` is `(κ : SL.S) → IsOrd (fst κ) → SqLaw (fst κ)`
(`agents/tasks/LJ-1-550/Probe550.agda:310-311`). Land nothing in `src/`.

**THIS IS ROW 2 OF THE FIVE-ROW BILL.** `[LJ-1.564]`'s `gch-from-five`
(`agents/tasks/LJ-1-564/Probe564.agda:456-463`) machine-checks that
`GCHStatement` follows from exactly five rows, and this is one of them.

**THE TREE ALREADY SAYS SOMETHING ABOUT WHY IT IS HARD, IN ITS OWN WORDS.**
`src/L/StageBound.lagda.md:42` reads **"Collection of truncated squares to a
truncated family. Not inhabited."** That is a sentence about `SqCollect`, and it
is the only note in the tree that bears on this row.

**THIS IS NOT `[LJ-1.567]`'S TASK AND YOU MUST NOT DUPLICATE IT.**
`[LJ-1.567]` builds `col-step`, one `Step` formula inside the INTERNAL square
law that `[LJ-1.556]` named. **This brief is about `SqAt` as `gch-from-five`
consumes it**, which is `SqLaw` at an ordinal and may want something else
entirely. **Say in your D-10 whether the two meet.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-571/Probe571.agda::sqat-or-what-it-wants"]

## SCOPE (write)
- agents/tasks/LJ-1-571/Probe571.agda
- agents/tasks/LJ-1-571/lj-1.571-report.md
- agents/tasks/LJ-1-571/review-of-sqat.md
- agents/tasks/LJ-1-571/runs/

## PREMISES

1. `[LJ-1.564]` is GO and its bill is five rows. Basis: agents/tasks/LJ-1-564/Probe564.agda:456
2. `SqAt` is row 2. Basis: agents/tasks/LJ-1-550/Probe550.agda:310
3. `StageBound` says `SqCollect` is not inhabited. Basis: src/L/StageBound.lagda.md:42
4. `SquareLaw` is imported by `Cardinal`. Basis: src/L/Cardinal.lagda.md:22
5. The chapter calls its injection type AMBIENT. Basis: src/L/Cardinal.lagda.md:46
6. `SquareLaw` is imported by `InjChain`. Basis: src/L/InjChain.lagda.md:23
7. `[LJ-1.556]` is a NO-GO and named `col-step` as the only payable piece. Basis: agents/tasks/LJ-1-556/lj-1.556-report.md:298
8. Its sections 1 and 2 are green and copyable. Basis: agents/tasks/LJ-1-556/Probe556.agda:1
9. `[LJ-1.51]` landed `SquareLaw` as a 775-line master. Basis: archive/dev/LJ-dispatch-index.md:100
10. `[LJ-1.560]` is GO and its obligation was an instantiation. Basis: agents/tasks/LJ-1-560/lj-1.560-report.md:1
11. A stop is a deliverable. Basis: AGENTS.md:43
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

An ambient square law used by two chapters, a note saying one collection is not
inhabited, and `[LJ-1.556]`'s green sections 1 and 2. **No term of `SqAt`'s
shape.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS WHETHER `SqAt` IS AMBIENT OR INTERNAL.** Read
`SqLaw` and say at `file:line` which carrier its injection lives at. **If it is
ambient, the existing `L.Ordinal.SquareLaw` may supply it directly and this task
is short.** If it is internal, say so and then say whether `[LJ-1.567]`'s
`col-step` is on its path.

**READ `src/L/StageBound.lagda.md` AROUND LINE 42 BEFORE YOU BELIEVE THE NOTE.**
A comment is not a measurement. **Say whether `SqCollect` is what `SqAt` needs
at all**, or whether the note is about a neighbour.

**IF THE AMBIENT LAW SUPPLIES IT, SAY SO AND FINISH EARLY.** `[LJ-1.560]` found
its obligation was an instantiation and its estimate far too high. **That is a
good outcome and you should report it as one.**

**DO NOT BUILD `col-step` AND DO NOT RE-DISPATCH `[LJ-1.556]`'S TYPE**, which
its own report calls under-hypothesized. AD12 gives this brief one obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## AMBIENT OR INTERNAL`.** Which, at `file:line`, and
what follows from it.

**REQUIRED REPORT SECTION `## DOES IT MEET LJ-1.567`.** Three sentences saying
whether the internal square law work is on this row's path or beside it.

ESTIMATE: about 150 lines in the probe, of which the obligation is about 35.
**If the ambient law supplies it, far less, and I would rather be wrong this way
than fund a rebuild.** Comparables are of SHAPE and nothing may be funded
against them.

## W3, THE WIDEST UNMEASURED TERM

It is `SqLaw`'s own carrier.

    -- SqLaw (fst κ), unfolded one step, TYPE ONLY

**Write it FIRST and typecheck it ALONE.** It decides the whole shape of the
task. ESTIMATE: about 10 lines, under 60 seconds.

## WHAT GO AND NO-GO EACH EARN

**A GO TAKES THE BILL FROM FIVE ROWS TO FOUR.**

**A NO-GO THAT SAYS WHICH INPUT `SqAt` LACKS TELLS THE MATHEMATICIAN WHETHER THE
INTERNAL SQUARE LAW IS ON THE CRITICAL PATH**, which decides whether
`[LJ-1.567]`'s line of work continues.

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
  changed_files_none = ["agents/tasks/LJ-1-571/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-571/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-571/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-571/Probe571.agda"]
  changed_files_none = ["agents/tasks/LJ-1-571/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-571/review-of-*.md"]

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
- CANDIDATE archive/dev/JOURNAL.md  (score 163.495)
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 159.494)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 158.604)
- CANDIDATE archive/dev/DD-archived.md  (score 137.026)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 131.359)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 54.258)
- CANDIDATE dev/literature/devlin-II5.md  (score 50.176)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 35.778)
- CANDIDATE dev/literature/digest.md  (score 34.239)
- CANDIDATE dev/literature/terms-2026-08.md  (score 32.015)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
