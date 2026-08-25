# LJ-1.567: the Step formula for col, which its predecessor named as the only task in its chapter

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-567/Probe567.agda`:

    col-step : <`RecShape` instantiated at `dom = Square.sqL κ`, with `Step`
                saying `z = ⋃ { sucV (f r) : r ≺ c }`>

Land nothing in `src/`.

**`[LJ-1.556]` IS A NO-GO AND IT NAMED THIS TASK ITSELF.** Its
`## WHAT THE NEXT BRIEF NEEDS FROM THIS ONE`
(`agents/tasks/LJ-1-556/lj-1.556-report.md:298`) says, in its own words:

1. **"DO NOT RE-DISPATCH THE BRIEF'S TYPE. It is under-hypothesized."**
2. **"THE FIRST PAYABLE PIECE IS THE `Step` FORMULA FOR `col`, AND IT IS ONE
   OBLIGATION."** Instantiate `RecShape` (`src/L/Coding/Sequence.lagda.md:281`)
   at `dom = Square.sqL κ` with `Step` saying `z = ⋃ { sucV (f r) : r ≺ c }`.
   **"The order enters as a FORMULA, so section 2's device carries it and no
   order-as-a-set is needed. That is a task, and it is the only part of this
   chapter that is."**
3. Sections 1 and 2 of `Probe556.agda` are **green Agda a chapter can copy**:
   the product, its two readings, and the pattern for turning a condition on
   the components into a formula and then into a set.

**I AM TAKING ITS RECOMMENDATION AND I SAY SO.** My own brief's type was
under-hypothesized, which is why `[LJ-1.556]` stopped; **I am not re-dispatching
it.**

**AND NOTHING HERE MAY BE FUNDED AGAINST THE 775-LINE FIGURE.** `[LJ-1.556]`
says so in its own item 4, and the archive's number is for an old tree.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-567/Probe567.agda::col-step"]

## SCOPE (write)
- agents/tasks/LJ-1-567/Probe567.agda
- agents/tasks/LJ-1-567/lj-1.567-report.md
- agents/tasks/LJ-1-567/review-of-col-step.md
- agents/tasks/LJ-1-567/runs/

## PREMISES

1. `[LJ-1.556]` is a NO-GO and names this as the only payable piece. Basis: agents/tasks/LJ-1-556/lj-1.556-report.md:298
2. It calls the brief's own type under-hypothesized. Basis: agents/tasks/LJ-1-556/lj-1.556-report.md:298
3. Its sections 1 and 2 are green and copyable. Basis: agents/tasks/LJ-1-556/Probe556.agda:1
4. `RecShape` takes a `Step` formula. Basis: src/L/Coding/Sequence.lagda.md:281
5. `SquareLaw` is imported by `Cardinal`. Basis: src/L/Cardinal.lagda.md:22
6. The chapter calls its injection type AMBIENT. Basis: src/L/Cardinal.lagda.md:46
7. `[LJ-1.552]` named the square law inside L as a decomposition step. Basis: agents/tasks/LJ-1-552/Probe552.agda:295
8. `[LJ-1.557]` is GO and built the pointwise internal code. Basis: agents/tasks/LJ-1-557/lj-1.557-report.md:1
9. `[LJ-1.51]` landed `SquareLaw` as a 775-line master. Basis: archive/dev/LJ-dispatch-index.md:100
10. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
11. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
12. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

`Probe556.agda` sections 1 and 2, green: the product, its two readings, and the
formula-to-set pattern. **The `Step` formula itself is delivered nowhere.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE RE-READ OF `Probe556.agda`.** Read its
sections 1 to 4 and say at `file:line` what is already green and what
`SquareStep` (its section 4) asks for. **Copy what is green rather than
rebuilding it**, and say in the report which lines you took.

**THE ORDER ENTERS AS A FORMULA AND NOT AS A SET.** `[LJ-1.556]` measured that.
**If you find yourself building an order-as-a-set, stop and say so**: it means
its finding does not hold at your frame and that is a result.

**`RecShape`'S `Step` HAS THREE `Fin n` ARGUMENTS** (`src/L/Coding/Sequence.lagda.md:281`).
Say what each is at your instantiation before you write the formula.

**DO NOT BUILD THE SQUARE LAW AND DO NOT RE-DISPATCH `[LJ-1.556]`'S TYPE.** AD12
gives this brief one obligation, and its predecessor explicitly warned against
the wider one.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## WHAT I COPIED`.** The lines taken from
`Probe556.agda`, at `file:line`, and what you had to change.

**REQUIRED REPORT SECTION `## WHAT SQUARESTEP STILL WANTS`.** Three sentences.
Given `col-step`, **say what remains before `SquareStep` is payable.** Do not
build it.

ESTIMATE: about 160 lines in the probe, of which the obligation is about 40.
BASIS: `[LJ-1.556]`'s sections 1 and 2 are green and this adds one formula.
Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is `RecShape` at this `dom`.

    -- RecShape instantiated at dom = Square.sqL κ, TYPE ONLY, Step abstract

**Write it FIRST and typecheck it ALONE.** If `RecShape` will not instantiate
there, the formula has nowhere to go and you say so before spending the
estimate. ESTIMATE: about 15 lines, under 2 minutes.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS THE ONLY PIECE ITS PREDECESSOR JUDGED PAYABLE**, and it is the first
step of the only route to `Codes δ κ` that any task has found.

**A NO-GO SAYS THE SQUARE LAW HAS NO INTERNAL ROUTE AT ALL**, which would close
`[LJ-1.552]`'s decomposition and force the mathematician to look elsewhere.

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
  changed_files_none = ["agents/tasks/LJ-1-567/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-567/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-567/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-567/Probe567.agda"]
  changed_files_none = ["agents/tasks/LJ-1-567/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-567/review-of-*.md"]

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
- CANDIDATE archive/dev/JOURNAL.md  (score 172.074)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 157.669)
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 155.835)
- CANDIDATE archive/dev/DD-archived.md  (score 141.085)
- CANDIDATE dev/ARCHIVE.md  (score 140.561)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 52.672)
- CANDIDATE dev/literature/terms-2026-08.md  (score 48.435)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 40.806)
- CANDIDATE dev/literature/digest.md  (score 39.163)
- CANDIDATE dev/literature/geology.md  (score 29.036)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
