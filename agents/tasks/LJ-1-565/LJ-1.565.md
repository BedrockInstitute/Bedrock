# LJ-1.565: StageHigh again, because the door turned out to be open

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-565/Probe565.agda`:

    stage-high : <the statement `[LJ-1.536]` carried>
      (`agents/tasks/LJ-1-536/Probe536.agda:350-352`)

Land nothing in `src/`.

**`[LJ-1.536]` STOPPED AT A DOOR THAT `[LJ-1.562]` THEN FOUND OPEN.** Its stop
said `𝒟ₒ-intro` needs `AtStage`, and that `AtStage` has two hypotheses: the
formula is Δ₀, and every constant in it is a member of the stage
(`agents/tasks/LJ-1-536/review-of-StageHigh.md`).

**BOTH ARE PAYABLE AT THAT FORMULA, MEASURED.** `[LJ-1.562]` is GO and reports:
**"it is Δ₀ by two constructors, and `[LJ-1.536]` already typechecked the
witness it never reported"**, `Δ₀-adjoin = δ-∨ δ-∈ δ-≐` at
`agents/tasks/LJ-1-536/runs/W3.agda:156-157`, so **"BOTH of `AtStage`'s
hypotheses are payable for the formula that task actually needed and the door
is not what blocks it."**

**SO THE STOP IS NOT REFUTED AND IT IS NOT UPHELD: ITS STATED REASON IS PAID.**
Whatever blocks `StageHigh`, it is not the door. **Find out what does, or build
the term.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-565/Probe565.agda::stage-high"]

## SCOPE (write)
- agents/tasks/LJ-1-565/Probe565.agda
- agents/tasks/LJ-1-565/lj-1.565-report.md
- agents/tasks/LJ-1-565/review-of-stage-high.md
- agents/tasks/LJ-1-565/runs/

## PREMISES

1. `[LJ-1.536]` is a NO-GO and its obligation is stated at its probe. Basis: agents/tasks/LJ-1-536/Probe536.agda:350
2. Its stop names `AtStage`'s two hypotheses. Basis: agents/tasks/LJ-1-536/review-of-StageHigh.md:11
3. `[LJ-1.562]` is GO and reports both payable at that formula. Basis: agents/tasks/LJ-1-562/lj-1.562-report.md:1
4. The Δ₀ witness is typechecked in `[LJ-1.536]`'s own runs. Basis: agents/tasks/LJ-1-536/runs/W3.agda:156
5. `𝒟ₒ-intro` is the one route into a stage. Basis: src/L/Constructible.lagda.md:301
6. `defSet` reads under the world's inner satisfaction. Basis: src/L/Definability.lagda.md:111
7. `AtStage` is the one external-to-inner bridge. Basis: src/L/Axioms/Separation.lagda.md:119
8. Its Δ₀ hypothesis sits at a stated line. Basis: src/L/Axioms/Separation.lagda.md:199
9. `[LJ-1.520]` built a graded formula with a nine-row cost table. Basis: agents/tasks/LJ-1-520/lj-1.520-report.md:1
10. `[LJ-1.522]` paid its one unpaid row. Basis: agents/tasks/LJ-1-522/lj-1.522-report.md:1
11. A stop is a deliverable. Basis: AGENTS.md:43
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

`[LJ-1.536]`'s probe, its `runs/W3.agda` with a typechecked Δ₀ witness, and
`[LJ-1.562]`'s measurement that both door hypotheses are payable. **All of it is
committed and all of it is yours to read.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE RE-READ.** Read `[LJ-1.536]`'s probe and
its `runs/`, then say at `file:line` **exactly which step it could not take**,
now that the door is known to be payable. **If its stop names a second reason
beyond the door, say so: I did not read the whole file and I do not claim it
names only one.**

**DO NOT ASSUME `[LJ-1.562]`'S FINDING TRANSFERS TO YOUR FORMULA.** It measured
the formula `[LJ-1.536]` actually needed. **If you find yourself needing a
different formula, its Δ₀-ness is unmeasured and you must measure it.** A
measured cure does not transfer by analogy.

**IF THE REAL BLOCKER IS AN UNBOUNDED SEARCH, SAY SO AND STOP.** `[LJ-1.560]` is
running on exactly that question and this brief must not duplicate it. **Naming
it here would CONFIRM from a second site that the two legs share one wall**,
which is worth more than a partial build.

**DO NOT BUILD A REFLECTION PRINCIPLE.** AD12 gives this brief one obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## WHAT ACTUALLY BLOCKED IT`.** One paragraph with
`file:line`. If you built the term, say what `[LJ-1.536]` was missing; if you
did not, say what is left now that the door is paid.

**REQUIRED REPORT SECTION `## THE UNREPORTED WITNESS`.** Two sentences.
`[LJ-1.536]` typechecked `Δ₀-adjoin` and did not report it. **Say whether
anything else in its `runs/` is delivered work that its report omits.** That is
a check on the campaign's record-keeping and it costs one read.

ESTIMATE: about 180 lines in the probe, of which the obligation is about 40.
BASIS: `[LJ-1.536]`'s own probe. Comparables are of SHAPE and nothing may be
funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is `AtStage` applied at this formula, with both hypotheses supplied.

    -- AtStage at [LJ-1.536]'s formula, both hypotheses fed, TYPE ONLY

**Write it FIRST and typecheck it ALONE.** If it will not apply even with both
hypotheses in hand, `[LJ-1.562]`'s finding does not reach this site and you say
so at once. ESTIMATE: about 15 lines, under 2 minutes.

## WHAT GO AND NO-GO EACH EARN

**A GO UNSTICKS THE CONDENSATION LEG'S ROW SIX**, which has now cost three
attempts and an adversarial review.

**A NO-GO THAT NAMES AN UNBOUNDED SEARCH CONFIRMS THE SHARED WALL FROM A SECOND
SITE**, which is exactly what `[LJ-1.561]` is trying to establish by argument.

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
  changed_files_none = ["agents/tasks/LJ-1-565/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-565/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-565/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-565/Probe565.agda"]
  changed_files_none = ["agents/tasks/LJ-1-565/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-565/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 145.230)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 135.752)
- CANDIDATE archive/dev/JOURNAL.md  (score 134.429)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 111.897)
- CANDIDATE dev/ARCHIVE.md  (score 111.774)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 43.145)
- CANDIDATE dev/literature/devlin-II5.md  (score 37.210)
- CANDIDATE dev/literature/digest.md  (score 29.126)
- CANDIDATE dev/literature/terms-2026-08.md  (score 27.588)
- CANDIDATE dev/literature/geology.md  (score 27.571)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
