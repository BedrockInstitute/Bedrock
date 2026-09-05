# LJ-1.589: thread the infinity clause through row 5, as its predecessor advised

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-589/Probe589.agda`:

    row5-carries-infinity :
      <row 5's consumer, restated so that it carries the infinity clause
       `[LJ-1.581]`'s `SquareStepInf` needs>

Land nothing in `src/`.

**`[LJ-1.581]` IS A NO-GO, UPHELD, AND IT NAMED TWO REOPENERS AND RECOMMENDED
THE SECOND. I AM TAKING ITS RECOMMENDATION.** Its own words:

> **"THREAD THE INFINITY CLAUSE THROUGH ROW 5 FIRST**, because the consumer does
> not carry it today (section 5 above). That is a smaller task than the square
> law, and it decides the shape of the square-law brief rather than following
> it."

**THE OTHER REOPENER IS `SquareStepInf`** (`agents/tasks/LJ-1-581/Probe581.agda:427`),
**"or the same type with the `γ∉ω`-plus-`numerals` spelling that
`src/L/CodedShift.lagda.md:37-39` uses. Nothing in this file inhabits it and
nothing refutes it."** **This brief does NOT fund that**, because its
predecessor says the spelling is not yet decided and this task decides it.

**AND THE TROPHY ALREADY EXCLUDES ω.** `GCHStatement`'s fourth hypothesis is
`(⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)` (`src/L/GCH.lagda.md:64`). **So the clause may
already be available at the consumer and simply not threaded.** That is the
cheap outcome and you should test it first.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-589/Probe589.agda::row5-carries-infinity"]

## SCOPE (write)
- agents/tasks/LJ-1-589/Probe589.agda
- agents/tasks/LJ-1-589/lj-1.589-report.md
- agents/tasks/LJ-1-589/review-of-row5-carries-infinity.md
- agents/tasks/LJ-1-589/runs/

## PREMISES

1. `[LJ-1.581]` is a NO-GO and its critic upheld it. Basis: agents/tasks/LJ-1-581/review-of-LJ-1-581-1.md:1
2. It recommends threading the infinity clause first. Basis: agents/tasks/LJ-1-581/review-of-pairs-into-kappa.md:1
3. `SquareStepInf` is stated at its probe. Basis: agents/tasks/LJ-1-581/Probe581.agda:427
4. `CodedShift` uses a `γ∉ω`-plus-`numerals` spelling. Basis: src/L/CodedShift.lagda.md:37
5. `GCHStatement`'s fourth hypothesis excludes ω. Basis: src/L/GCH.lagda.md:64
6. Row 5 is `SuccIntoPower`. Basis: agents/tasks/LJ-1-558/Probe558.agda:99
7. `[LJ-1.574]` named the square-law code as row 5's step 2. Basis: agents/tasks/LJ-1-574/review-of-succ-assignment-definable.md:90
8. `[LJ-1.564]`'s bill is five rows. Basis: agents/tasks/LJ-1-564/Probe564.agda:456
9. `SuccCardL`'s fourth component is a leastness clause. Basis: src/L/GCH.lagda.md:47
10. `[LJ-1.585]` proved a hypothesis cannot be stated more widely than its function. Basis: agents/tasks/LJ-1-585/Probe585.agda:163
11. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
12. A stop is a deliverable. Basis: AGENTS.md:43
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

A named square-law step that wants an infinity clause, and a consumer that does
not carry one. **No thread between them.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE TWO SPELLINGS.** `[LJ-1.581]` names two:
its own `SquareStepInf`, and the `γ∉ω`-plus-`numerals` spelling at
`src/L/CodedShift.lagda.md:37-39`. **Say at `file:line` what each says and
whether they are interderivable.** **Pick one and say why**: that choice is this
task's main deliverable and it shapes the square-law brief that follows.

**TRY THE CHEAP ROUTE FIRST.** `GCHStatement`'s fourth hypothesis already
excludes ω. **Say whether it propagates to the site row 5 spends at.** If it
does, the thread is short and you should report that and finish early, the way
`[LJ-1.560]` did when its obligation turned out to be an instantiation.

**DO NOT BUILD `SquareStepInf` AND DO NOT BUILD THE SQUARE LAW.** `[LJ-1.581]`
says the shape is undecided and this task decides it. AD12 gives this brief one
obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE SPELLING I CHOSE`.** Which, why, and whether
the two are interderivable, each at `file:line`.

**REQUIRED REPORT SECTION `## WHAT THE SQUARE-LAW BRIEF SHOULD SAY`.** Three
sentences. **This is the deliverable `[LJ-1.581]` asked for**: given the
threading, say what type the square-law task should carry. Do not build it.

ESTIMATE: about 150 lines in the probe, of which the obligation is about 35.
BASIS: `[LJ-1.581]` worked the same site. **Its own words are that this is
smaller than the square law.** Comparables are of SHAPE and nothing may be
funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is whether the trophy's ω-exclusion reaches the consumer.

    -- GCHStatement's fourth hypothesis, propagated to row 5's spend site,
    -- TYPE ONLY

**Write it FIRST and typecheck it ALONE.** If it reaches, the task is short.
ESTIMATE: about 12 lines, under 90 seconds.

## WHAT GO AND NO-GO EACH EARN

**A GO DECIDES THE SHAPE OF THE SQUARE-LAW BRIEF**, which is the largest single
object left on the bill, and it does so for a fraction of that object's cost.

**A NO-GO SHOWING THE CLAUSE CANNOT BE THREADED SAYS ROW 5 NEEDS THE SQUARE LAW
IN ITS WIDER FORM**, which is a price the mathematician must know before
funding it.

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
  changed_files_none = ["agents/tasks/LJ-1-589/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-589/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-589/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-589/Probe589.agda"]
  changed_files_none = ["agents/tasks/LJ-1-589/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-589/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 177.250)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 171.972)
- CANDIDATE archive/dev/JOURNAL.md  (score 163.650)
- CANDIDATE archive/dev/PLAN-archived.md  (score 135.756)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 134.714)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/terms-2026-08.md  (score 54.674)
- CANDIDATE dev/literature/devlin-II5.md  (score 50.421)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 47.323)
- CANDIDATE dev/literature/geology.md  (score 44.016)
- CANDIDATE dev/literature/digest.md  (score 36.475)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
