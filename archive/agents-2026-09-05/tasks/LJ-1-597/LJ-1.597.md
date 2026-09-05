# LJ-1.597: the graph of step, which is the whole condition

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-597/Probe597.agda`:

    step-graph : <a `Formula` expressing the graph of `stage-card-upper`'s
                  `step`, with its reading in both directions>

Land nothing in `src/`. **Do not apply it to anything.**

**`src/L/Recursion.lagda.md` SAYS THE GRAPH IS THE ONLY CONDITION, IN ITS OWN
PROSE.** `[LJ-1.594]` found it while refuting my premise:

> "A recursive definition is internalizable when its graph is expressible, and
> nothing about the recursion's shape, its depth, its order of descent, or the
> complexity of its clauses appears in the condition"
> (`src/L/Recursion.lagda.md:259-261`), under the title "Recursive definitions
> are internalizable" (`:1`).

**`stage-card-upper = ∈-induction step`** (`src/L/StageCardinal.lagda.md:566`).
**So the whole question for that object is one formula, and this brief is only
that formula.**

**`[LJ-1.596]` IS AIMING AT THE ROW AND THIS BRIEF AT THE CONDITION.** They are
deliberately parallel and neither waits on the other. **If `[LJ-1.596]` reports
the machine does not fit, this formula is still the thing every other route has
wanted**, because `[LJ-1.568]` proved that coding an injection IS describing it,
necessary and sufficient (`agents/tasks/LJ-1-568/Probe568.agda:252`, `:377`).

**FOUR TASKS HAVE FAILED TO PRODUCE A FORMULA FOR THIS FAMILY OF OBJECTS**:
`[LJ-1.533]`, `[LJ-1.549]`, `[LJ-1.552]`, `[LJ-1.584]`. **What is different here
is the SCOPE: a graph of one step, not a description of a whole injection.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-597/Probe597.agda::step-graph"]

## SCOPE (write)
- agents/tasks/LJ-1-597/Probe597.agda
- agents/tasks/LJ-1-597/lj-1.597-report.md
- agents/tasks/LJ-1-597/review-of-step-graph.md
- agents/tasks/LJ-1-597/runs/

## PREMISES

1. `Recursion`'s title states the claim. Basis: src/L/Recursion.lagda.md:1
2. Its condition is the graph alone. Basis: src/L/Recursion.lagda.md:259
3. `[LJ-1.594]` found it while refuting my premise. Basis: agents/tasks/LJ-1-594/review-of-pairing-suffices.md:79
4. `stage-card-upper` is `∈-induction step`. Basis: src/L/StageCardinal.lagda.md:566
5. `[LJ-1.568]` proved coding is describing, sufficient. Basis: agents/tasks/LJ-1-568/Probe568.agda:252
6. And necessary. Basis: agents/tasks/LJ-1-568/Probe568.agda:377
7. `[LJ-1.584]` is a NO-GO on describing the whole injection. Basis: agents/tasks/LJ-1-584/review-of-stage-bound-definable.md:12
8. `[LJ-1.533]` refuted a code for an arbitrary ambient injection. Basis: agents/tasks/LJ-1-533/lj-1.533-report.md:1
9. `hasSeparationL` takes an arbitrary formula. Basis: src/L/Axioms/Full.lagda.md:144
10. `defSet` is `𝒟ₒ` in that module. Basis: src/L/StageCardinal.lagda.md:400
11. The least-element selection is the ordinal order. Basis: src/L/StageCardinal.lagda.md:258
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

An internalization chapter whose condition is one formula, and four measured
failures at describing whole injections. **No graph formula.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS `step` ITSELF.** Read `step` at
`src/L/StageCardinal.lagda.md` and say at `file:line` **what it takes, what it
returns, and what it calls.** A graph is a relation between its input and its
output; you cannot write one before you have read both.

**READ THE CHAPTER'S ACTUAL CONDITION, NOT ITS PROSE.** `[LJ-1.594]` quoted the
sentence. **Re-ascribe the type the chapter really requires and say whether it
agrees with the sentence.** If the type asks for more than the prose does, that
is the finding.

**TWO OF THE THREE NEIGHBOURING INGREDIENTS ARE ALREADY INTERNAL**, measured by
`[LJ-1.584]`: `defSet` is `𝒟ₒ` (`src/L/StageCardinal.lagda.md:400-401`) and the
least-element selection is the ordinal order (`:258-259`). **Use them rather
than rebuilding them.**

**DO NOT APPLY THE FORMULA AND DO NOT BUILD B9.** `[LJ-1.596]` is doing that.
AD12 gives this brief one obligation, and the point of splitting is that the
formula is separately checkable.

**IF `step` CALLS SOMETHING WITH NO FORMULA, NAME IT AND STOP.** That is the
deliverable in the NO-GO case, and it would be the first time this campaign has
named the atom rather than the whole object.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## WHAT step CALLS`.** Every call at `file:line`, each
marked as having a formula or not.

**REQUIRED REPORT SECTION `## THE GRAPH`.** The formula, its arity, and both
readings, or the named atom that blocked it.

ESTIMATE: about 190 lines in the probe, of which the obligation is about 50.
BASIS: `[LJ-1.568]` built `Def` and its two directions at a comparable size.
Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is `step`'s own type.

    -- stage-card-upper's `step`, re-ascribed alone, TYPE ONLY

**Write it FIRST and typecheck it ALONE.** ESTIMATE: about 12 lines, under 90
seconds.

## WHAT GO AND NO-GO EACH EARN

**A GO SUPPLIES THE ONE CONDITION THE INTERNALIZATION CHAPTER ASKS FOR**, and
`[LJ-1.596]` or its successor can spend it immediately.

**A NO-GO THAT NAMES THE ATOM WITHOUT A FORMULA IS THE MOST USEFUL STOP THIS
LINE COULD PRODUCE.** Four tasks have said "the injection has no formula". None
has said which piece of it does not.

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
  changed_files_none = ["agents/tasks/LJ-1-597/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-597/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-597/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-597/Probe597.agda"]
  changed_files_none = ["agents/tasks/LJ-1-597/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-597/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 170.374)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 167.304)
- CANDIDATE archive/dev/JOURNAL.md  (score 150.943)
- CANDIDATE dev/ARCHIVE.md  (score 141.349)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 126.736)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 57.551)
- CANDIDATE dev/literature/devlin-II5.md  (score 51.716)
- CANDIDATE dev/literature/digest.md  (score 45.098)
- CANDIDATE dev/literature/terms-2026-08.md  (score 38.549)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 30.610)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
