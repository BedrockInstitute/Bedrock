# LJ-1.601: measure the finite base, which no task has measured

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-601/Probe601.agda`:

    finite-base-measured : <the `Tally` question `[LJ-1.597]` named, stated and
                            settled at this carrier>

**Take the exact statement from `[LJ-1.597]`'s `## WHAT WOULD REOPEN IT`, item
2.** I do not restate it here, because that task measured it and I did not. Land
nothing in `src/`.

**`[LJ-1.597]` IS A NO-GO, UPHELD, AND ITS SECOND REOPENER IS AN UNMEASURED
FACT.** Its words: **"MEASURE THE FINITE BASE. No task has measured whether the
`Tally`..."** — read the rest there and take it verbatim
(`agents/tasks/LJ-1-597/review-of-step-graph.md:154`).

**WHY IT IS WORTH A DISPATCH OF ITS OWN.** Every other open piece on this object
is a construction. **This one is a measurement**, and it is the only item on
either reopener list that nobody has ever taken. A measurement that costs one
task can retire or re-price a construction that costs a chapter.

**WHAT THE OBJECT IS, SO YOU KNOW WHERE YOU ARE.** `step` is one equation
(`src/L/StageCardinal.lagda.md:561-562`) and its value equation is
`fst (sq α α∈suc infα) (m , cnt m φ) ≡ y`. `sq` is a bare module parameter
(`:17-19`) with injectivity and no formula. **Three tasks have now reached that
same parameter from three directions**: `[LJ-1.572]`, `[LJ-1.594]`, `[LJ-1.597]`.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-601/Probe601.agda::finite-base-measured"]

## SCOPE (write)
- agents/tasks/LJ-1-601/Probe601.agda
- agents/tasks/LJ-1-601/lj-1.601-report.md
- agents/tasks/LJ-1-601/review-of-finite-base.md
- agents/tasks/LJ-1-601/runs/

## PREMISES

1. `[LJ-1.597]` is a NO-GO and names the finite base as unmeasured. Basis: agents/tasks/LJ-1-597/review-of-step-graph.md:154
2. `step` is one equation. Basis: src/L/StageCardinal.lagda.md:561
3. `limit-step` is `LimitStep.h`. Basis: src/L/StageCardinal.lagda.md:396
4. `h x` is `leastOf` over the ordinal order. Basis: src/L/StageCardinal.lagda.md:350
5. `sq` is a bare module parameter. Basis: src/L/StageCardinal.lagda.md:17
6. `[LJ-1.594]` wrote `class-pred` out by refl. Basis: agents/tasks/LJ-1-594/Probe594.agda:283
7. `[LJ-1.572]` reached `sq` by refl from the other side. Basis: agents/tasks/LJ-1-572/review-of-b9-g-definable.md:116
8. `[LJ-1.596]` is a NO-GO on the chapter route. Basis: agents/tasks/LJ-1-596/lj-1.596-report.md:1
9. `defSet` is `𝒟ₒ` in that module. Basis: src/L/StageCardinal.lagda.md:400
10. The least-element selection is the ordinal order. Basis: src/L/StageCardinal.lagda.md:258
11. A stop is a deliverable. Basis: AGENTS.md:43
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

Three independent readings of the same chain and two reopener lists. **This item
is on one of them and nobody has taken it.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE STATEMENT.** Read `[LJ-1.597]`'s item 2
and **write out what it asks, at `file:line`, in your own probe.** If its
sentence is not precise enough to state, say so and say what is missing: that is
a defect in the reopener and worth knowing.

**A MEASUREMENT IS THE DELIVERABLE, NOT A CONSTRUCTION.** If the answer is no,
report it with the evidence and stop. **Do not build a cure for what you
measured.**

**TIME-BOX EVERY TYPECHECK.** Set your own wall-clock cap and report it. **Two
tasks this week ran 1800 s because nobody capped one.**

**DO NOT ATTEMPT (v), (i), (ii), (iii) OR (iv) OF THE `class-pred` FORMULA.**
`[LJ-1.600]` has (v). AD12 gives this brief one obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE MEASUREMENT`.** What you measured, the number
or the verdict, and the cap you ran under.

**REQUIRED REPORT SECTION `## WHAT IT RETIRES OR RE-PRICES`.** Two sentences.
**Say whether your answer removes any item from either reopener list.**

ESTIMATE: about 140 lines in the probe, of which the obligation is about 35.
**Uncertain, because I am taking the statement from a predecessor rather than
writing it.** Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the statement itself, taken verbatim.

    -- LJ-1.597's item 2, restated as a type in this probe, TYPE ONLY

**Write it FIRST and typecheck it ALONE, under a cap.** If it will not state,
that is your report. ESTIMATE: about 12 lines, cap at two minutes.

## WHAT GO AND NO-GO EACH EARN

**EITHER OUTCOME IS A MEASUREMENT THIS CAMPAIGN DOES NOT HAVE**, and it is the
cheapest open item on either list.

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
  changed_files_none = ["agents/tasks/LJ-1-601/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-601/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-601/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-601/Probe601.agda"]
  changed_files_none = ["agents/tasks/LJ-1-601/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-601/review-of-*.md"]

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
  Full entry: dev/LESSONS.md:2307
- **P-l. A statement may be ABOUT a concrete stage without dragging that stage's PRESENTATION into its type**
  **The law.** Being about a concrete position is not what costs. Naming a transparent construction in a statement's TYPE is. If the tower's stage values are `opaque` upstream, a theorem may quantify over, hypothesize about and conclude at `Sset ω` freely, because the stage is an ATOM to the elaborator and nothing unfolds. If instead the type mentions a transparent presentation, such as `⟪ sucV (...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2367
- **D-26. A well-founded key on a tower needs generation data, or it needs syntax**
  **Rule:** When a route must well-order a cumulative tower's stage, ask first what the stage's members CARRY. A stage built as the values of finitely many total operations carries its own generation data, so a well-founded key exists with NO syntax at all: the operation index, then the arguments, ordered recursively. A stage built as a definable power carries nothing: its members are sets, not c...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:1735
- **C-42. A refutation measures the site it names, and it never measures how far that site extends**
  **Rule:** A refutation is a measurement of ONE site. It says the statement there is false. **It says nothing about how many other sites carry the same false shape.** So when a refutation lands, the next action is not the cure. **It is the sweep: search the tree for the shape, and report the COUNT before you price the cure.** A cure funded against the named site is priced against a number nobody...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:3762

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev, archive/scripts, dev/ARCHIVE.md:
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 188.133)
- CANDIDATE archive/dev/JOURNAL.md  (score 177.385)
- CANDIDATE dev/ARCHIVE.md  (score 164.787)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 163.679)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 150.870)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 60.315)
- CANDIDATE dev/literature/devlin-II5.md  (score 52.586)
- CANDIDATE dev/literature/digest.md  (score 46.829)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 42.748)
- CANDIDATE dev/literature/geology.md  (score 42.745)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
