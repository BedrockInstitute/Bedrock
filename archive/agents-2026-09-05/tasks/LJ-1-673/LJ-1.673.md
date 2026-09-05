# LJ-1.673: the bound is a hull member

## HEAD
head_slot: coder
machine: shared
agda_tier: wide

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-673/Probe673.agda`:

    lset-grounded : <`LsetGrounded` at `[LJ-1.667]`'s `matrix₃`, the
                     hull-membership of the bound>

Land nothing in `src/`. **This is NOT a second formula.** `[LJ-1.667]` says so in
those words: it is the hull-membership of the bound at the matrix already written.

**NAME ANY FILE THAT CANNOT TYPECHECK `.agda.txt`, NEVER `.agda`.** Conjunct 1
runs EVERY `.agda` under this task home.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-673/Probe673.agda::lset-grounded"]

## SCOPE (write)
- agents/tasks/LJ-1-673/Probe673.agda
- agents/tasks/LJ-1-673/lj-1.673-report.md
- agents/tasks/LJ-1-673/review-of-lset-grounded.md
- agents/tasks/LJ-1-673/runs/

## PREMISES

1. **`[LJ-1.667]` NAMES THIS AS ITS SECOND ITEM AND SAYS THE CONSUMER IS ALREADY
   GREEN.** `commute-from-witnessed` at `agents/tasks/LJ-1-652/Probe652.agda:266`.
   Basis: agents/tasks/LJ-1-667/lj-1.667-report.md:1
2. `[LJ-1.667]` delivered the witness slot's SYNTAX; what it could not give was
   soundness and a hull member. This is the second of those two. Basis:
   agents/tasks/LJ-1-667/lj-1.667-report.md:1
3. `hull-closed` is the hull's only closure rule and takes a `Formula Code 1`, so
   a membership claim needs the condition named in the hull's language. Basis:
   src/L/Hull.lagda.md:415
4. **CLAUSE (iii)'s COMMUTE IS ALREADY CLOSED GIVEN ITS INPUTS.** `commute-641`
   delivers `[LJ-1.641]`'s own type from elementarity and a formula, and
   `[LJ-1.670]` proved the elementarity slot fills from what the tree has. Basis:
   agents/tasks/LJ-1-670/lj-1.670-report.md:1

## WHAT IS DELIVERED ALREADY

Premises 1 and 4, both green. `LsetGrounded` has supply 0.

## THE REASONING

Clause (iii) now needs two things and a sibling is taking the other. This one has
a green consumer waiting and an elementarity slot already filled, so it is the
shorter of the two.

## W3, THE WIDEST UNMEASURED TERM

Getting the bound into the hull without a second formula. Estimate 80 to 180
lines, basis: `[LJ-1.667]` wrote the syntax and stopped at exactly this
(agents/tasks/LJ-1-667/lj-1.667-report.md:1).

## WHAT GO AND NO-GO EACH EARN

**GO** with a sibling's GO closes clause (iii) outright.
**NO-GO** earns why the bound resists the hull, which is the same class of fact
`[LJ-1.664]` earned for `𝒟ₒ`.
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
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-673/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-673/review-of-LJ-*-*.md"]

[[branch]]
id = "accept-failed"
priority = 14
action = "escalate"
head_slot = "coder_adversarial"

  [branch.when]
  exit_code = 1
  obligations_delta_max = -1
  changed_files_none = ["agents/tasks/LJ-1-673/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-673/Probe673.agda"]
  changed_files_none = ["agents/tasks/LJ-1-673/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-673/review-of-*.md"]

[[branch]]
# PARK, NOT ESCALATE. A heap wall is a resource fact and no critic can
# adjudicate it (MEASURED on LJ-1.534).
id = "heap-wall-park"
priority = 30
action = "park_and_split"

  [branch.when]
  heap_wall = true

[[branch]]
# CLOSES BACKLOG ITEM 30, MEASURED ON LJ-1.630 2026-08-25. A REAL failed
# landing carries a named Agda error and NEITHER companion file: the coder
# edits the target directly and leaves ad-hoc runs/*.out. Both rows above
# demand a companion (Probe or review-of), so that return matched NOTHING
# and the task parked with its evidence invisible. This row is the catch-all
# and it sits BELOW heap-wall-park, so a wall still parks.
id = "no-go-bare"
priority = 40
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
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

## STANDING (program-generated, do not edit)

The records every dispatch may need. They are NOT candidates, they are not the answer to any search, and no return has to account for them. The search below spends its whole budget on what is not here.

- STANDING archive/dev/JOURNAL-archived.md
- STANDING dev/literature/truncation-and-selection.md
- STANDING dev/literature/devlin-II5.md
- STANDING dev/literature/digest.md
- STANDING archive/dev/LJ-dispatch-index.md
- STANDING archive/dev/JOURNAL.md
- STANDING dev/literature/terms-2026-08.md
- STANDING dev/ARCHIVE.md
- STANDING dev/literature/geology.md
- STANDING archive/dev/DECISIONS-archived.md

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev, archive/scripts, dev/ARCHIVE.md:
- CANDIDATE archive/dev/DD-archived.md  (score 141.202)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 140.150)
- CANDIDATE archive/dev/PLAN-archived.md  (score 126.554)
- CANDIDATE archive/dev/STATUS-archived.md  (score 100.482)
- CANDIDATE archive/dev/TASKS-archived.md  (score 95.864)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 32.766)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 32.631)
- CANDIDATE dev/literature/devlin-errata.md  (score 31.814)
- CANDIDATE dev/literature/primary-sources.md  (score 30.185)
- CANDIDATE dev/literature/BIBLIOGRAPHY.md  (score 28.675)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
