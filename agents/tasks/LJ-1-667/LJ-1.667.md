# LJ-1.667: the witnessed matrix clause three actually wants

## HEAD
head_slot: coder
machine: shared
agda_tier: wide

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-667/Probe667.agda`:

    witnessed-lset : <`Witnessed Lset` together with `LsetGrounded`, at the
                      shape `[LJ-1.652]` measured and `[LJ-1.665]` assembled>

Land nothing in `src/`. **DO NOT FUND `Matrix₂`.** `[LJ-1.665]` records that D-10
explicitly: the literature's matrix has a WITNESS slot, and
`certificate-remainder-witnessed` is the same assembly at the corrected shape,
green.

**NAME ANY FILE THAT CANNOT TYPECHECK `.agda.txt`, NEVER `.agda`.** Conjunct 1
runs EVERY `.agda` under this task home.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-667/Probe667.agda::witnessed-lset"]

## SCOPE (write)
- agents/tasks/LJ-1-667/Probe667.agda
- agents/tasks/LJ-1-667/lj-1.667-report.md
- agents/tasks/LJ-1-667/review-of-witnessed-lset.md
- agents/tasks/LJ-1-667/runs/

## PREMISES

1. **`[LJ-1.665]` NAMES THIS AS ONE OF THREE OBJECTS THE CERTIFICATE STILL OWES**,
   and says its consumer is already green. Basis:
   agents/tasks/LJ-1-665/lj-1.665-report.md:328
2. `[LJ-1.652]` recorded that the literature's matrix carries a witness slot, and
   that Δ₀ is the only thing that crosses into the collapse. Basis:
   agents/tasks/LJ-1-652/lj-1.652-report.md:1
3. **CLAUSE (iii) IS A DIFFERENT FORMULA ON A DIFFERENT ALPHABET FROM
   `LevelFormula`**, ambient and parameter-free, so a sibling working the level
   formula does not produce this. Basis: agents/tasks/LJ-1-665/lj-1.665-report.md:1
4. **`[LJ-1.665]` ALSO LISTS `Elementary` AS AN OBJECT TO FUND, AND THAT MAY BE
   STALE.** It never mentions `[LJ-1.655]`, which delivered `elem-at-collapse` GO,
   and `elem : A.Elementary` is proved at `src/L/BoundedSubset.lagda.md:759`.
   **Take elementarity from there and report if it does not reach.** Basis:
   src/L/BoundedSubset.lagda.md:759

## WHAT IS DELIVERED ALREADY

`LsetGrounded` has supply 0. Premise 1's consumer is green. `commute-641`, the
clause (iii) statement, is delivered and waits only on the formula.

## THE REASONING

Clause (iii)'s commute closed this week from elementarity plus a formula. The
formula it wants is this one, at the witnessed shape rather than the two-slot one
that two earlier tasks assumed.

## W3, THE WIDEST UNMEASURED TERM

The witness slot's content. Estimate 100 to 220 lines, basis: `[LJ-1.651]` built
the two-slot analogue in a 156-line probe
(agents/tasks/LJ-1-651/lj-1.651-report.md:1).

## WHAT GO AND NO-GO EACH EARN

**GO** closes clause (iii) outright, since its consumer is green.
**NO-GO** earns what the witness slot needs that the ambient reading cannot give.
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
  changed_files_any = ["agents/tasks/LJ-1-667/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-667/review-of-LJ-*-*.md"]

[[branch]]
id = "accept-failed"
priority = 14
action = "escalate"
head_slot = "coder_adversarial"

  [branch.when]
  exit_code = 1
  obligations_delta_max = -1
  changed_files_none = ["agents/tasks/LJ-1-667/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-667/Probe667.agda"]
  changed_files_none = ["agents/tasks/LJ-1-667/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-667/review-of-*.md"]

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
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 145.080)
- CANDIDATE archive/dev/DD-archived.md  (score 135.770)
- CANDIDATE archive/dev/PLAN-archived.md  (score 123.495)
- CANDIDATE archive/dev/STATUS-archived.md  (score 106.492)
- CANDIDATE archive/dev/TASKS-archived.md  (score 105.795)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 38.884)
- CANDIDATE dev/literature/BIBLIOGRAPHY.md  (score 33.535)
- CANDIDATE dev/literature/primary-sources.md  (score 28.416)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 28.408)
- CANDIDATE dev/literature/devlin-errata.md  (score 25.288)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
