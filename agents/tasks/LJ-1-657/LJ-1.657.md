# LJ-1.657: levelIn from the level formula

## HEAD
head_slot: coder
machine: shared
agda_tier: wide

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-657/Probe657.agda`:

    levelin-from-level-formula :
        <`[LJ-1.650]`'s `LevelFormula` as a HYPOTHESIS>
      → <`[LJ-1.653]`'s `HoodExistsP` and `HoodSoundP` at the formula it carries>

Land nothing in `src/`. **Do not build `LevelFormula`. `[LJ-1.653]` already
proved that those two give `LevelIn`; this brief connects the formula to them.**

**NAME ANY FILE THAT CANNOT TYPECHECK `.agda.txt`, NEVER `.agda`.** Conjunct 1
runs EVERY `.agda` under this task home. `[LJ-1.636]` and `[LJ-1.643]` each lost
real attempts to a floor or bisection file that failed by construction.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-657/Probe657.agda::levelin-from-level-formula"]

## SCOPE (write)
- agents/tasks/LJ-1-657/Probe657.agda
- agents/tasks/LJ-1-657/lj-1.657-report.md
- agents/tasks/LJ-1-657/review-of-levelin-from-level-formula.md
- agents/tasks/LJ-1-657/runs/

## PREMISES

1. `[LJ-1.653]` proved `levelin-from-hood-pf : (φ₀ : Formula _ 2) → HoodExistsP φ₀
   → HoodSoundP φ₀ → LevelIn`, green. Basis:
   agents/tasks/LJ-1-653/Probe653.agda:290
2. **THAT CHAIN CONTAINS NO STEP 2 AND NO STEP 4**, so `[LJ-1.462]`'s
   decomposition is not the only road and step 4 is not a toll gate on this one.
   Basis: agents/tasks/LJ-1-653/lj-1.653-report.md:1
3. `LevelFormula` carries a `Formula Code 2` with soundness AND completeness,
   which is the arity and the two halves premise 1 wants. Basis:
   agents/tasks/LJ-1-650/Probe650.agda:322
4. **THE ARITY MATCH IS MY READING AND IT IS THE THING TO TEST.** The two
   formulas live over different alphabets: `Formula Code 2` against
   `Formula (⊥* {ℓ-suc ℓ}) 2`. If the embedding costs something, that cost IS the
   deliverable. Basis: agents/tasks/LJ-1-653/Probe653.agda:283

## WHAT IS DELIVERED ALREADY

Premise 1's term. `HoodExistsP` and `HoodSoundP` have supply 0.

## THE REASONING

`[LJ-1.653]` opened a road to `levelIn` that bypasses two objects the campaign
had thought mandatory. This measures whether the level formula drives on it.

## W3, THE WIDEST UNMEASURED TERM

The alphabet embedding of premise 4. Estimate 80 to 170 lines, basis:
`[LJ-1.653]`'s own probe reached `LevelIn` from the two Hood facts
(agents/tasks/LJ-1-653/lj-1.653-report.md:1).

## WHAT GO AND NO-GO EACH EARN

**GO** reduces `levelIn`, the campaign's oldest stop, to ONE object that
`[LJ-1.656]` is building. **NO-GO** earns the alphabet gap as a type, which is a
fact about the hull's two readings that no report carries.
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
  changed_files_any = ["agents/tasks/LJ-1-657/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-657/review-of-LJ-*-*.md"]

[[branch]]
id = "accept-failed"
priority = 14
action = "escalate"
head_slot = "coder_adversarial"

  [branch.when]
  exit_code = 1
  obligations_delta_max = -1
  changed_files_none = ["agents/tasks/LJ-1-657/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-657/Probe657.agda"]
  changed_files_none = ["agents/tasks/LJ-1-657/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-657/review-of-*.md"]

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

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev, archive/scripts, dev/ARCHIVE.md:
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 153.104)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 137.753)
- CANDIDATE archive/dev/JOURNAL.md  (score 126.034)
- CANDIDATE dev/ARCHIVE.md  (score 124.950)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 116.701)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 45.855)
- CANDIDATE dev/literature/digest.md  (score 39.744)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 34.364)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 23.485)
- CANDIDATE dev/literature/terms-2026-08.md  (score 22.684)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
