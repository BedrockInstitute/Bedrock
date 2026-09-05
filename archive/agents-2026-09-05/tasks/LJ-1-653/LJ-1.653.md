# LJ-1.653: is step 4 TRUE at ordinals, before anyone prices its proof

## HEAD
head_slot: coder
machine: shared
agda_tier: wide

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-653/Probe653.agda`:

    step4-at-ord-status : <either a term of `[LJ-1.462]`'s step 4 RESTRICTED to
                           ordinal `y`, from elementarity as a hypothesis, or a
                           term refuting it at a named `y` the frame admits>

Land nothing in `src/`. **This prices a TARGET's truth, per D-10, before anyone
prices its proof.**

Step 4 is `πCommuteLset = (y : S) → ⟨ y ∈ˢ M ⟩ → C.π (Lset y) ≡ Lset (C.π y)`
(`agents/tasks/LJ-1-462/Probe462.agda:140-142`).

**NAME ANY FILE THAT CANNOT TYPECHECK `.agda.txt`, NEVER `.agda`.** A floor with
holes, a bisection arm that walls, a superseded shape: keep it, track it and cite
it, but do not claim it typechecks. Conjunct 1 runs EVERY `.agda` under this task
home. `[LJ-1.636]` and `[LJ-1.643]` each lost real attempts to exactly that.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-653/Probe653.agda::step4-at-ord-status"]

## SCOPE (write)
- agents/tasks/LJ-1-653/Probe653.agda
- agents/tasks/LJ-1-653/lj-1.653-report.md
- agents/tasks/LJ-1-653/review-of-step4-status.md
- agents/tasks/LJ-1-653/runs/

## PREMISES

1. **`[LJ-1.649]` NAMES THIS THE CAMPAIGN'S REAL STOP.** After it, `levelIn`
   reduces to exactly TWO objects, and step 2 has a route while step 4 has a
   NO-GO that has never been reattempted. Basis:
   agents/tasks/LJ-1-649/lj-1.649-report.md:334
2. `[LJ-1.477]`'s NO-GO is an obstruction of the computation-law route and it
   recorded that it "did not prove the type false". Basis:
   agents/tasks/LJ-1-477/lj-1.477-report.md:188
3. **AN ORDINAL-CONDITIONED STEP 4 IS ENOUGH FOR THE CONSUMER**, and that is a
   cheaper target than the one `[LJ-1.477]` attacked. Basis:
   agents/tasks/LJ-1-649/Probe649.agda:237
4. Elementarity is proved at this chapter, `elem : A.Elementary`, and
   `[LJ-1.477]` mentions it three times without using it. Basis:
   src/L/BoundedSubset.lagda.md:759

## WHAT IS DELIVERED ALREADY

`[LJ-1.477]`'s measurement of where the two computation laws fail to meet.
`πCommuteLset` has supply 0.

## THE REASONING

D-10 says a recorded residue names a target that can itself be false, and
`[LJ-1.477]` explicitly did not settle that. Before this campaign funds a proof
of step 4 it should know whether step 4 is true at the ordinals its consumer
needs. **Both answers are first class and the refutation is the more valuable.**

## W3, THE WIDEST UNMEASURED TERM

Whether the collapse of a LEVEL is the level of the collapse at an ordinal.
Estimate 90 to 190 lines, basis: `[LJ-1.477]`'s probe reached the join of the two
laws (agents/tasks/LJ-1-477/lj-1.477-report.md:1).

## WHAT GO AND NO-GO EACH EARN

**GO** either closes `levelIn`'s last object or refutes it and re-plans the
campaign in one dispatch. **NO-GO** here means neither could be settled, and you
say which side resisted.
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
  changed_files_any = ["agents/tasks/LJ-1-653/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-653/review-of-LJ-*-*.md"]

[[branch]]
id = "accept-failed"
priority = 14
action = "escalate"
head_slot = "coder_adversarial"

  [branch.when]
  exit_code = 1
  obligations_delta_max = -1
  changed_files_none = ["agents/tasks/LJ-1-653/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-653/Probe653.agda"]
  changed_files_none = ["agents/tasks/LJ-1-653/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-653/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 191.685)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 181.574)
- CANDIDATE archive/dev/JOURNAL.md  (score 154.010)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 144.568)
- CANDIDATE dev/ARCHIVE.md  (score 140.894)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 54.466)
- CANDIDATE dev/literature/digest.md  (score 40.540)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 38.616)
- CANDIDATE dev/literature/devlin-errata.md  (score 29.426)
- CANDIDATE dev/literature/geology.md  (score 29.011)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
