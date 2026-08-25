# LJ-1.534: the frame the honest forms want, and whether it is satisfiable

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-534/Probe534.agda`:

    honest-frame-inhabited :
        (the extra hypotheses the EnvSupply honest forms take, collected as one
         record or telescope)
      → (a witness of that telescope at KValue's frame)

**state the collected frame AND exhibit one inhabitant.** Land nothing in
`src/`.

**A CENSUS OF ALL 59 FIELDS EXISTS AND IT IS STRANDED.** `[LJ-1.512]` delivered
it, then hit `attempt_max:sys-lint-accept` and parked permanently, so its report
is in a worktree and not in the tree. **The mathematician has read it and its
count is the reason for this task**: 41 of the 59 `TFacts` fields have an honest
form delivered in `src/L/Coding/EnvSupply.lagda.md`, 16 have theirs elsewhere,
2 have none in `src/`. **Do not cite the stranded report as a basis. Re-derive
what you need from `src/`.**

**THE CHAPTER HAS TWO HOMES FOR HONEST FORMS AND BOTH ARE LIVE.**
`SupplyEnv` (`src/L/Coding/EnvSupply.lagda.md:107`), pinned to the concrete
level `lam`; and `Fact` (`:450`), generic over `(K, Ktr)`.

**WHY THIS AND NOT A RECORD REPLACEMENT.** The census says 16 of the 41
chapter-delivered forms take extra mathematical hypotheses the record field does
not carry. **So the swap is not mechanical.** This campaign has met that shape
four times and ruled the same way each time: `arNumC` (`[LJ-1.500]`), `valSub`
(`[LJ-1.508]`), the ω gate (`[LJ-1.503]`), `defPow-closed` (`[LJ-1.522]`). **The
hypothesis goes in the FRAME, where the carrier is a value.** This task collects
them and asks whether they can all hold at once.

**AND NON-VACUITY IS THE POINT, NOT THE STATEMENT.** `[LJ-1.507]` proved that
three dispatches of this campaign built toward `someEnvDef-gap`, a statement
NOTHING SATISFIED. **A collected frame that nothing inhabits would repeat that
at sixteen times the scale.** The witness is the deliverable.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-534/Probe534.agda::honest-frame-inhabited"]

## SCOPE (write)
- agents/tasks/LJ-1-534/Probe534.agda
- agents/tasks/LJ-1-534/lj-1.534-report.md
- agents/tasks/LJ-1-534/review-of-honest-frame.md
- agents/tasks/LJ-1-534/runs/

## PREMISES

1. `SupplyEnv` is one home for the honest forms. Basis: src/L/Coding/EnvSupply.lagda.md:107
2. `Fact` is the other, generic over the carrier. Basis: src/L/Coding/EnvSupply.lagda.md:450
3. `envK-gen` is a delivered honest form there. Basis: src/L/Coding/EnvSupply.lagda.md:277
4. `subK-gen` is another. Basis: src/L/Coding/EnvSupply.lagda.md:481
5. `TFacts` is the record under question. Basis: src/L/Condensation/TwelveAgree.lagda.md:129
6. `KValue` binds the carrier and the stage. Basis: src/L/Condensation.lagda.md:7380
7. `[LJ-1.495]` delivers `KFacts` at the shifted indices. Basis: agents/tasks/LJ-1-495/Probe495.agda:166
8. `[LJ-1.507]` proved a three-dispatch chain rested on an empty antecedent. Basis: agents/tasks/LJ-1-507/Probe507.agda:257
9. `[LJ-1.508]` ruled a frame hypothesis about slot one. Basis: agents/tasks/LJ-1-508/Probe508.agda:201
10. `[LJ-1.522]` ruled another at a limit. Basis: agents/tasks/LJ-1-522/Probe522.agda:356
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**FIFTY SEVEN OF FIFTY NINE FIELDS HAVE A DELIVERED HONEST FORM SOMEWHERE.**
That is what the stranded census measured and it is the largest single result
this front has produced. **What nobody has checked is whether the hypotheses
those forms want can hold together.**

## THE REASONING

**D-10, BEFORE ANY AGDA.** Walk `src/L/Coding/EnvSupply.lagda.md` and collect,
at `file:line`, every hypothesis that `SupplyEnv`'s telescope (`:107` onward)
and `Fact`'s telescope (`:450` onward) take. **Say which of them `KValue`'s
frame already supplies and which it does not.** `KValue.facts` is at
`src/L/Condensation.lagda.md:7411` and `[LJ-1.495]` shifts it.

**COLLECT, THEN INHABIT. IN THAT ORDER.** A telescope nobody can satisfy is
worth nothing, and this campaign has paid three dispatches to learn it.

**IF TWO HYPOTHESES CONFLICT, SAY WHICH AND STOP.** Sixteen forms take extra
hypotheses; if any two cannot hold at once, the honest forms cannot all be used
at one frame and the record needs splitting rather than replacing. **That is a
finding about the design and it is the best outcome this task could have.**

**DO NOT REPLACE `TFacts` AND DO NOT EDIT `src/`.** Whether the record is
replaced is the mathematician's, and this task is its evidence.

**DO NOT REBUILD THE 59-ROW CENSUS.** It exists. Re-derive only the hypotheses
you need, from `src/`.

**DO NOT POSTULATE.**

**REQUIRED REPORT SECTION `## THE COLLECTED FRAME`.** The telescope as a type,
with every hypothesis at its `file:line`, and for each: supplied by `KValue`,
supplied by `[LJ-1.495]`'s shift, or NEW. **The count of NEW is the number the
mathematician needs.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 180 lines in the probe, of which the obligation is
about 60. BASIS: `[LJ-1.522]` and `[LJ-1.530]` each built several memberships at
this frame in comparable files. Comparables are of SHAPE and nothing may be
funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the witness, because the whole point is whether the collected frame is
inhabited and no statement about it matters otherwise.

    -- one inhabitant of the collected telescope at KValue's frame

**Build it FIRST if you can, or state the telescope and then attack the
witness.** If nothing inhabits it, say which hypothesis has no witness and
STOP.

ESTIMATE for W3: unknown. **Report it.** The collected telescope has not been
written, so there is no comparable and the brief will not invent one.

## WHAT GO AND NO-GO EACH EARN

**A GO SAYS THE HONEST FORMS CAN ALL BE USED AT ONE FRAME**, and the
mathematician can rule on replacing the record with a projection of them.

**A NO-GO NAMES TWO HYPOTHESES THAT CANNOT HOLD TOGETHER**, which would say the
record must be split rather than replaced. **Either answer settles a question
this campaign has circled since `[LJ-1.495]`.**

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
  changed_files_none = ["agents/tasks/LJ-1-534/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-534/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-534/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-534/Probe534.agda"]
  changed_files_none = ["agents/tasks/LJ-1-534/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-534/review-of-*.md"]

[[branch]]
id = "heap-wall-escalate"
priority = 30
action = "escalate"
head_slot = "coder_adversarial"

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 239.187)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 214.103)
- CANDIDATE archive/dev/JOURNAL.md  (score 205.903)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 181.882)
- CANDIDATE archive/dev/PLAN-archived.md  (score 176.008)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 60.612)
- CANDIDATE dev/literature/digest.md  (score 56.942)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 47.231)
- CANDIDATE dev/literature/terms-2026-08.md  (score 45.059)
- CANDIDATE dev/literature/geology.md  (score 42.579)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
