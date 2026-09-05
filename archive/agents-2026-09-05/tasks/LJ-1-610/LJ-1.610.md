# LJ-1.610: face G+, the stage's inner world at the tower's own values

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-610/Probe610.agda`:

    graph-stage : <`GraphStage`, face G+ of `[LJ-1.606]`'s `Crossing`>
      (`agents/tasks/LJ-1-606/Probe606.agda:156-159`)

Land nothing in `src/`.

**`[LJ-1.606]` IS GO. IT BUILT THE CROSSING AND NAMED THREE FACES.** Row 3's
three clause failures share one root, and the crossing is that root
(`[LJ-1.602]`). Face G+ is one of three things the crossing consumes and nothing
else does:

> **G+ `GraphStage`**: the stage's inner world satisfies the **Σ₁ closure** of
> the graph matrix at the tower's own values. **UNBUILT.** Devlin (b)'s
> witness-in-carrier (`dev/literature/devlin-II5.md:222`); the `Adeq` shape of
> `[LJ-1.570]` (`agents/tasks/LJ-1-570/Probe570.agda:319-322`).

**THIS BRIEF CARRIES A LITERATURE STEP AND THE SOURCE IS NAMED TO THE LINE.**
`dev/literature/devlin-II5.md:222` reads, in part, **"the Σ₁ form is
'witnessed inside the carrier', not"** the ambient one. **Read the whole clause
and say what it gives and what it leaves to the reader.**

**THE Σ₁ IS THE POINT AND IT IS NOT A Δ₀.** `[LJ-1.562]` measured that both of
`AtStage`'s hypotheses are payable at a Δ₀ formula. **G+ is a Σ₁ closure, so
that measurement does NOT transfer.** A measured cure does not transfer by
analogy.

**THE KIT IS PROVED NON-VACUOUS.** `[LJ-1.606]` showed the faces cannot be
filled with junk, both ways (`Probe606.agda:260-285`).

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-610/Probe610.agda::graph-stage"]

## SCOPE (write)
- agents/tasks/LJ-1-610/Probe610.agda
- agents/tasks/LJ-1-610/lj-1.610-report.md
- agents/tasks/LJ-1-610/review-of-graph-stage.md
- agents/tasks/LJ-1-610/runs/

## PREMISES

1. `[LJ-1.606]` is GO and names three faces. Basis: agents/tasks/LJ-1-606/lj-1.606-report.md:119
2. Face G+ is stated at its probe. Basis: agents/tasks/LJ-1-606/Probe606.agda:156
3. Devlin's Σ₁ form is witnessed inside the carrier. Basis: dev/literature/devlin-II5.md:222
4. The `Adeq` shape is `[LJ-1.570]`'s. Basis: agents/tasks/LJ-1-570/Probe570.agda:319
5. The kit cannot be filled with junk. Basis: agents/tasks/LJ-1-606/Probe606.agda:260
6. `[LJ-1.602]` found the shared root of row 3's failures. Basis: agents/tasks/LJ-1-602/lj-1.602-report.md:1
7. `[LJ-1.562]` measured both `AtStage` hypotheses payable at a Δ₀ formula. Basis: agents/tasks/LJ-1-562/lj-1.562-report.md:1
8. `Σ₁` has an unbounded-quantifier constructor. Basis: src/FOL/LevyHierarchy.lagda.md:75
9. `AtStage`'s first hypothesis is Δ₀. Basis: src/L/Axioms/Separation.lagda.md:199
10. `defSet` reads under the world's inner satisfaction. Basis: src/L/Definability.lagda.md:111
11. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
12. A stop is a deliverable. Basis: AGENTS.md:43
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

A built crossing, a non-vacuity proof, and an `Adeq` shape at a sibling site.
**Face G+ is unbuilt.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE LITERATURE.** Read
`dev/literature/devlin-II5.md` around `:222` and say at `file:line` **what
Devlin's (b) supplies for the witness-in-carrier and what it assumes.** That
reading is the deliverable even if the Agda does not land.

**THEN THE `Adeq` SHAPE.** `[LJ-1.570]`'s `Probe570.agda:319-322` is the nearest
built thing. **Say at `file:line` what it does and whether it instantiates at
G+'s frame.** If it does, this task may be short.

**THE Σ₁ IS WHERE THIS DIFFERS FROM EVERY Δ₀ RESULT THIS CAMPAIGN HAS.** Say
explicitly whether you need an unbounded quantifier
(`src/FOL/LevyHierarchy.lagda.md:75`) and, if so, where it is discharged. **If it
cannot be discharged inside the stage, say so and stop**: that would be the same
wall two legs of this campaign already met, reached from a third side.

**DO NOT BUILD FACES E OR G-.** AD12 gives this brief one obligation.

**CAP EVERY TYPECHECK ON A WALL CLOCK YOU SET AND REPORT THE CAP**, and report
peak RSS: this family heap-walled once.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED LITERATURE STEP.** Name in a LITERATURE USED section what you read of
`dev/literature/devlin-II5.md` and `dev/literature/devlin-errata.md`, and whether
the errata record anything about (b).

**REQUIRED REPORT SECTION `## WHERE THE Σ₁ IS DISCHARGED`.** At `file:line`, or
the sentence that it is not.

ESTIMATE: about 200 lines in the probe, of which the obligation is about 50.
**Uncertain: every prior success on this machinery was at Δ₀ and this is not.**
Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the Σ₁ closure itself.

    -- the Σ₁ closure of the graph matrix, stated alone, TYPE ONLY, capped

**Write it FIRST, typecheck it ALONE, cap it.** ESTIMATE: about 15 lines, cap at
two minutes.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS THE FACE THAT CARRIES DEVLIN'S OWN (b)** and, with E and G-, would
complete the crossing that row 3's three failures reduce to.

**A NO-GO THAT NAMES AN UNDISCHARGEABLE Σ₁ REACHES THIS CAMPAIGN'S OLDEST WALL
FROM A THIRD SIDE**, which is worth knowing precisely.

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
  changed_files_none = ["agents/tasks/LJ-1-610/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-610/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-610/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-610/Probe610.agda"]
  changed_files_none = ["agents/tasks/LJ-1-610/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-610/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 192.224)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 181.361)
- CANDIDATE archive/dev/JOURNAL.md  (score 165.578)
- CANDIDATE dev/ARCHIVE.md  (score 150.556)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 136.341)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 78.806)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 59.176)
- CANDIDATE dev/literature/digest.md  (score 50.135)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 47.989)
- CANDIDATE dev/literature/geology.md  (score 42.112)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
