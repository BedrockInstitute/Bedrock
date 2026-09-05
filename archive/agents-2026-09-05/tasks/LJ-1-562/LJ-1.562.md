# LJ-1.562: AtStage's SECOND hypothesis, which nobody has looked at

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-562/Probe562.agda`:

    constants-bounded :
      <`BoundedFo Below` for the formula `[LJ-1.536]` needed at `𝒟ₒ-intro`,
       or the term that refutes it>

Land nothing in `src/`.

**`AtStage` HAS TWO HYPOTHESES AND THE CAMPAIGN HAS ONLY EVER DISCUSSED THE
FIRST.** `[LJ-1.536]`'s stop names both
(`agents/tasks/LJ-1-536/review-of-StageHigh.md`,
`## What the door wants that the tree does not have`):

1. the formula is **Δ₀** (`src/L/Axioms/Separation.lagda.md:199-206`), and
2. **every constant in it is a member of the stage** (`BoundedFo Below`).

**Every report this week has argued about the first.** `[LJ-1.560]` takes it.
**This brief takes the second, and it is a different question with a different
answer.**

**AND THERE IS A COUNT THAT MAKES IT URGENT.** `[LJ-1.514]` counted **664
constants** in the Formula carrier (`agents/tasks/LJ-1-514/lj-1.514-report.md`),
which killed an earlier hope that the family had none. **If those constants
cannot be bounded by a stage, the second hypothesis fails no matter what happens
to the first**, and `[LJ-1.560]`'s answer would not matter.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-562/Probe562.agda::constants-bounded"]

## SCOPE (write)
- agents/tasks/LJ-1-562/Probe562.agda
- agents/tasks/LJ-1-562/lj-1.562-report.md
- agents/tasks/LJ-1-562/review-of-constants-bounded.md
- agents/tasks/LJ-1-562/runs/

## PREMISES

1. `[LJ-1.536]` is a NO-GO and names both hypotheses. Basis: agents/tasks/LJ-1-536/lj-1.536-report.md:1
2. `AtStage` is the one external-to-inner bridge. Basis: src/L/Axioms/Separation.lagda.md:119
3. Its Δ₀ hypothesis sits at a stated line. Basis: src/L/Axioms/Separation.lagda.md:199
4. `𝒟ₒ-intro` is the one route into a stage. Basis: src/L/Constructible.lagda.md:301
5. `defSet` reads under the world's inner satisfaction. Basis: src/L/Definability.lagda.md:111
6. `[LJ-1.514]` counted 664 constants in the Formula carrier. Basis: agents/tasks/LJ-1-514/lj-1.514-report.md:1
7. `[LJ-1.514]` killed the Formula-carrier wall via `Relabel`. Basis: agents/tasks/LJ-1-514/lj-1.514-report.md:1
8. `[LJ-1.522]` paid `[LJ-1.520]`'s unpaid cost row. Basis: agents/tasks/LJ-1-522/lj-1.522-report.md:1
9. `Bounding` states the bounded-quantifier machinery. Basis: src/FOL/Manipulation/Bounding.lagda.md:146
10. A stop is a deliverable. Basis: AGENTS.md:43
11. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
12. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

`Relabel`, which `[LJ-1.514]` used to kill the Formula-carrier wall for a whole
family, and a count of 664 constants. **No term says whether those constants sit
inside a stage.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS WHICH CONSTANTS ACTUALLY OCCUR.** 664 is the
carrier's count, not this formula's. **Say at `file:line` how many constants the
formula `[LJ-1.536]` needed actually contains**, and do not carry 664 into your
own reasoning: it is a different number about a different object. **Never
conclude a count from a command containing `head`.**

**`Relabel` IS THE MEASURED CURE FOR THE NEIGHBOURING PROBLEM AND IT MAY NOT
TRANSFER.** `[LJ-1.514]` used it against the carrier. This is about membership
in a stage. **Re-measure it here or say you did not use it.**

**IF THE CONSTANTS CANNOT BE BOUNDED, SAY SO AND STOP, AND SAY IT LOUDLY.** That
would mean `[LJ-1.560]`'s question is moot for this site, and the mathematician
must know before funding more work on the Δ₀ side.

**DO NOT ATTEMPT THE Δ₀ HYPOTHESIS.** `[LJ-1.560]` has it. AD12 gives this brief
one obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE CONSTANTS, COUNTED`.** How many, which, and
whether each sits in the stage. **A count you measured, not one you inherited.**

**REQUIRED REPORT SECTION `## DOES THE FIRST HYPOTHESIS STILL MATTER`.** Two
sentences. Given your answer, say whether `[LJ-1.560]`'s Δ₀ question is still
worth funding at this site.

ESTIMATE: about 150 lines in the probe, of which the obligation is about 40.
BASIS: `[LJ-1.522]` paid a comparable single cost row. Comparables are of SHAPE
and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the constant list of the actual formula.

    -- the constants of [LJ-1.536]'s formula, enumerated, TYPE ONLY

**Write it FIRST and typecheck it ALONE.** If the formula is not reconstructible
from `[LJ-1.536]`'s probe, say so and state which formula you took instead.
ESTIMATE: about 15 lines, under 60 seconds.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS ONE OF `AtStage`'S TWO HYPOTHESES**, and leaves the campaign with a
single named blocker instead of two.

**A NO-GO MOOTS THE Δ₀ WORK AT THIS SITE**, which would save the campaign from
funding a question whose answer cannot be used.

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
  changed_files_none = ["agents/tasks/LJ-1-562/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-562/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-562/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-562/Probe562.agda"]
  changed_files_none = ["agents/tasks/LJ-1-562/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-562/review-of-*.md"]

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
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 134.076)
- CANDIDATE archive/dev/JOURNAL.md  (score 133.178)
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 130.894)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 118.906)
- CANDIDATE dev/ARCHIVE.md  (score 117.902)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 40.342)
- CANDIDATE dev/literature/devlin-II5.md  (score 34.894)
- CANDIDATE dev/literature/digest.md  (score 34.290)
- CANDIDATE dev/literature/terms-2026-08.md  (score 33.302)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 32.431)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
