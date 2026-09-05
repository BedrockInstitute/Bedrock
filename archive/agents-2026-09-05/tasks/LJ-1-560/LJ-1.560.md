# LJ-1.560: bound one unbounded search to a stage

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-560/Probe560.agda`:

    search-bounds :
      <given a predicate on L-sets that is satisfied somewhere in L,
       a stage β whose Lset already holds a witness>

**State the predicate's form yourself**, as generally as you can make it true.
Land nothing in `src/`. **This is a REFLECTION step and nothing more.**

**BOTH LEGS OF THE CAMPAIGN ARE BLOCKED ON THE SAME THING AND THEY REACHED IT
INDEPENDENTLY.**

- **GCH leg.** `[LJ-1.557]` is GO and built the pointwise internal code, then
  measured that it does not reach the uniform assignment: the formula would have
  to describe `leastOf` at `w` over the code predicate, **"which is a quantifier
  over the whole L-carrier and not over a stage"**
  (`agents/tasks/LJ-1-557/lj-1.557-report.md`, `## POINTWISE AGAINST UNIFORM`).
- **Condensation leg.** `[LJ-1.536]` is a NO-GO at the door. `𝒟ₒ-intro`
  (`src/L/Constructible.lagda.md:301-304`) is the one route into a stage and
  `defSet` reads its formula under the world's INNER satisfaction
  (`src/L/Definability.lagda.md:111-112`), so **"every quantifier in it ranges
  over the members of the stage and over nothing else."** The one bridge is
  `L.Axioms.Separation.AtStage` (`src/L/Axioms/Separation.lagda.md:119-135`)
  and its first hypothesis is that the formula is **Δ₀** (`:199-206`).

**AN UNBOUNDED SEARCH IS NOT Δ₀. A SEARCH BOUNDED BY A STAGE IS.** That is the
whole reason this task exists.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-560/Probe560.agda::search-bounds"]

## SCOPE (write)
- agents/tasks/LJ-1-560/Probe560.agda
- agents/tasks/LJ-1-560/lj-1.560-report.md
- agents/tasks/LJ-1-560/review-of-search-bounds.md
- agents/tasks/LJ-1-560/runs/

## PREMISES

1. `[LJ-1.557]` is GO and names the unbounded quantifier. Basis: agents/tasks/LJ-1-557/lj-1.557-report.md:1
2. `[LJ-1.536]` is a NO-GO at the door. Basis: agents/tasks/LJ-1-536/lj-1.536-report.md:1
3. `𝒟ₒ-intro` is the one route into a stage. Basis: src/L/Constructible.lagda.md:301
4. `defSet` reads under the world's inner satisfaction. Basis: src/L/Definability.lagda.md:111
5. `AtStage` is the one external-to-inner bridge. Basis: src/L/Axioms/Separation.lagda.md:119
6. Its first hypothesis is Δ₀. Basis: src/L/Axioms/Separation.lagda.md:199
7. Σ₁ has an unbounded-quantifier constructor. Basis: src/FOL/LevyHierarchy.lagda.md:75
8. `Ladder` builds an ω-indexed union of ordinals with its rungs inside it. Basis: src/L/Reflect.lagda.md:256
9. Its `top-ord` gives that union ordinality. Basis: src/L/Reflect.lagda.md:271
10. `[LJ-1.544]` used `Ladder` to build a limit above a stage. Basis: agents/tasks/LJ-1-544/lj-1.544-report.md:1
11. `[LJ-1.516]` found the Levy grade to be the real obstruction on a sibling row. Basis: agents/tasks/LJ-1-516/lj-1.516-report.md:1
12. A stop is a deliverable. Basis: AGENTS.md:43
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

`src/L/Reflect.lagda.md` exists and `[LJ-1.544]` used its `Ladder` to build a
limit ordinal above a stage, with the rungs inside it. **Nothing in the campaign
has used it to bound a SEARCH.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS WHAT `src/L/Reflect.lagda.md` ALREADY
PROVES.** Read the whole chapter and say at `file:line` whether it contains a
reflection principle, or only the `Ladder` construction. **If a reflection
principle is already there, this task is an instantiation and you say so at
once.** `[LJ-1.526]` overturned an archived claim by reading the source rather
than the summary, and `[LJ-1.544]` found `Ladder` fit a row nobody expected.

**STATE THE PREDICATE AS A `Formula`, NOT AS AN AGDA FUNCTION.** The whole point
is the object language. A term that bounds a meta-level search proves nothing
about `defSet`, and `[LJ-1.533]`, `[LJ-1.549]`, `[LJ-1.552]` and `[LJ-1.554]`
each stopped at exactly that boundary. **Say in the report which side of it your
term lives on.**

**A TRUNCATED CONCLUSION IS FINE.** You are not asked for the least such β.

**IF REFLECTION IS NOT AVAILABLE, NAME WHAT IT WOULD COST.** That is the
deliverable in the NO-GO case and it is what the mathematician needs to fund the
next brief. Do not build a partial one.

**DO NOT ATTEMPT `StageHigh`, `Link`, OR THE ASSIGNMENT.** AD12 gives this brief
one obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## WHAT REFLECT ALREADY HAS`.** The chapter's
contents against this obligation, at `file:line`.

**REQUIRED REPORT SECTION `## WHICH SIDE OF THE BOUNDARY`.** Two sentences. Say
whether your term bounds a search in the OBJECT language or in Agda, and if the
latter, say what remains before `AtStage` would accept it.

ESTIMATE: about 170 lines in the probe, of which the obligation is about 45.
BASIS: `[LJ-1.544]` used the same chapter for a comparable construction.
**This estimate is uncertain: reflection is the classical tool here and the
tree's stock of it is unmeasured.** Comparables are of SHAPE and nothing may be
funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is whether `src/L/Reflect.lagda.md` already proves a reflection principle.

    -- the chapter's strongest statement about a formula holding at a stage,
    -- re-ascribed, TYPE ONLY

**Write it FIRST and typecheck it ALONE.** If the chapter already has it, the
estimate above is far too high and you should say so and finish early.
ESTIMATE: about 15 lines, under 2 minutes.

## WHAT GO AND NO-GO EACH EARN

**A GO IS THE MOST VALUABLE SINGLE RESULT THIS CAMPAIGN COULD PRODUCE**, because
two legs are blocked on it and `[LJ-1.561]` is measuring whether five stopped
sites are one wall.

**A NO-GO THAT PRICES REFLECTION IS A RULING**, and the mathematician will carry
it to the owner as the cost of the remaining route.

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
  changed_files_none = ["agents/tasks/LJ-1-560/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-560/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-560/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-560/Probe560.agda"]
  changed_files_none = ["agents/tasks/LJ-1-560/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-560/review-of-*.md"]

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
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 175.319)
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 172.620)
- CANDIDATE archive/dev/JOURNAL.md  (score 170.000)
- CANDIDATE dev/ARCHIVE.md  (score 134.740)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 127.656)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 62.112)
- CANDIDATE dev/literature/digest.md  (score 56.079)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 55.060)
- CANDIDATE dev/literature/geology.md  (score 40.119)
- CANDIDATE dev/literature/terms-2026-08.md  (score 39.073)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
