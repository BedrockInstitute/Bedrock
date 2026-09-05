# LJ-1.613: ingredients (i) and (ii), which two tasks called internal and nobody checked

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-613/Probe613.agda`:

    first-two-internal : <ingredients (i) and (ii) of `[LJ-1.594]`'s
                          `class-pred` table, instantiated at this carrier>

Land nothing in `src/`.

**THREE OF THE FIVE INGREDIENTS ARE SETTLED AND TWO ARE ASSERTED.** The
`class-pred` formula's five, after this week:

| ingredient | state |
|---|---|
| (i) | **"already internal"**, `[LJ-1.594]`. Never instantiated here |
| (ii) | **"already internal"**, `[LJ-1.594]`. Never instantiated here |
| (iii) the pairing | INSIDE the circle `[LJ-1.607]` confirmed as a term |
| (iv) | **PAID**: base by `[LJ-1.601]`, limit by `[LJ-1.608]` |
| (v) `keyS` | **PAID** by `[LJ-1.600]` |

**"ALREADY INTERNAL" IS A JUDGEMENT AND NOT A MEASUREMENT.** `[LJ-1.594]` wrote
it while its own obligation was failing, and its route line says (i) and (ii)
come after (v). **(v) is now paid, so the order permits this and nothing blocks
it.**

**THE CAMPAIGN HAS BEEN WRONG ABOUT "ALREADY THERE" BEFORE.** `[LJ-1.607]`
looked for `pick-canonical`, which `archive/dev/LJ-dispatch-index.md:212` records
as a delivered cure, and found it exists in **no Agda anywhere**. **A recorded
claim is not a term.**

**THIS TASK IS OUTSIDE THE CIRCLE.** (iii) is inside it and is not yours.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-613/Probe613.agda::first-two-internal"]

## SCOPE (write)
- agents/tasks/LJ-1-613/Probe613.agda
- agents/tasks/LJ-1-613/lj-1.613-report.md
- agents/tasks/LJ-1-613/review-of-first-two-internal.md
- agents/tasks/LJ-1-613/runs/

## PREMISES

1. `[LJ-1.594]` states the five ingredients and their order. Basis: agents/tasks/LJ-1-594/review-of-pairing-suffices.md:138
2. It calls (i) and (ii) already internal. Basis: agents/tasks/LJ-1-594/review-of-pairing-suffices.md:79
3. `[LJ-1.600]` is GO and paid (v). Basis: agents/tasks/LJ-1-600/lj-1.600-report.md:1
4. `[LJ-1.601]` is GO and paid (iv)'s base. Basis: agents/tasks/LJ-1-601/lj-1.601-report.md:1
5. `[LJ-1.608]` is GO and paid (iv)'s limit. Basis: agents/tasks/LJ-1-608/lj-1.608-report.md:1
6. `[LJ-1.607]` confirmed the circle as a term. Basis: agents/tasks/LJ-1-607/lj-1.607-report.md:173
7. It found a recorded cure with no surviving code. Basis: archive/dev/LJ-dispatch-index.md:212
8. `defSet` is `𝒟ₒ` in that module. Basis: src/L/StageCardinal.lagda.md:400
9. The least-element selection is the ordinal order. Basis: src/L/StageCardinal.lagda.md:258
10. `hasSeparationL` takes an arbitrary formula. Basis: src/L/Axioms/Full.lagda.md:144
11. R-42 rules the respelling cost. Basis: dev/LESSONS.md:4404
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

Three of five ingredients, and two asserted to be free. **Neither assertion has
been instantiated at this carrier.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE TWO CLAIMS.** Read `[LJ-1.594]`'s table
and say at `file:line` **exactly what (i) and (ii) are** and what "already
internal" was claimed to mean. **Then instantiate each at this carrier.**

**IF EITHER IS NOT ACTUALLY INTERNAL, THAT IS THE RESULT AND IT IS A BIG ONE.**
The campaign has been treating three of five as done. **Say which, and say it
plainly.**

**IMPORT `[LJ-1.600]`'s (v) RATHER THAN RESTATING IT.** R-42 measures a
cross-file respelling of one object at 1.74 s against 155.02 s.

**DO NOT TOUCH (iii).** `[LJ-1.607]` proved the circle as a term and
`[LJ-1.593]` forbade a fourth square-law dispatch. **A sixth arrival at that
point is not funded.**

**CAP EVERY TYPECHECK ON A WALL CLOCK YOU SET AND REPORT THE CAP.**

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE TWO CLAIMS, TESTED`.** One row each, at
`file:line`, marked instantiated or not.

**REQUIRED REPORT SECTION `## WHAT THE FORMULA NOW WANTS`.** Of the five, say
which are paid after this task. **Count, and do not read a discharge into
anything you did not inhabit.**

ESTIMATE: about 150 lines in the probe, of which the obligation is about 40.
**If both are genuinely internal, far less, and I would rather be wrong that way
than fund a rebuild.** Comparables are of SHAPE and nothing may be funded
against them.

## W3, THE WIDEST UNMEASURED TERM

It is ingredient (i) at this carrier.

    -- (i), re-ascribed at this carrier, TYPE ONLY, capped

**Write it FIRST, typecheck it ALONE, cap it.** ESTIMATE: about 12 lines, cap at
two minutes.

## WHAT GO AND NO-GO EACH EARN

**A GO LEAVES THE `class-pred` FORMULA WANTING ONLY (iii)**, which is the piece
inside the circle, and makes the circle the campaign's single named blocker
rather than one of several.

**A NO-GO SHOWING (i) OR (ii) IS NOT INTERNAL RE-OPENS AN INGREDIENT THE
CAMPAIGN HAS COUNTED AS FREE FOR A WEEK.**

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
  changed_files_none = ["agents/tasks/LJ-1-613/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-613/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-613/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-613/Probe613.agda"]
  changed_files_none = ["agents/tasks/LJ-1-613/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-613/review-of-*.md"]

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
- CANDIDATE archive/dev/JOURNAL.md  (score 177.739)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 174.595)
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 174.541)
- CANDIDATE archive/dev/DD-archived.md  (score 153.550)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 150.331)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 50.849)
- CANDIDATE dev/literature/digest.md  (score 48.103)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 46.439)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 44.196)
- CANDIDATE dev/literature/primary-sources.md  (score 33.379)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
