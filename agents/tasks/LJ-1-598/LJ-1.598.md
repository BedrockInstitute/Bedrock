# LJ-1.598: clause (i) again, in a frame that fits under the cap

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-598/Probe598.agda`:

    defines-level : <`Cert.DefinesLevel`, clause (i) of the level-hood
                     certificate>
      (`agents/tasks/LJ-1-578/Probe578.agda:234-240`)

**Clause (i) only.** Land nothing in `src/`.

**`[LJ-1.582]` HIT THE HEAP WALL AND PARKED.** Its row is
`task-lj-1-582-heap-wall-park`. **That is not a refutation and I do not treat it
as one.** The clause is still open and the question is unchanged.

**THE HEAP IS THE RISK AND IT IS MEASURABLE.** `[LJ-1.545]` measured the heap
LINEAR in field count at one caliber, 28 fields at 12.46 percent of the 8 GiB
cap (`agents/tasks/LJ-1-545/lj-1.545-report.md`). `[LJ-1.559]` measured a floor
of 1.39 s warm and 4.12 s cold in a TRIMMED frame and used that to rule the
frame out as the cause of two timeouts. **Do the same here: measure the floor
before you prove anything.**

**WHAT THE CLAUSE IS.** `[LJ-1.578]` named row 3's remainder as ONE object with
THREE clauses (`agents/tasks/LJ-1-578/Probe578.agda:525-534`), which are
**Devlin's own chain split at the tree's joints**. Clause (i) says: at the
STAGE's inner world, a formula over hull codes has `Lset δ` as its only witness.
It is **Devlin's (b)** (`dev/literature/devlin-II5.md:99`).

**`[LJ-1.595]` WENT AT CLAUSE (ii) AND RETURNED A NO-GO.** Read its stop before
you start: it may have measured something about the family that saves you time.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-598/Probe598.agda::defines-level"]

## SCOPE (write)
- agents/tasks/LJ-1-598/Probe598.agda
- agents/tasks/LJ-1-598/lj-1.598-report.md
- agents/tasks/LJ-1-598/review-of-defines-level.md
- agents/tasks/LJ-1-598/runs/

## PREMISES

1. `[LJ-1.582]` parked at the heap wall. Basis: dev/pod/transitions/2026-08.jsonl:3418
2. `[LJ-1.578]` names the remainder as three clauses. Basis: agents/tasks/LJ-1-578/Probe578.agda:525
3. Clause (i) is stated at its probe. Basis: agents/tasks/LJ-1-578/Probe578.agda:234
4. Clause (i) is Devlin's (b). Basis: dev/literature/devlin-II5.md:99
5. `[LJ-1.595]` is a NO-GO on clause (ii). Basis: agents/tasks/LJ-1-595/review-of-defines-cover.md:1
6. `[LJ-1.545]` measured the heap linear in field count. Basis: agents/tasks/LJ-1-545/lj-1.545-report.md:1
7. `[LJ-1.559]` measured a floor in a trimmed frame. Basis: agents/tasks/LJ-1-559/lj-1.559-report.md:1
8. `[LJ-1.562]` measured both `AtStage` hypotheses payable at a sibling formula. Basis: agents/tasks/LJ-1-562/lj-1.562-report.md:1
9. `AtStage` is the one external-to-inner bridge. Basis: src/L/Axioms/Separation.lagda.md:119
10. `𝒟ₒ-intro` is the one route into a stage. Basis: src/L/Constructible.lagda.md:301
11. `[LJ-1.75]` measured a trimmed telescope better than proportional. Basis: archive/dev/LJ-dispatch-index.md:142
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

A typed statement of all three clauses, everything on row 3 below them, and one
parked attempt that left no report.

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE FLOOR.** State `defines-level` with a
hole in the smallest import set that holds it. **Record the typecheck time and
peak RSS and report both.** If the floor is already near the cap, say so at once.

**TRIM. `[LJ-1.75]`'S CURE IS MEASURED**, 41.6 percent cheaper for a 37.7 percent
smaller telescope (`archive/dev/LJ-dispatch-index.md:142`). **That is an old
price at an old tree and nothing may be funded against it**, but the method is
the method.

**DO NOT SET `GHCRTS` YOURSELF.** Use the caliber the program sets on your pane,
one Agda process at a time, and say so.

**WRITE THE REPORT AS A SKELETON FIRST AND FILL IT AS RUNS LAND.** `[LJ-1.582]`
left nothing. **Do not be the second on this clause.**

**READ `[LJ-1.595]`'s STOP FIRST.** It attacked the sibling clause. **If it
measured that the two are not siblings, say so and re-price this one.**

**`[LJ-1.562]` PAID BOTH `AtStage` HYPOTHESES AT A DIFFERENT FORMULA.**
**Re-measure Δ₀-ness and the constants here.**

**DO NOT BUILD CLAUSES (ii) OR (iii).** AD12 gives this brief one obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE FLOOR`.** Empty-body time and peak RSS, and the
finished term's if you get there.

**REQUIRED REPORT SECTION `## THE FORMULA AND ITS UNIQUENESS`.** The formula, and
how you proved `Lset δ` is its ONLY witness. **Uniqueness is the hard half.**

ESTIMATE: about 200 lines in the probe, of which the obligation is about 50.
**The heap, not the line count, is the risk, and that is why the floor comes
first.** Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is uniqueness, not existence.

    -- "Lset δ is the ONLY witness", stated alone at the inner world, TYPE ONLY

**Write it FIRST, typecheck it ALONE, and time it.** ESTIMATE: about 15 lines.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS ONE OF THE THREE CLAUSES OF A CERTIFICATE THAT HAS BLOCKED THIS TREE
SINCE `[LJ-1.7]`**, and gives the first real price for the other two.

**A NO-GO WITH A MEASURED FLOOR IS STILL A RESULT**, because two dispatches on
row 3's certificate have now ended without a number.

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
  changed_files_none = ["agents/tasks/LJ-1-598/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-598/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-598/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-598/Probe598.agda"]
  changed_files_none = ["agents/tasks/LJ-1-598/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-598/review-of-*.md"]

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
  Full entry: dev/LESSONS.md:2299
- **P-l. A statement may be ABOUT a concrete stage without dragging that stage's PRESENTATION into its type**
  **The law.** Being about a concrete position is not what costs. Naming a transparent construction in a statement's TYPE is. If the tower's stage values are `opaque` upstream, a theorem may quantify over, hypothesize about and conclude at `Sset ω` freely, because the stage is an ATOM to the elaborator and nothing unfolds. If instead the type mentions a transparent presentation, such as `⟪ sucV (...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2359
- **D-26. A well-founded key on a tower needs generation data, or it needs syntax**
  **Rule:** When a route must well-order a cumulative tower's stage, ask first what the stage's members CARRY. A stage built as the values of finitely many total operations carries its own generation data, so a well-founded key exists with NO syntax at all: the operation index, then the arguments, ordered recursively. A stage built as a definable power carries nothing: its members are sets, not c...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:1735
- **C-42. A refutation measures the site it names, and it never measures how far that site extends**
  **Rule:** A refutation is a measurement of ONE site. It says the statement there is false. **It says nothing about how many other sites carry the same false shape.** So when a refutation lands, the next action is not the cure. **It is the sweep: search the tree for the shape, and report the COUNT before you price the cure.** A cure funded against the named site is priced against a number nobody...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:3754

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev, archive/scripts, dev/ARCHIVE.md:
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 255.310)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 244.993)
- CANDIDATE archive/dev/JOURNAL.md  (score 231.530)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 181.179)
- CANDIDATE archive/dev/PLAN-archived.md  (score 178.293)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 60.205)
- CANDIDATE dev/literature/digest.md  (score 59.876)
- CANDIDATE dev/literature/devlin-II5.md  (score 56.066)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 40.853)
- CANDIDATE dev/literature/terms-2026-08.md  (score 39.501)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
