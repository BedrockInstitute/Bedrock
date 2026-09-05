# LJ-1.609: face E at the six slots that are missing, with seventeen already built

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-609/Probe609.agda`:

    elem-down-at : <`ElemDownAt`, face E of `[LJ-1.606]`'s `Crossing`>
      (`agents/tasks/LJ-1-606/Probe606.agda:147-149`)

Land nothing in `src/`.

**`[LJ-1.606]` IS GO AND IT BUILT THE COMMUTE, THEN NAMED EXACTLY WHAT THE
COMMUTE LACKS.** Row 3's certificate had failed at all three clauses;
`[LJ-1.602]` found they "share one root, the absence of any crossing from an
inner world to the ambient tower"; `[LJ-1.606]` built that crossing and reported
**three faces, each one named type, each consumed by the term and by nothing
else** (`agents/tasks/LJ-1-606/lj-1.606-report.md:119-131`).

**FACE E IS THE MOST BOUNDED OF THE THREE AND THAT IS WHY IT GOES FIRST:**

> **E `ElemDownAt`**: elementarity down at the hull, all arities;
> `DownReflect.ElemDown` (`src/L/BoundedSubset.lagda.md:410`).
> **UNBUILT at six slots; DELIVERED at `[LJ-1.570]`'s seventeen**
> (`agents/tasks/LJ-1-578/Probe578.agda:413-427`).

**SEVENTEEN OF TWENTY-THREE ARE ALREADY IN THE TREE.** `elem-down-taken`
(`agents/tasks/LJ-1-578/Probe578.agda:413`) is the delivered form. **Your task is
the six, not the twenty-three.**

**AND THE KIT IS PROVED NON-VACUOUS, WHICH MATTERS BEFORE YOU SPEND ANYTHING.**
`[LJ-1.606]` showed the faces **cannot be filled with junk, both ways, as terms**
(`Probe606.agda:260-285`): a TRUE matrix fails G- outright, because at the
ordinal `∅` it would force every level. **So face E is not a formality.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-609/Probe609.agda::elem-down-at"]

## SCOPE (write)
- agents/tasks/LJ-1-609/Probe609.agda
- agents/tasks/LJ-1-609/lj-1.609-report.md
- agents/tasks/LJ-1-609/review-of-elem-down-at.md
- agents/tasks/LJ-1-609/runs/

## PREMISES

1. `[LJ-1.606]` is GO and built the commute. Basis: agents/tasks/LJ-1-606/lj-1.606-report.md:193
2. It names three faces with statuses. Basis: agents/tasks/LJ-1-606/lj-1.606-report.md:119
3. Face E is stated at its probe. Basis: agents/tasks/LJ-1-606/Probe606.agda:147
4. `DownReflect.ElemDown` is the tree's form. Basis: src/L/BoundedSubset.lagda.md:410
5. `elem-down-taken` is delivered at seventeen slots. Basis: agents/tasks/LJ-1-578/Probe578.agda:413
6. The kit cannot be filled with junk. Basis: agents/tasks/LJ-1-606/Probe606.agda:260
7. `[LJ-1.602]` found the shared root of row 3's three failures. Basis: agents/tasks/LJ-1-602/lj-1.602-report.md:1
8. `[LJ-1.598]` is a NO-GO on clause (i). Basis: agents/tasks/LJ-1-598/lj-1.598-report.md:1
9. `[LJ-1.595]` is a NO-GO on clause (ii). Basis: agents/tasks/LJ-1-595/review-of-defines-cover.md:1
10. `[LJ-1.570]` measured 41 lines for the piece below row 3. Basis: agents/tasks/LJ-1-570/Probe570.agda:251
11. R-42 rules the respelling cost. Basis: dev/LESSONS.md:4404
12. A stop is a deliverable. Basis: AGENTS.md:43
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

A built commute, a non-vacuity proof for its kit, and seventeen of face E's
slots. **Six slots are missing.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS WHICH SIX.** Read `elem-down-taken`
(`agents/tasks/LJ-1-578/Probe578.agda:413-427`) and face E's statement
(`agents/tasks/LJ-1-606/Probe606.agda:147-149`) and **name the six missing slots
at `file:line`.** Report the number you measured; **if it is not six, take
yours and say so.**

**IMPORT THE SEVENTEEN. DO NOT RESTATE THEM.** R-42 measures a cross-file
respelling of one object at 1.74 s against 155.02 s, and it was written from
this campaign's own runs. **Say which lines you took.**

**IF A MISSING SLOT NEEDS SOMETHING THE OTHER SEVENTEEN DID NOT, NAME IT AND
STOP.** Seventeen delivered and six not is a pattern, not an accident: **the six
may differ in kind, and saying how is worth more than a partial build.**

**DO NOT BUILD FACES G+ OR G-.** AD12 gives this brief one obligation, and the
other two faces are separately queued.

**CAP EVERY TYPECHECK ON A WALL CLOCK YOU SET AND REPORT THE CAP.** Report peak
RSS too: `[LJ-1.582]` heap-walled on this family.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE SIX, NAMED`.** Each at `file:line`, each marked
built or not, with what it needed.

**REQUIRED REPORT SECTION `## WHAT THE CROSSING NOW WANTS`.** Of the three faces,
say which are paid after this task. **Do not read a discharge into anything you
did not inhabit**, the standard `[LJ-1.606]` set when it wrote "NOTHING BELOW
READS A DISCHARGE INTO AN UNBUILT FACE".

ESTIMATE: about 180 lines in the probe, of which the obligation is about 45.
BASIS: `[LJ-1.578]` delivered the seventeen at a comparable size. Comparables are
of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is what the six have in common.

    -- the six missing slots, listed by name with their arities, TYPE ONLY

**Write it FIRST, typecheck it ALONE, cap it.** ESTIMATE: about 12 lines, cap at
two minutes.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS ONE OF THE THREE FACES OF THE CROSSING** that row 3's three failures
all reduce to.

**A NO-GO THAT SAYS HOW THE SIX DIFFER FROM THE SEVENTEEN IS WORTH AS MUCH**,
because it would say face E is two objects and not one.

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
  changed_files_none = ["agents/tasks/LJ-1-609/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-609/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-609/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-609/Probe609.agda"]
  changed_files_none = ["agents/tasks/LJ-1-609/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-609/review-of-*.md"]

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
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 192.114)
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 185.593)
- CANDIDATE archive/dev/JOURNAL.md  (score 158.561)
- CANDIDATE dev/ARCHIVE.md  (score 146.371)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 142.125)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 67.735)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 61.504)
- CANDIDATE dev/literature/terms-2026-08.md  (score 44.383)
- CANDIDATE dev/literature/digest.md  (score 36.946)
- CANDIDATE dev/literature/geology.md  (score 34.468)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
