# LJ-1.570: levelIn and cover, re-priced at today's tree

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-570/Probe570.agda`:

    cohyps-at-today : <`[LJ-1.550]`'s `CoHyps` supplied at the frame
                       `gch-from-five` calls it, or the term that names
                       precisely what is missing>

`CoHyps` is `Co`'s two parameters, `levelIn` and `cover`
(`agents/tasks/LJ-1-550/Probe550.agda:215-230`,
`src/L/BoundedSubset.lagda.md:1555-1558`). Land nothing in `src/`.

**THIS IS ROW 3 OF FIVE, AND FIVE IS THE WHOLE REMAINING BILL.** `[LJ-1.564]`
is GO and `gch-from-five` (`agents/tasks/LJ-1-564/Probe564.agda:456-463`)
machine-checks that `GCHStatement` follows from exactly five rows.

**THE ARCHIVE PRICES THIS PAIR AS A WALL AND EVERY ONE OF THOSE PRICES IS
OLD.** They survived as hypotheses since `[LJ-1.7]`
(`archive/dev/LJ-dispatch-index.md:95`), outlived two cure campaigns (`:97`,
`:100`), and were priced twice: `[LJ-1.121]` found them "NEITHER REFUTABLE,
NEITHER SUPPLIED" against a level-hood certificate at 2.8k to 3.3k lines
(`:198`), and `[LJ-1.146]` called them "A WALL, NAMED TWICE AT ONE TERM" at
about 1.0k lines (`:222`). **NOTHING MAY BE FUNDED AGAINST THOSE NUMBERS.**
They are here so you know the shape of what you are looking at.

**WHY IT IS WORTH ASKING AGAIN NOW.** The tree has changed under them for four
hundred dispatches, and the pair has never been re-measured since. **`[LJ-1.543]`
found that a row everybody assumed needed the bounded subset theorem did not
need it at all**, and `[LJ-1.526]` overturned an archived claim about cardinals
by reading the source. **A re-measurement is cheap and the old number is not
evidence about today.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-570/Probe570.agda::cohyps-at-today"]

## SCOPE (write)
- agents/tasks/LJ-1-570/Probe570.agda
- agents/tasks/LJ-1-570/lj-1.570-report.md
- agents/tasks/LJ-1-570/review-of-cohyps.md
- agents/tasks/LJ-1-570/runs/

## PREMISES

1. `[LJ-1.564]` is GO and its bill is five rows. Basis: agents/tasks/LJ-1-564/Probe564.agda:456
2. `CoHyps` is row 3. Basis: agents/tasks/LJ-1-550/Probe550.agda:215
3. It is `Co`'s two parameters. Basis: src/L/BoundedSubset.lagda.md:1555
4. The theorem sits under them. Basis: src/L/BoundedSubset.lagda.md:1621
5. They have been hypotheses since `[LJ-1.7]`. Basis: archive/dev/LJ-dispatch-index.md:95
6. `[LJ-1.121]` found them neither refutable nor suppliable. Basis: archive/dev/LJ-dispatch-index.md:198
7. `[LJ-1.146]` priced them at about 1.0k lines. Basis: archive/dev/LJ-dispatch-index.md:222
8. `[LJ-1.543]` found a sibling row did not need the theorem. Basis: agents/tasks/LJ-1-543/lj-1.543-report.md:1
9. `[LJ-1.526]` overturned an archived claim by measurement. Basis: agents/tasks/LJ-1-526/lj-1.526-report.md:1
10. `[LJ-1.560]` is GO and its obligation was an instantiation. Basis: agents/tasks/LJ-1-560/lj-1.560-report.md:1
11. A stop is a deliverable. Basis: AGENTS.md:43
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

A theorem under two hypotheses, and two old prices for supplying them. **No
measurement at today's tree.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE INVENTORY.** State `levelIn` and `cover`
at the frame `gch-from-five` calls them and say at `file:line` **what each one
asks for in the tree as it stands today.** Then say, for each, whether anything
delivered since `[LJ-1.146]` supplies it. **`[LJ-1.560]`'s reflection step is the
most likely candidate and nobody has tried it against this pair.**

**IF THEY ARE STILL NOT SUPPLIABLE, PRICE THEM AT TODAY'S TREE.** That is the
deliverable in the NO-GO case: a line count you measured, not one you inherited.
**Say plainly that it supersedes the archive's numbers, or that it agrees with
them.**

**DO NOT BUILD A LEVEL-HOOD CERTIFICATE.** If that is what is wanted, name it
and stop. The archive says it was priced at 2.8k to 3.3k lines and not built,
and this brief does not fund it.

**DO NOT ATTEMPT ROWS 1, 2, 4 OR 5.** AD12 gives this brief one obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## WHAT EACH ASKS FOR TODAY`.** One paragraph each,
at `file:line`, with a mark saying supplied, suppliable or not.

**REQUIRED REPORT SECTION `## THE PRICE I MEASURED`.** A number, or the sentence
that you did not measure one and why.

ESTIMATE: about 160 lines in the probe, of which the obligation is about 40.
BASIS: `[LJ-1.543]` and `[LJ-1.564]` worked against the same chapter. **The
estimate covers the INVENTORY and a supply attempt, not a certificate.**
Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is `levelIn` at the frame `gch-from-five` uses.

    -- levelIn, re-ascribed at that frame, TYPE ONLY, no inhabitant

**Write it FIRST and typecheck it ALONE.** ESTIMATE: about 12 lines, under 90
seconds.

## WHAT GO AND NO-GO EACH EARN

**A GO TAKES THE BILL FROM FIVE ROWS TO FOUR** and closes a wall that has stood
since `[LJ-1.7]`.

**A NO-GO WITH A MEASURED PRICE REPLACES A FOUR-HUNDRED-DISPATCH-OLD NUMBER**
with one the mathematician can actually plan against.

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
  changed_files_none = ["agents/tasks/LJ-1-570/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-570/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-570/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-570/Probe570.agda"]
  changed_files_none = ["agents/tasks/LJ-1-570/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-570/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 276.440)
- CANDIDATE archive/dev/JOURNAL.md  (score 243.321)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 237.606)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 198.459)
- CANDIDATE archive/dev/DD-archived.md  (score 197.986)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 75.096)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 59.673)
- CANDIDATE dev/literature/digest.md  (score 52.340)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 46.364)
- CANDIDATE dev/literature/geology.md  (score 44.946)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
