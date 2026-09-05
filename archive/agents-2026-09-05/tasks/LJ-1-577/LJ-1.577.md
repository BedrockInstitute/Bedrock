# LJ-1.577: the V = L residue, read out of Devlin and taken off the hypothesis

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-577/Probe577.agda`:

    bounded-subset-internal :
      <`Devlin55.BoundedSubsetAt`'s conclusion, with its cardinality
       hypothesis read INTERNALLY as `IsCardinalL` instead of ambiently
       as `IsCardinal`>

or, if that will not go through, the term that names precisely which step
demands the ambient reading. Land nothing in `src/`.

**`[LJ-1.569]` IS A NO-GO, UPHELD, AND IT DIAGNOSED WHERE ROW 1 CAME FROM.**
Row 1 is `AmbientCardAtSucc`, and `row-1-from-the-converse`
(`agents/tasks/LJ-1-569/Probe569.agda:187-188`) names the demand as one
principle: **an L-cardinal is a cardinal.** That is a statement about the
ambient V and not about L, and the route asks for it at every successor pair the
trophy quantifies over.

**AND IT NAMED THE SOURCE.** In its own words:

> `Devlin55.BoundedSubsetAt` is Devlin II 5.5, and 5.5 opens `Assume V = L`
> (`dev/literature/devlin-II5.md:147`). Under that assumption "κ is a cardinal"
> is ambient and internal at once, so the printed hypothesis does not choose.
> **Bedrock does not assume V = L.** The port kept the ambient reading, and row
> 1 is the residue of an assumption the trophy does not make.

**SO THIS IS A PORT DEFECT AND NOT A MATHEMATICAL WALL, AND THAT IS MY
READING.** I state it as a reading and not as a measurement: **the classical
proof of 5.5 runs inside L and needs κ to be a cardinal OF L only.** This task
finds out whether the tree's port can be read that way.

**THIS BRIEF CARRIES A LITERATURE STEP AND IT IS THE FIRST ONE I HAVE ORDERED
THIS WEEK.** `dev/literature/devlin-II5.md` is the digest and it is where the
`Assume V = L` line sits. **Read 5.5's proof and say which of its steps use the
ambient reading.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-577/Probe577.agda::bounded-subset-internal"]

## SCOPE (write)
- agents/tasks/LJ-1-577/Probe577.agda
- agents/tasks/LJ-1-577/lj-1.577-report.md
- agents/tasks/LJ-1-577/review-of-bounded-subset-internal.md
- agents/tasks/LJ-1-577/runs/

## PREMISES

1. `[LJ-1.569]` is a NO-GO and its critic upheld it. Basis: agents/tasks/LJ-1-569/review-of-LJ-1-569-1.md:1
2. It names the demand as one principle. Basis: agents/tasks/LJ-1-569/Probe569.agda:187
3. Devlin 5.5 opens `Assume V = L`. Basis: dev/literature/devlin-II5.md:147
4. `[LJ-1.550]`'s `site-forced` closes the move-the-site route. Basis: agents/tasks/LJ-1-550/Probe550.agda:385
5. `[LJ-1.94]` supplied `cardκ` from the ambient Hartogs cardinal at ITS site. Basis: archive/dev/LJ-dispatch-index.md:170
6. `IsCardinalL` is stated by `InjCode`, internally. Basis: src/L/Cardinal.lagda.md:230
7. The bounded subset theorem is in the tree. Basis: src/L/BoundedSubset.lagda.md:1621
8. It sits under `levelIn` and `cover`. Basis: src/L/BoundedSubset.lagda.md:1555
9. `[LJ-1.564]`'s bill has this as row 1. Basis: agents/tasks/LJ-1-564/Probe564.agda:456
10. `GCHStatement` names no ambient type. Basis: src/L/GCH.lagda.md:59
11. `[LJ-1.526]` overturned an archived claim about cardinals by measurement. Basis: agents/tasks/LJ-1-526/lj-1.526-report.md:1
12. A stop is a deliverable. Basis: AGENTS.md:43
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

A ported theorem carrying an ambient hypothesis, and a diagnosis of where that
hypothesis came from. **No internal reading anywhere.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE LITERATURE.** Read `dev/literature/devlin-II5.md`
around `:147` and through 5.5's proof. **Say at `file:line` which steps use "κ is
a cardinal" and, for each, whether the step needs the ambient reading or only
the internal one.** That table is the deliverable even if the Agda does not
land.

**DO NOT ASSUME MY READING IS RIGHT.** I said the classical proof runs inside L.
**That is a reading and it is unmeasured.** If a step genuinely needs the
ambient cardinality, say so at `file:line` and stop: the campaign then has a
real mathematical obstruction rather than a port defect, and the owner must
hear which it is.

**DO NOT TRY TO MOVE THE SITE.** `[LJ-1.550]`'s `site-forced` already proves no
other ambient cardinal μ above κ serves, and `[LJ-1.569]` records that the
`[LJ-1.94]` Hartogs route is closed here because `SuccCardL` fixes δ.

**DO NOT WEAKEN THE CONCLUSION.** A theorem that concludes less is a different
theorem and `gch-from-five` will not take it.

**DO NOT ATTEMPT ROWS 2 TO 5.** AD12 gives this brief one obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## WHERE 5.5 USES THE AMBIENT READING`.** The table
from the D-10, one row per step, each at `file:line`.

**REQUIRED REPORT SECTION `## PORT DEFECT OR REAL OBSTRUCTION`.** One paragraph.
**Say which it is, and say it plainly.** The owner is waiting on exactly this
sentence.

**REQUIRED LITERATURE STEP.** Name in a LITERATURE USED section what you read of
`dev/literature/devlin-II5.md` and `dev/literature/devlin-errata.md`, and say
whether the errata record anything about 5.5.

ESTIMATE: about 220 lines in the probe, of which the obligation is about 50.
**This is an uncertain estimate: the task is a re-reading of a ported proof and
nobody has measured how far the ambient reading has spread.** Comparables are of
SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is `BoundedSubsetAt`'s cardinality hypothesis as the tree states it today.

    -- BoundedSubsetAt's cardinality parameter, re-ascribed with IsCardinalL
    -- in place of IsCardinal, TYPE ONLY

**Write it FIRST and typecheck it ALONE.** If the module will not even form with
the internal reading, the answer is in hand in the first hour. ESTIMATE: about
15 lines, under 2 minutes.

## WHAT GO AND NO-GO EACH EARN

**A GO TAKES ROW 1 OFF THE BILL AND REMOVES THE ONLY DEMAND THIS ROUTE MAKES ON
THE AMBIENT UNIVERSE.** It would mean `L ⊨ GCH` is provable here without
assuming V = L, which is the whole point of the trophy.

**A NO-GO THAT NAMES THE STEP IS THE RULING THE OWNER IS WAITING FOR**, and I
will carry it as soon as it lands.

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
  changed_files_none = ["agents/tasks/LJ-1-577/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-577/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-577/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-577/Probe577.agda"]
  changed_files_none = ["agents/tasks/LJ-1-577/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-577/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 209.559)
- CANDIDATE archive/dev/JOURNAL.md  (score 191.612)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 179.736)
- CANDIDATE archive/dev/DD-archived.md  (score 161.519)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 155.446)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 68.277)
- CANDIDATE dev/literature/devlin-II5.md  (score 63.741)
- CANDIDATE dev/literature/geology.md  (score 47.644)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 46.963)
- CANDIDATE dev/literature/digest.md  (score 41.212)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
