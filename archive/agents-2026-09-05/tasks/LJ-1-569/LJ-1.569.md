# LJ-1.569: row 1, the ambient cardinality that came back

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-569/Probe569.agda`:

    gch-without-row-1 :
      <`GCHStatement`'s conclusion, from `[LJ-1.564]`'s `gch-from-five`
       with `AmbientCardAtSucc` REMOVED from the hypotheses>

**If it will not build, the deliverable is the site where row 1 is really
used**, stated as a term whose type names it and nothing else. Land nothing in
`src/`.

**`[LJ-1.564]` IS GO AND IT MACHINE-CHECKED THE WHOLE REMAINING BILL.**
`gch-from-five` (`agents/tasks/LJ-1-564/Probe564.agda:456-463`) takes five rows
and returns `GCHStatement zf`. Row 1 is

    AmbientCardAtSucc = (κ δ : SL.S) → SuccCardL δ κ → IsCardinal (fst δ)

(`agents/tasks/LJ-1-550/Probe550.agda:301-302`): **δ is a cardinal AMBIENTLY.**

**I REPORTED LAST HOUR THAT THE AMBIENT FACT WAS OFF THE BILL. THAT WAS WRONG
AND I CORRECT IT HERE.** `[LJ-1.558]`'s three hypotheses hid it inside
`PowerIntoSucc`; paying `PowerIntoSucc` exposed it again as row 1.

**AND THE MATHEMATICS SAYS IT SHOULD NOT BE THERE.** δ is a cardinal OF L.
Nothing makes it a cardinal of V. **`L ⊨ GCH` is a theorem about L**, and
`GCHStatement` names no ambient type (`src/L/GCH.lagda.md:59-70`, and the
chapter says so at `:57-58`). **A route that needs δ to be a real cardinal is
proving something stronger than the trophy.**

**`[LJ-1.558]` MADE THIS EXACT MOVE FOR B5 AND IT WORKED.** `[LJ-1.550]` had
proved the ambient fact unavoidable for `[LJ-1.523]`'s bridge; `[LJ-1.558]`
found a route that never lands inside `Lset δ` and dropped it. **This brief asks
the same question one level down.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-569/Probe569.agda::gch-without-row-1"]

## SCOPE (write)
- agents/tasks/LJ-1-569/Probe569.agda
- agents/tasks/LJ-1-569/lj-1.569-report.md
- agents/tasks/LJ-1-569/review-of-gch-without-row-1.md
- agents/tasks/LJ-1-569/runs/

## PREMISES

1. `[LJ-1.564]` is GO and `gch-from-five` is its bill. Basis: agents/tasks/LJ-1-564/Probe564.agda:456
2. Row 1 is the ambient cardinality at the successor. Basis: agents/tasks/LJ-1-550/Probe550.agda:301
3. `[LJ-1.550]` proves the site cannot be moved for ITS bridge. Basis: agents/tasks/LJ-1-550/review-of-bridge-without-B5.md:21
4. `[LJ-1.558]` is GO and dropped the ambient fact by re-routing. Basis: agents/tasks/LJ-1-558/lj-1.558-report.md:1
5. `GCHStatement` names no ambient type. Basis: src/L/GCH.lagda.md:59
6. The chapter says no ambient function type crosses the boundary. Basis: src/L/GCH.lagda.md:57
7. `IsCardinalL` is stated by `InjCode`, internally. Basis: src/L/Cardinal.lagda.md:230
8. Readback makes an ambient cardinal an L-cardinal. Basis: src/L/CantorBernstein.lagda.md:33
9. `[LJ-1.526]` overturned an archived claim about cardinals by measurement. Basis: agents/tasks/LJ-1-526/lj-1.526-report.md:1
10. `[LJ-1.528]` built `CardAboveL` under `--safe` with no choice. Basis: agents/tasks/LJ-1-528/Probe528.agda:638
11. A stop is a deliverable. Basis: AGENTS.md:43
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

A five-row bill, machine-checked, and a precedent for removing exactly this kind
of row from it.

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE USE SITE.** Read `[LJ-1.564]`'s probe and
`[LJ-1.550]`'s and say at `file:line` **every place `AmbientCardAtSucc` is
consumed.** Name the step and say what it needs the ambient cardinality FOR.

**DO NOT PROVE ROW 1 AND DO NOT REFUTE IT.** Whether δ is a real cardinal is not
settled inside this development, and a task that tries will spend its estimate
on a question the tree cannot answer. **The obligation is the bill WITHOUT it.**

**CHANGE EXACTLY ONE THING.** If you weaken another row to make it go through,
the result is about a different bill and says nothing. Say in the report that
the other four are untouched, or say precisely what you changed.

**READBACK IS THE SUSPECT AND IT CUTS BOTH WAYS.** `src/L/CantorBernstein.lagda.md:33`
turns an ambient cardinal into an L-cardinal. **Say whether the consuming step
wants that direction or its converse.** `[LJ-1.550]`'s `site-forced` turned on
exactly this.

**DO NOT ATTEMPT ROWS 2 TO 5.** They stay as hypotheses here. AD12 gives this
brief one obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## WHERE ROW 1 IS USED`.** Every consumption site at
`file:line`, or the sentence that there are none.

**REQUIRED REPORT SECTION `## THE BILL AFTER THIS TASK`.** How many rows
`GCHStatement` still wants, named. **Count, do not estimate.**

ESTIMATE: about 130 lines in the probe, of which the obligation is about 25.
BASIS: `[LJ-1.558]` made the same move one level up at a comparable size.
Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is whether `gch-from-five` consumes row 1 at all.

    -- gch-from-five's body, with AmbientCardAtSucc bound but UNUSED,
    -- typechecked with an unused-variable check on

**Write it FIRST and typecheck it ALONE.** If the elaborator accepts it unused,
the answer is in hand and the rest is bookkeeping. ESTIMATE: about 15 lines,
under 60 seconds.

## WHAT GO AND NO-GO EACH EARN

**A GO REMOVES THE ONLY ROW THAT ASKS FOR SOMETHING OUTSIDE L**, and takes the
bill from five rows to four.

**A NO-GO SAYS `L ⊨ GCH` AS ROUTED HERE NEEDS δ TO BE A REAL CARDINAL.** That is
a ruling the owner must hear, because it would mean the route proves more than
the trophy and has to be replaced.

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
  changed_files_none = ["agents/tasks/LJ-1-569/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-569/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-569/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-569/Probe569.agda"]
  changed_files_none = ["agents/tasks/LJ-1-569/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-569/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 214.740)
- CANDIDATE archive/dev/JOURNAL.md  (score 194.709)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 192.285)
- CANDIDATE archive/dev/DD-archived.md  (score 159.805)
- CANDIDATE dev/ARCHIVE.md  (score 150.948)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 56.560)
- CANDIDATE dev/literature/devlin-II5.md  (score 55.056)
- CANDIDATE dev/literature/geology.md  (score 46.688)
- CANDIDATE dev/literature/terms-2026-08.md  (score 43.069)
- CANDIDATE dev/literature/digest.md  (score 35.616)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
