# LJ-1.538: the honest-form frame, one family at a time

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-538/Probe538.agda`:

    envK-frame-inhabited :
        (the extra hypotheses that `SupplyEnv`'s NINE env forms take, collected
         as one telescope)
      → (a witness of that telescope at KValue's frame)

**the `envK-*` and `envInK-*` family ONLY, not all sixteen.** Land nothing in
`src/`.

**`[LJ-1.534]` TRIED ALL SIXTEEN AT ONCE AND THE ELABORATOR RAN OUT OF
MEMORY.** It parked at `attempt_max` after matching a heap wall four times,
exit 251 each (`dev/pod/transitions/2026-08.jsonl`, 10:34Z to 11:13Z). **Its
worktree holds no report and no probe: the wall fired before anything was
written.**

**THAT IS A MEASUREMENT AND NOT ONLY A PROGRAM FAULT.** Sixteen hypotheses
collected at one frame do not elaborate. **So the frame is assembled one family
at a time, and this brief takes the family that is already delivered whole.**

**THE FAMILY.** `[LJ-1.499]` is GO and found that
`src/L/Coding/EnvSupply.lagda.md:293-411` holds all nine `envK-*` and
`envInK-*` forms, and that they reach `TFacts`'s frame with one `refl` each
(`agents/tasks/LJ-1-499/lj-1.499-report.md:277-280`). **Nine forms, one
chapter, one delivered reduction. If any family collects cleanly, it is this
one.**

**AND NON-VACUITY IS STILL THE POINT.** `[LJ-1.507]` proved that three
dispatches of this campaign built toward a statement NOTHING SATISFIED. **The
witness is the deliverable; the telescope alone is not.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-538/Probe538.agda::envK-frame-inhabited"]

## SCOPE (write)
- agents/tasks/LJ-1-538/Probe538.agda
- agents/tasks/LJ-1-538/lj-1.538-report.md
- agents/tasks/LJ-1-538/review-of-envK-frame.md
- agents/tasks/LJ-1-538/runs/

## PREMISES

1. `[LJ-1.499]` is GO and found the nine forms delivered. Basis: agents/tasks/LJ-1-499/lj-1.499-report.md:20
2. They reach the record's frame with one `refl` each. Basis: agents/tasks/LJ-1-499/lj-1.499-report.md:277
3. `envK-gen` is the generic supplier. Basis: src/L/Coding/EnvSupply.lagda.md:277
4. The nine forms live in one block. Basis: src/L/Coding/EnvSupply.lagda.md:293
5. `SupplyEnv` is their home and it is pinned to `lam`. Basis: src/L/Coding/EnvSupply.lagda.md:107
6. `KValue` binds the carrier and the stage. Basis: src/L/Condensation.lagda.md:7380
7. `KValue.facts` is delivered there. Basis: src/L/Condensation.lagda.md:7411
8. `[LJ-1.495]` shifts it to the record's indices. Basis: agents/tasks/LJ-1-495/Probe495.agda:166
9. `[LJ-1.503]` settled the gate `SupplyEnv` states. Basis: src/L/Coding/EnvSupply.lagda.md:111
10. `[LJ-1.507]` proved a chain rested on an empty antecedent. Basis: agents/tasks/LJ-1-507/Probe507.agda:257
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**FIFTY SEVEN OF FIFTY NINE `TFacts` FIELDS HAVE A DELIVERED HONEST FORM
SOMEWHERE.** `[LJ-1.512]` measured that before its own routing loop stranded it.
**What is unmeasured is whether the hypotheses those forms want can hold
together, and the first attempt at all sixteen did not fit in memory.**

## THE REASONING

**D-10, BEFORE ANY AGDA.** Read `SupplyEnv`'s telescope from
`src/L/Coding/EnvSupply.lagda.md:107` and list, at `file:line`, every
hypothesis the NINE env forms actually use. **Some of the telescope may not be
used by this family; say which.** A collected frame that carries unused
hypotheses is larger than it needs to be, and size is exactly what killed
`[LJ-1.534]`.

**COLLECT ONLY WHAT THE NINE USE.** Not the whole telescope, not the other
seven forms.

**BUILD THE WITNESS. A TELESCOPE ALONE IS NOT THE DELIVERABLE.**

**WATCH THE HEAP AND SAY WHAT YOU SEE.** `[LJ-1.534]` hit the wall at
sixteen. **If nine also walls, say so at once**: that would mean the frame
cannot be collected at any useful size and the record must be read
field-by-field, which is a design finding and the best outcome available.

**DO NOT COLLECT THE OTHER SEVEN FORMS.** AD12 gives this brief one obligation
and `[LJ-1.534]` measured what happens when the scope is the whole set.

**DO NOT EDIT `src/` AND DO NOT REPLACE `TFacts`.** Whether the record is
replaced is the mathematician's.

**DO NOT POSTULATE.**

**REQUIRED REPORT SECTION `## THE NINE, AND WHAT THEY COST`.** The collected
telescope as a type, every hypothesis at its `file:line`, and for each:
supplied by `KValue`, supplied by `[LJ-1.495]`'s shift, or NEW. **Plus the peak
RSS, because the next family is priced against it.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 160 lines in the probe, of which the obligation is
about 50. BASIS: `[LJ-1.499]` reached these same nine forms at this frame in a
comparable file. Comparables are of SHAPE and nothing may be funded against
them, and `[LJ-1.534]`'s attempt at sixteen produced no line count at all.

## W3, THE WIDEST UNMEASURED TERM

It is the heap, because the previous attempt died there and no smaller
collection has been tried.

    -- the nine hypotheses as one telescope, stated and typechecked, no witness

**Write it FIRST, and typecheck it ALONE, and report the peak RSS.** If nine
hypotheses do not elaborate at this frame, stop and say so: the number that
does fit is what the mathematician needs.

ESTIMATE for W3: about 30 lines and under 60 seconds. **Do not fund it against
`[LJ-1.534]`**, which produced no measurement, only a wall.

## WHAT GO AND NO-GO EACH EARN

**A GO GIVES THE FIRST COLLECTED FAMILY AND A HEAP FIGURE**, and the remaining
forms can be priced against a real number instead of a guess.

**A NO-GO AT NINE SAYS THE FRAME CANNOT BE COLLECTED AT ANY USEFUL SIZE**,
which would mean the record must be read field-by-field and would settle the
replacement question against the redesign.

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
  changed_files_none = ["agents/tasks/LJ-1-538/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-538/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-538/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-538/Probe538.agda"]
  changed_files_none = ["agents/tasks/LJ-1-538/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-538/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 219.252)
- CANDIDATE archive/dev/JOURNAL.md  (score 197.167)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 191.008)
- CANDIDATE dev/ARCHIVE.md  (score 172.725)
- CANDIDATE archive/dev/PLAN-archived.md  (score 168.256)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/digest.md  (score 49.717)
- CANDIDATE dev/literature/devlin-II5.md  (score 49.170)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 47.523)
- CANDIDATE dev/literature/geology.md  (score 36.903)
- CANDIDATE dev/literature/terms-2026-08.md  (score 34.589)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
