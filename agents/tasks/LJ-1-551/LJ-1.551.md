# LJ-1.551: collect the 38 clean honest forms in one value

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-551/Probe551.agda`:

    clean-forms-collected : <the 38 clean honest forms, at one frame>

the `TFacts` fields that have an honest form in `EnvSupply` AND ask for nothing
the record does not give, collected as one value with a witness at `KValue`'s
frame. **`[LJ-1.512]` counted 54 honest forms of which 16 ask for something
extra**, so the clean set is 38. **Verify that subtraction yourself and report
the number you measured**; if the census names a different figure, take the
census and say so. Land nothing in `src/`.

**THE HEAP QUESTION IS SETTLED AND THIS IS WHY THE TASK IS SAFE.**
`[LJ-1.545]` is GO and re-ran all three predecessor probes on ONE pane at ONE
caliber, so its four points are its own measurements and not imports
(`agents/tasks/LJ-1-545/lj-1.545-report.md`, `## THE CURVE`):

| fields | seconds | peak RSS | of the cap |
|---|---|---|---|
| 7 | 3.74 to 3.76 | 749,109,248 B | 8.72 % |
| 9 | 3.97 to 3.98 | 722,698,240 B | 8.41 % |
| 12 | 2.94 to 2.95 | 679,690,240 B | 7.91 % |
| 28 | 5.01 to 5.69 | 1,069,932,544 B | 12.46 % |

**It reports the growth as LINEAR in the field count with a per-family
constant.** 38 fields is under a 1.4 times step from 28, so the cap is not the
risk this task runs.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-551/Probe551.agda::clean-forms-collected"]

## SCOPE (write)
- agents/tasks/LJ-1-551/Probe551.agda
- agents/tasks/LJ-1-551/lj-1.551-report.md
- agents/tasks/LJ-1-551/review-of-clean-forms.md
- agents/tasks/LJ-1-551/runs/

## PREMISES

1. `[LJ-1.512]`'s census covers all 59 `TFacts` fields. Basis: agents/tasks/LJ-1-512/lj-1.512-report.md:1
2. It counts 54 honest forms and 16 that ask for more. Basis: agents/tasks/LJ-1-512/lj-1.512-report.md:1
3. It calls the result a pattern and not three accidents. Basis: agents/tasks/LJ-1-512/lj-1.512-report.md:39
4. `[LJ-1.545]` is GO and measured four points itself. Basis: agents/tasks/LJ-1-545/lj-1.545-report.md:1
5. `TFacts` has 59 fields. Basis: src/L/Condensation/TwelveAgree.lagda.md:129
6. `KFacts` has 29 fields. Basis: src/L/Condensation.lagda.md:6079
7. `KValue` delivers a `KFacts` value at this frame. Basis: src/L/Condensation.lagda.md:7411
8. `[LJ-1.71]` found a telescope uninhabited at EVERY frame. Basis: archive/dev/LJ-dispatch-index.md:135
9. `[LJ-1.72]` found a green union frame whose APPLICATION heap-walls. Basis: archive/dev/LJ-dispatch-index.md:137
10. `[LJ-1.75]` measured a trimmed telescope 41.6 percent cheaper for 37.7 percent smaller. Basis: archive/dev/LJ-dispatch-index.md:142
11. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
12. Evidence is `file:line`. Basis: AGENTS.md:41
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

A census of all 59 fields and a four-point heap curve. **What is NOT delivered is
any value carrying more than 28 of them.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE LIST.** Read `[LJ-1.512]`'s census table
and write out the clean fields BY NAME at `file:line`. **Report how many there
are.** If your count differs from 38, say so and use yours.

**GUARD AGAINST VACUITY FIRST, BECAUSE THE ARCHIVE RECORDS EXACTLY THIS FAILURE.**
`[LJ-1.71]` shipped a module whose telescope was uninhabited at every frame
(`archive/dev/LJ-dispatch-index.md:135`), and the audit after it found that
parameter counts and instantiation counts do not ask whether a telescope is
satisfiable. **Inhabit before you collect. That is W3.**

**A GREEN COLLECTION DOES NOT PREDICT A GREEN APPLICATION, AND YOU MUST SAY SO.**
`[LJ-1.72]` measured a union frame that checked green while the APPLICATION
heap-walled at the 8 GB cap (`:137`). **Do not claim this value can be applied.
Claim only what you measured.**

**DO NOT TRIM THE TELESCOPE TO MAKE IT CHEAPER.** `[LJ-1.75]` shows trimming
wins, but the point of this task is the FULL clean set at one frame. A trimmed
value answers a different question.

**DO NOT COLLECT THE 16 THAT ASK FOR MORE. DO NOT BUILD A `TFacts` VALUE.**
AD12 gives this brief one obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE FIFTH POINT`.** Add your measurement to
`[LJ-1.545]`'s four rows, at the same caliber, and say in one sentence whether
the linear reading still holds. **Say it only about numbers you measured.**

**REQUIRED REPORT SECTION `## WHAT THE 16 WOULD COST`.** Three sentences. The 16
fields ask for something the record does not give. **Say whether they ask for
sixteen DIFFERENT things or a few repeated**, and name the most common one. Do
not build them. That grouping is what the mathematician needs to size the next
brief.

ESTIMATE: about 260 lines in the probe, of which the obligation is about 60, and
under 10 seconds of Agda. BASIS: `[LJ-1.545]` collected 28 fields at 5.01 to
5.69 seconds. Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is whether the clean set's hypotheses can hold together at one frame.

    -- the union of the clean fields' extra hypotheses, at KValue's frame, INHABITED

**Write it FIRST and typecheck it ALONE.** If it is uninhabited, the collection
is refuted before any field is written and that is a full result, and it is the
`[LJ-1.71]` failure caught early. ESTIMATE: about 20 lines, under 30 seconds.

## WHAT GO AND NO-GO EACH EARN

**A GO PUTS 38 OF THE 59 FIELDS IN ONE VALUE** and gives the curve a fifth
point, which prices every remaining collection brief.

**A NO-GO NAMES THE FIELD OR THE HYPOTHESIS THAT WILL NOT JOIN**, which is the
seam in the record and is worth more than the collection.

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
  changed_files_none = ["agents/tasks/LJ-1-551/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-551/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-551/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-551/Probe551.agda"]
  changed_files_none = ["agents/tasks/LJ-1-551/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-551/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 248.061)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 239.999)
- CANDIDATE archive/dev/JOURNAL.md  (score 209.792)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 170.668)
- CANDIDATE dev/ARCHIVE.md  (score 164.769)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 51.525)
- CANDIDATE dev/literature/digest.md  (score 45.716)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 39.722)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 37.765)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 32.926)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
