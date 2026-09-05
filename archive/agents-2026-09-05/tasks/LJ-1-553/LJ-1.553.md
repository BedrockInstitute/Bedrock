# LJ-1.553: one membership, thirteen fields

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-553/Probe553.agda`:

    graph-in-K-discharges :
      <the thirteen TFacts fields that ask for a membership in K,
       collected at KValue's frame under ONE supplied membership>

**One hypothesis in, thirteen fields out.** Land nothing in `src/`.

**`[LJ-1.551]` IS GO AND IT FOUND THE PATTERN BY READING ALL SIXTEEN FIRST
HAND.** Of the 16 fields that ask for something the record does not give,
**13 ask for the same kind of thing, a membership in `K`**, and nine of those
state one slot character for character
(`agents/tasks/LJ-1-551/lj-1.551-report.md`, `## WHAT THE 16 WOULD COST`):

| shape | fields | sites |
|---|---|---|
| `⟨ fst (lookup (suc zero) γ') ∈ fst K ⟩` | 7 | `src/L/Coding/EnvSupply.lagda.md:497`, `:508`, `:519`, `:530`, `:541`, `:552`, `:563` |
| `(C T : S) → ⟨ fst T ∈ fst K ⟩`, same slot, fresh binder | 2 | `:462`, `:471` |
| a membership in `K` at another binder | 4 | `:594-595`, `:604-605`, and the `wKfact` sites |

**SEVEN OF THEM ARE THE SAME SENTENCE.** That is why this is one task and not
thirteen.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-553/Probe553.agda::graph-in-K-discharges"]

## SCOPE (write)
- agents/tasks/LJ-1-553/Probe553.agda
- agents/tasks/LJ-1-553/lj-1.553-report.md
- agents/tasks/LJ-1-553/review-of-graph-in-K.md
- agents/tasks/LJ-1-553/runs/

## PREMISES

1. `[LJ-1.551]` is GO and read all sixteen at first hand. Basis: agents/tasks/LJ-1-551/lj-1.551-report.md:1
2. It groups 13 of the 16 as memberships in `K`. Basis: agents/tasks/LJ-1-551/lj-1.551-report.md:1
3. Seven state one slot character for character. Basis: src/L/Coding/EnvSupply.lagda.md:497
4. Two name the same slot with a fresh binder. Basis: src/L/Coding/EnvSupply.lagda.md:462
5. `[LJ-1.512]` counted 54 honest forms of which 16 ask for more. Basis: agents/tasks/LJ-1-512/lj-1.512-report.md:1
6. `[LJ-1.545]` measured the heap linear in field count. Basis: agents/tasks/LJ-1-545/lj-1.545-report.md:1
7. `TFacts` has 59 fields. Basis: src/L/Condensation/TwelveAgree.lagda.md:129
8. `KValue` delivers a `KFacts` value at this frame. Basis: src/L/Condensation.lagda.md:7411
9. `[LJ-1.71]` shipped a module whose telescope was uninhabited at every frame. Basis: archive/dev/LJ-dispatch-index.md:135
10. `[LJ-1.75]` measured a trimmed telescope better than proportional. Basis: archive/dev/LJ-dispatch-index.md:142
11. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
12. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

`[LJ-1.551]` collected the 38 clean forms in one value. **The 16 are collected
nowhere, and nobody has tried to supply their common hypothesis once.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS WHETHER ONE MEMBERSHIP COVERS THEM.** Read
the thirteen at `src/L/Coding/EnvSupply.lagda.md` yourself. **Say at `file:line`
whether one supplied membership discharges all thirteen, or whether the binders
differ enough that it discharges only the seven.** Report the number you can
actually cover and build THAT, and say so in the title of your report.

**GUARD AGAINST VACUITY FIRST, BECAUSE THE ARCHIVE RECORDS THIS EXACT FAILURE.**
`[LJ-1.71]` shipped a module whose telescope was uninhabited at every frame
(`archive/dev/LJ-dispatch-index.md:135`). **Inhabit the supplied membership at
`KValue`'s frame BEFORE you discharge anything with it. That is W3.**

**DO NOT WEAKEN A FIELD TO MAKE IT FIT.** If a field needs a different
membership, it is not one of the thirteen: say which and leave it.

**DO NOT COLLECT THE 38 AGAIN.** `[LJ-1.551]` has them. AD12 gives this brief one
obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## HOW MANY THE ONE MEMBERSHIP BOUGHT`.** The count
you measured, the fields by name, and the ones it did not reach.

**REQUIRED REPORT SECTION `## THE REMAINING THREE`.** `[LJ-1.551]` says three of
the sixteen are NOT memberships in `K`. **Name them and say in one sentence each
what they ask for.** Do not build them.

ESTIMATE: about 180 lines in the probe, of which the obligation is about 45, and
under 10 seconds of Agda. BASIS: `[LJ-1.545]` collected 28 fields at 5.01 to
5.69 seconds and `[LJ-1.551]` collected 38. Comparables are of SHAPE and nothing
may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the membership itself, at the frame, inhabited.

    -- ⟨ fst (lookup (suc zero) γ') ∈ fst K ⟩ at KValue's frame, INHABITED

**Write it FIRST and typecheck it ALONE.** If it is not inhabitable there, the
whole task is refuted before a field is touched, and that is a full result.
ESTIMATE: about 20 lines, under 30 seconds.

## WHAT GO AND NO-GO EACH EARN

**A GO TAKES THE COVERED COUNT FROM 38 TO 51 OF 59** and shows the 16 are three
problems rather than sixteen, which prices the whole remaining front.

**A NO-GO NAMES THE FRAME AT WHICH THE COMMON MEMBERSHIP FAILS**, which is the
seam in `EnvSupply` and is worth more than the collection.

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
  changed_files_none = ["agents/tasks/LJ-1-553/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-553/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-553/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-553/Probe553.agda"]
  changed_files_none = ["agents/tasks/LJ-1-553/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-553/review-of-*.md"]

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
- CANDIDATE archive/dev/JOURNAL.md  (score 137.266)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 137.199)
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 134.353)
- CANDIDATE dev/ARCHIVE.md  (score 128.244)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 108.099)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 43.249)
- CANDIDATE dev/literature/devlin-II5.md  (score 40.144)
- CANDIDATE dev/literature/terms-2026-08.md  (score 39.944)
- CANDIDATE dev/literature/digest.md  (score 33.117)
- CANDIDATE dev/literature/geology.md  (score 27.209)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
