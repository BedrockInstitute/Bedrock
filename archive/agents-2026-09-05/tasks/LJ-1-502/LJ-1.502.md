# LJ-1.502: does the consumer's formula survive t0 := N0

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-502/Probe502.agda`:

    twelveB-at-identified : (the twelve rows of SatGraphB.twelveB, elaborated
                            with t0 := N0 and t1 := N1, with the downstream
                            row lemmas still applying)

**and say whether the identification costs the consumer anything.** Land nothing
in `src/`.

**`[LJ-1.501]` IS GO AND IT ASKED FOR THIS TASK BY NAME.** It paid four `TFacts`
fields at `KValue`'s frame, and its section 4 records why the win may be borrowed
(`agents/tasks/LJ-1-501/lj-1.501-report.md:133-172`):

> `t0eq` IS FREE AT `KValue`'S FRAME ONLY BECAUSE THE FRAME POINTS `t0` AT THE
> SAME SLOT AS `N0`.

**`Kenv` HAS FOURTEEN SLOTS AND NONE IS SPARE** (`src/L/Condensation.lagda.md:7389`).
Two hold the carrier and the bound; the other twelve hold `numeralL 0` to
`numeralL 11`, one each. So a frame that needs `t0` to hold `numeralL 0` has
exactly one choice, `t0 := i0`, and `[LJ-1.495]` already instantiated `N0 := i0`
there (`agents/tasks/LJ-1-495/Probe495.agda:169`). **The identification is forced
by the list, not chosen.**

**AND `t0` AND `t1` ARE NOT ONLY FACT INDICES.** They are variable indices INSIDE
`SatGraphB.twelveB` (`src/L/Condensation.lagda.md:2239-2240`), in four of the
twelve rows: `memBndAt` (`:2241`), `eqBndAt` (`:2244`), `allInBndAt` (`:2255`) and
`exInBndAt` (`:2258`). **Setting `t0 := N0` makes one variable index serve two
syntactic roles.** `[LJ-1.501]` did not measure whether the consumer survives it,
and says so plainly.

**THIS QUESTION IS PRIOR TO WORK ALREADY RUNNING.** `[LJ-1.499]` and `[LJ-1.500]`
are building `TFacts` fields at this same fourteen-slot frame. If the answer is
NO, their frame is wrong and the mathematician re-reads both.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-502/Probe502.agda::twelveB-at-identified"]

## SCOPE (write)
- agents/tasks/LJ-1-502/Probe502.agda
- agents/tasks/LJ-1-502/lj-1.502-report.md
- agents/tasks/LJ-1-502/review-of-twelveB-at-identified.md
- agents/tasks/LJ-1-502/runs/

## PREMISES

1. `[LJ-1.501]` is GO and paid four fields at this frame. Basis: agents/tasks/LJ-1-501/lj-1.501-report.md:5
2. Its section 4 names this question and recommends it. Basis: agents/tasks/LJ-1-501/lj-1.501-report.md:133
3. `Kenv` has fourteen slots. Basis: src/L/Condensation.lagda.md:7389
4. `[LJ-1.495]` instantiated `N0 := i0` at this frame. Basis: agents/tasks/LJ-1-495/Probe495.agda:169
5. `twelveB` is the consumer's formula. Basis: src/L/Condensation.lagda.md:2239
6. `memBndAt` is one of the four rows that name `t0` or `t1`. Basis: src/L/Condensation.lagda.md:2241
7. `eqBndAt` is the second. Basis: src/L/Condensation.lagda.md:2244
8. `allInBndAt` is the third. Basis: src/L/Condensation.lagda.md:2255
9. `exInBndAt` is the fourth. Basis: src/L/Condensation.lagda.md:2258
10. `twelveB` carries a Δ₀ certificate that must survive. Basis: src/L/Condensation.lagda.md:2262
11. `[LJ-1.113]` measured that `t0eq` is not derivable at a FREE `t0`, which this does not contradict. Basis: agents/tasks/LJ-1-113/lj-1.113-report.md:122
12. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
13. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
14. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THIRTY OF FIFTY-NINE `TFacts` FIELDS ARE NOW ACCOUNTED AT ONE FRAME**, twenty
six by `[LJ-1.495]` and four by `[LJ-1.501]`. **All thirty rest on the same
fourteen-slot `Kenv`**, and this task asks whether that frame is sound for the
record's consumer.

## WHAT IS MISSING

The elaboration, and the answer.

## THE REASONING

**D-10, BEFORE ANY AGDA.** Read the four rows and say at `file:line` what role
`t0` and `t1` play in each: a bound, a tag, a comparison operand, or something
else. **If a row uses `t0` in a position where `N0` already appears, name the
position.** That is where a collision would show, and naming it before you
elaborate is cheaper than reading an error.

**ELABORATE `twelveB` AT THE IDENTIFICATION AND THEN APPLY THE ROW LEMMAS.** A
formula that elaborates is not the deliverable: the deliverable is that the
downstream row lemmas STILL APPLY. **`Δ₀-twelveB` (`src/L/Condensation.lagda.md:2262`)
is the cheapest witness that the shape is unhurt; check it first.**

**DO NOT CHANGE `Kenv` AND DO NOT PROPOSE A SIXTEEN-SLOT FRAME.** If the answer
is NO, say so with the failing row and STOP. Sizing the cure is the
mathematician's and it would change three chapters.

**DO NOT BUILD A `TFacts` VALUE AND DO NOT TOUCH THE `envK-*` FAMILY OR THE CODE
READERS.** `[LJ-1.499]` and `[LJ-1.500]` hold those and are running.

**REQUIRED REPORT SECTION `## WHAT THE IDENTIFICATION COSTS`.** One row per
affected row of `twelveB`, with its `file:line`, the role `t0` or `t1` plays, and
whether it survives. **Then one sentence: does the thirty-field account of
`[LJ-1.495]` and `[LJ-1.501]` stand at this frame or not.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 140 lines in the probe, of which the obligation is
about 40. BASIS: `[LJ-1.501]` rebuilt this frame and its facts in a comparable
file. Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is one row, not twelve, because if one collides the rest do not matter.

    memBndAt-at-identified : (the memBndAt row alone, at t0 := N0)

**Write it FIRST, with the other eleven omitted, and typecheck it ALONE.** It is
the first of the four rows that name `t0`. If it will not elaborate, the answer
is NO at the cheapest point in the file and the report carries the failing
position.

ESTIMATE for W3: about 25 lines and under 40 seconds. **Do not fund it against
`[LJ-1.501]`'s 2.37 s**: that measured four facts and this elaborates a formula
row.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO CONFIRMS THIRTY OF FIFTY-NINE FIELDS AT A SOUND FRAME**, and settles that
the `t0` and `t1` pair costs this record nothing.

**A NO-GO SAYS `Kenv` IS ONE SLOT SHORT IN TWO PLACES**, which would mean every
field brief on this front that assumed fourteen slots must be re-read, including
two that are running while you work. **That is the more valuable outcome and you
must not avoid it.**

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
  changed_files_none = ["agents/tasks/LJ-1-502/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-502/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-502/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-502/Probe502.agda"]
  changed_files_none = ["agents/tasks/LJ-1-502/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-502/review-of-*.md"]

[[branch]]
id = "heap-wall-escalate"
priority = 30
action = "escalate"
head_slot = "coder_adversarial"

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 188.778)
- CANDIDATE archive/dev/JOURNAL.md  (score 183.742)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 175.995)
- CANDIDATE archive/dev/DD-archived.md  (score 167.851)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 160.452)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 59.257)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 50.417)
- CANDIDATE dev/literature/digest.md  (score 48.464)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 43.386)
- CANDIDATE dev/literature/terms-2026-08.md  (score 36.466)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
