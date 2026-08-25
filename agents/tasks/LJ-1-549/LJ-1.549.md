# LJ-1.549: SuccIntoSubsets, and the formula it turns on

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-549/Probe549.agda`:

    succ-into-subsets :
        (κ δ : SL.S) → SuccCardL δ κ
      → ∥ Σ[ b ∈ SL.S ] Σ[ F ∈ SL.S ]
           ( InjCode F δ b
           × ((y : SL.S) → ⟨ fst y ∈ fst b ⟩ → ⟨ y ⊆ˢ κ ⟩) ) ∥₁

which is `SuccIntoSubsets`, the fact `[LJ-1.546]` named and left open
(`agents/tasks/LJ-1-546/Probe546.agda:152-157`). Land nothing in `src/`.

**`[LJ-1.546]` IS GO AND IT ALREADY PROVED THIS SUFFICES.** Its
`transfer-suffices` derives B10 `SuccIntoPower` from this statement, so this
task pays B10 outright if it lands. **Do not rebuild `transfer-suffices`.**

**WHAT MAKES THIS STATEMENT REACHABLE WHERE B10 WAS NOT.** It does not ask for
`𝒫 κ` itself. It asks for SOME L-set `b` whose members are all subsets of κ,
with a code from δ into it. **The freedom in `b` is the whole point of the
reduction**, and it is yours to use.

**THE WALL, NAMED BY ITS PREDECESSOR.** `[LJ-1.546]` measured that B10's only
remaining obstruction is "a `Formula` that carves a table with the required
domain" (`agents/tasks/LJ-1-546/lj-1.546-report.md`, `## WHAT B9 WANTS`).
`[LJ-1.537]` built `approx-carve` (`agents/tasks/LJ-1-537/lj-1.537-report.md:16`),
which carves a table from an ordinal and a member and pins its type in a
separate module. **Whether that method reaches THIS table is the task.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-549/Probe549.agda::succ-into-subsets"]

## SCOPE (write)
- agents/tasks/LJ-1-549/Probe549.agda
- agents/tasks/LJ-1-549/lj-1.549-report.md
- agents/tasks/LJ-1-549/review-of-succ-into-subsets.md
- agents/tasks/LJ-1-549/runs/

## PREMISES

1. `SuccIntoSubsets` is stated in full by `[LJ-1.546]`. Basis: agents/tasks/LJ-1-546/Probe546.agda:152
2. `[LJ-1.546]` proved it suffices for B10. Basis: agents/tasks/LJ-1-546/lj-1.546-report.md:1
3. It left the statement open, neither inhabited nor refuted. Basis: agents/tasks/LJ-1-546/lj-1.546-report.md:1
4. B10's type is stated in `[LJ-1.523]`'s probe. Basis: agents/tasks/LJ-1-523/Probe523.agda:266
5. `InjCode` has four conjuncts. Basis: src/L/Cardinal.lagda.md:223
6. `SuccCardL`'s fourth component is a leastness clause over cardinals. Basis: src/L/GCH.lagda.md:47
7. `[LJ-1.537]` built `approx-carve` and pinned its type. Basis: agents/tasks/LJ-1-537/lj-1.537-report.md:16
8. `[LJ-1.533]` measured a wall for coding an ambient injection. Basis: agents/tasks/LJ-1-533/lj-1.533-report.md:1
9. `[LJ-1.535]` closed the counting-site route. Basis: agents/tasks/LJ-1-535/lj-1.535-report.md:1
10. `[LJ-1.507]` refuted a statement three dispatches had built toward. Basis: agents/tasks/LJ-1-507/review-of-someEnv-at-frame.md:38
11. A stop is a deliverable. Basis: AGENTS.md:43
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

**THE IMPLICATION IS PAID AND THE ANTECEDENT IS NOT.** `[LJ-1.546]` did the
`[LJ-1.526]` half. This is the `[LJ-1.528]` half, and on B4 that pattern worked.

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE CHOICE OF `b`.** Say at `file:line` what
set you will take for `b` and why every member of it is a subset of κ. **Say it
before you write any formula.** The obvious candidates are a stage, a bounded
collection and `𝒫 κ` itself; each has a different cost and one of them may be
free.

**W3 IS THE FORMULA AND IT IS THE WHOLE TASK.** Get it wrong and the estimate is
meaningless.

**IF `approx-carve` DOES NOT REACH THIS TABLE, SAY SO PRECISELY AND STOP.** Name
which of its inputs you cannot supply. `[LJ-1.507]` refuted a target three
dispatches had built toward, and that refutation was the most valuable result of
its week. **A named stop here is worth more than a partial build.**

**THE LEASTNESS CLAUSE IS THE SUSPECT.** `SuccCardL`'s fourth component
(`src/L/GCH.lagda.md:51-52`) quantifies over every ordinal L-cardinal above κ.
**Say whether you used it. If you did, say at which step**: this bridge has
failed at a universally quantified cardinal hypothesis before.

**DO NOT REBUILD `transfer-suffices`. DO NOT TOUCH B5 OR B9.** AD12 gives this
brief one obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE SET b`.** Name it, say why its members are
subsets of κ, and say what it cost.

**REQUIRED REPORT SECTION `## THE FORMULA`.** Write the formula out, say whether
`approx-carve` supplied it or you wrote it fresh, and give its line count
MEASURED.

ESTIMATE: about 220 lines in the probe, of which the obligation is about 45.
BASIS: `[LJ-1.537]` built a carve of comparable shape. **This is the least
certain estimate I have written this week, because the formula is unmeasured
and `[LJ-1.520]`'s graded formula needed a nine-row cost table.** Comparables
are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the formula that carves the table from δ into `b`.

    -- the Formula, stated alone, with its arity and its free variables, TYPE ONLY

**Write it FIRST and typecheck it ALONE.** If you cannot state it, say so and
stop: that is the measurement the mathematician wants and it costs one hour
instead of four. ESTIMATE: about 25 lines, under 2 minutes.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS B10 OUTRIGHT**, because `[LJ-1.546]` already proved the implication.
The join would then want only B5 and B9.

**A NO-GO THAT NAMES THE MISSING INPUT OF `approx-carve` TELLS THE MATHEMATICIAN
THE JOIN NEEDS A FORMULA WRITTEN FROM SCRATCH**, and how big. That is the
ruling this leg has been waiting three days for.

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
  changed_files_none = ["agents/tasks/LJ-1-549/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-549/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-549/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-549/Probe549.agda"]
  changed_files_none = ["agents/tasks/LJ-1-549/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-549/review-of-*.md"]

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
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 140.457)
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 136.003)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 120.343)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 115.480)
- CANDIDATE dev/ARCHIVE.md  (score 113.978)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 61.799)
- CANDIDATE dev/literature/digest.md  (score 43.532)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 42.398)
- CANDIDATE dev/literature/terms-2026-08.md  (score 32.785)
- CANDIDATE dev/literature/geology.md  (score 31.189)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
