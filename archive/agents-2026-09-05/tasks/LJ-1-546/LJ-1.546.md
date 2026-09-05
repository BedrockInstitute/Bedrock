# LJ-1.546: what B10 wants BESIDE a code, and it is a pair mismatch

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

State ONE type in `agents/tasks/LJ-1-546/Probe546.agda` and inhabit it, or
refute it:

    succ-pair-transfer : <the fact that carries a code from the coding leg's
                          pair to B10's pair>

Then prove, in the same file, that it suffices:

    transfer-suffices : succ-pair-transfer → SuccIntoPower zf

**The name and the exact statement of `succ-pair-transfer` are YOURS to
choose**, and naming it well IS the deliverable. Land nothing in `src/`.

**WHY THIS ROW IS NOT SIMPLY BLOCKED.** `[LJ-1.540]` counted one code token in
B10 and called it "wants a code", and both routes to a GENERIC code are closed
(`[LJ-1.533]`, `[LJ-1.535]`). **But B10 does not want a generic code.** Unfold
it: `InjL a b = ∥ Σ[ F ∈ S ] InjCode F a b ∥₁` (`src/L/GCH.lagda.md:38`), so B10
wants `InjCode F δ (𝒫 κ)` for ONE specific pair. **And the coding leg has been
building `InjCode`'s four conjuncts all week.** The mismatch is the PAIR, not
the code: `src/L/CodedShift.lagda.md:40` builds at `sucʟ γ` and `γ`, and B10
wants `δ` and `𝒫 κ`. **That distance is what this task measures.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-546/Probe546.agda::transfer-suffices"]

## SCOPE (write)
- agents/tasks/LJ-1-546/Probe546.agda
- agents/tasks/LJ-1-546/lj-1.546-report.md
- agents/tasks/LJ-1-546/review-of-transfer-suffices.md
- agents/tasks/LJ-1-546/runs/

## PREMISES

1. B10's type is stated in `[LJ-1.523]`'s probe. Basis: agents/tasks/LJ-1-523/Probe523.agda:266
2. `InjL` unfolds to a truncated code with `InjCode`. Basis: src/L/GCH.lagda.md:38
3. `InjCode` has four conjuncts. Basis: src/L/Cardinal.lagda.md:223
4. `SuccCardL` has four components, the last a leastness clause. Basis: src/L/GCH.lagda.md:47
5. `CodedShift` builds a code at the successor-stage pair. Basis: src/L/CodedShift.lagda.md:40
6. `[LJ-1.533]` closed the generic coded route by a type argument. Basis: agents/tasks/LJ-1-533/lj-1.533-report.md:1
7. `[LJ-1.535]` closed the counting-site route. Basis: agents/tasks/LJ-1-535/lj-1.535-report.md:1
8. `[LJ-1.526]` reduced B4 to `CardAboveL`, the same shape of move. Basis: agents/tasks/LJ-1-526/lj-1.526-report.md:1
9. `[LJ-1.528]` then built `CardAboveL` and paid B4. Basis: agents/tasks/LJ-1-528/Probe528.agda:638
10. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
11. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
12. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

**THE PRECEDENT IS B4 AND IT WORKED TWICE.** `[LJ-1.526]` did not build B4: it
NAMED the fact B4 reduces to, and `[LJ-1.528]` then built that fact in a
`--safe` module with no choice. **This task is the `[LJ-1.526]` half for B10.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE DISTANCE.** Say at `file:line` what pair
`CodedShift` delivers a code at, and what pair B10 wants. **Then say in one
sentence what the difference is**: an ordinal against a power set, a successor
against a cardinal successor, or both.

**DO NOT BUILD THE TRANSFER FACT.** `[LJ-1.526]`'s value was that it stopped at
the naming. Your obligation is `transfer-suffices`, the IMPLICATION. If the
transfer fact turns out to be one line, say so and build it, but **do not spend
the estimate trying.**

**NAME IT SO A LATER TASK CAN BUILD IT.** The statement must be self-contained
at its own frame, must not mention `SuccIntoPower`, and must be something a
coder could take as a single obligation. **That is the test of a good name.**

**IF THE TRANSFER IS FALSE, SAY SO AND STOP.** A refutation here is worth as
much as an implication: it says B10 needs a code built from scratch and the
join waits on a formula. `[LJ-1.507]` refuted a statement three dispatches had
built toward, and that was the most valuable result of its week.

**THE LEASTNESS CLAUSE IS THE SUSPECT.** `SuccCardL`'s fourth component
(`src/L/GCH.lagda.md:51-52`) quantifies over every ordinal L-cardinal above κ.
**Say whether your transfer fact needs it. If it does, say so loudly**: a
universally quantified hypothesis over cardinals is where this bridge has
failed before.

**DO NOT BUILD B5, B8 OR B9.** AD12 gives this brief one obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE NAMED FACT`.** State `succ-pair-transfer` in
full, say whether you inhabited it, refuted it or left it open, and say in one
sentence what a task that builds it would cost.

**REQUIRED REPORT SECTION `## WHAT B9 WANTS`.** B9 is the other coded row.
**Say in three sentences whether the same pair-transfer move reaches it**, and
whether the two rows share a fact. Do not build it.

ESTIMATE: about 130 lines in the probe, of which the obligation is about 25.
BASIS: `[LJ-1.526]` did the same shape of move for B4. Comparables are of SHAPE
and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is `𝒫 κ` as `InjCode`'s second argument, because `InjCode` was written for a
stage and nobody has fed it a power set.

    -- InjCode F δ (𝒫 κ), stated at B10's frame, TYPE ONLY, no inhabitant

**Write it FIRST and typecheck it ALONE.** If the type does not even form, the
row is refuted before any reduction and that is a full result. ESTIMATE: about
12 lines, under 30 seconds.

## WHAT GO AND NO-GO EACH EARN

**A GO NAMES THE ONE FACT THAT UNBLOCKS B10**, and the B4 precedent says the
next task can then build it. That would take the join to two unpaid inputs.

**A NO-GO SAYS THE JOIN WAITS ON A FORMULA WRITTEN FROM SCRATCH**, which is a
ruling the mathematician must make and cannot make without this measurement.

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
  changed_files_none = ["agents/tasks/LJ-1-546/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-546/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-546/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-546/Probe546.agda"]
  changed_files_none = ["agents/tasks/LJ-1-546/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-546/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 162.378)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 150.360)
- CANDIDATE archive/dev/JOURNAL.md  (score 141.635)
- CANDIDATE archive/dev/DD-archived.md  (score 125.307)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 122.780)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 41.490)
- CANDIDATE dev/literature/devlin-II5.md  (score 38.819)
- CANDIDATE dev/literature/digest.md  (score 35.936)
- CANDIDATE dev/literature/terms-2026-08.md  (score 32.278)
- CANDIDATE dev/literature/geology.md  (score 28.815)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
