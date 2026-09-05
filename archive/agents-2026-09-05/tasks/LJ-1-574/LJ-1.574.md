# LJ-1.574: the assignment and its formula, in one task this time

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-574/Probe574.agda`:

    succ-assignment-definable :
        (δ κ : S) → SuccCardL δ κ
      → ∥ Σ[ g ∈ (⟪ fst δ ⟫ → ⟪ fst (powL κ) ⟫) ]
             ( <g injective> × <`[LJ-1.568]`'s `Def` at this g> ) ∥₁

**the assignment AND its defining formula together**, never separately. Land
nothing in `src/`.

**I SPLIT THIS WORK ONCE AND A PREDECESSOR PROVED THE SPLIT WRONG.** I queued
`[LJ-1.552]` for the assignment and `[LJ-1.554]` for its formula as independent
tasks. Both were NO-GO, and `[LJ-1.552]` said why in its own words: **"They are
not independent... a set enters L only through a generator, and both generators
take a `Formula`. A brief that funds the assignment as pure mathematics and the
link as pure coding has mis-split the work"**
(`agents/tasks/LJ-1-552/review-of-succ-assignment.md:161`). **This brief is that
correction and I say so plainly.**

**AND `[LJ-1.568]` NOW MAKES THE JOINT TARGET EXACT.** It proved `Def` both
sufficient AND necessary for `W` (`agents/tasks/LJ-1-568/Probe568.agda:252`,
`:368`), so `Def` at this `g` is not a convenient extra: **it is precisely what
row 5 wants and there is nothing weaker to look for.**

**WHAT IS ALREADY BUILT UNDER THIS.** `[LJ-1.557]` is GO and built the pointwise
internal code from ONE member of δ into κ
(`agents/tasks/LJ-1-557/lj-1.557-report.md`). It measured that the pointwise
form does not reach the uniform one and named the gap as exactly this formula.
**So the pointwise half is delivered and the uniform half is this task.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-574/Probe574.agda::succ-assignment-definable"]

## SCOPE (write)
- agents/tasks/LJ-1-574/Probe574.agda
- agents/tasks/LJ-1-574/lj-1.574-report.md
- agents/tasks/LJ-1-574/review-of-succ-assignment-definable.md
- agents/tasks/LJ-1-574/runs/

## PREMISES

1. `[LJ-1.552]` is a NO-GO and refutes the split. Basis: agents/tasks/LJ-1-552/review-of-succ-assignment.md:161
2. `[LJ-1.554]` is a NO-GO on the formula half. Basis: agents/tasks/LJ-1-554/review-of-no-generic-link.md:1
3. `[LJ-1.568]` proves `Def` sufficient. Basis: agents/tasks/LJ-1-568/Probe568.agda:252
4. `[LJ-1.568]` proves `Def` necessary. Basis: agents/tasks/LJ-1-568/Probe568.agda:368
5. `Def` is stated at its probe. Basis: agents/tasks/LJ-1-568/Probe568.agda:189
6. `[LJ-1.557]` is GO and built the pointwise code. Basis: agents/tasks/LJ-1-557/lj-1.557-report.md:1
7. `powL κ ≡ 𝒫 κ`, so no smaller target exists. Basis: agents/tasks/LJ-1-549/Probe549.agda:133
8. `[LJ-1.549]`'s `Residue` pays B10 outright. Basis: agents/tasks/LJ-1-549/Probe549.agda:685
9. `hasSeparationL` takes an arbitrary formula. Basis: src/L/Axioms/Full.lagda.md:144
10. `hasReplacementL` takes a `Formula S 2`. Basis: src/L/Axioms/Full.lagda.md:277
11. `[LJ-1.564]`'s bill has B10 as row 5. Basis: agents/tasks/LJ-1-564/Probe564.agda:456
12. A stop is a deliverable. Basis: AGENTS.md:43
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

A pointwise internal code, an exact statement of what the uniform form needs,
and two NO-GOs that show the halves cannot be funded separately.

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE FORMULA FIRST.** `[LJ-1.552]` measured
that the set enters L only through a generator and both generators take a
formula. **So write the formula before the function**, and say at `file:line`
what it says. If you cannot state it, stop there: that is the measurement.

**`[LJ-1.557]` SELECTED WITH `leastOf` AND MEASURED THAT ITS SELECTION IS "A
QUANTIFIER OVER THE WHOLE L-CARRIER AND NOT OVER A STAGE."** `[LJ-1.560]` is GO
and its reflection step was an INSTANTIATION of something already in the tree
(`agents/tasks/LJ-1-560/Probe560.agda:165-176`). **Ask whether that term bounds
this search. Nobody has tried it here, and it is the most likely opening.**

**DO NOT SPLIT THE WORK AGAIN.** If you deliver only the function or only the
formula, the task has repeated the mis-split. **Deliver both or stop.**

**DO NOT LOOK FOR A SMALLER TARGET.** `[LJ-1.549]` proved `powL κ ≡ 𝒫 κ`, so
there is no cheaper `b`.

**DO NOT ATTEMPT ROWS 1, 2, 3 OR 4.** AD12 gives this brief one obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE FORMULA, WRITTEN OUT`.** The formula, its
arity, and whether `[LJ-1.560]`'s reflection step supplied its bound.

**REQUIRED REPORT SECTION `## WHAT THIS DOES TO THE BILL`.** Which rows you
paid, which you did not. **Do not read a discharge into anything you did not
inhabit.**

ESTIMATE: about 240 lines in the probe, of which the obligation is about 60.
**This is the least certain estimate in the queue and it is the classical
content of the theorem.** Two predecessors stopped on its halves. Comparables
are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is whether `[LJ-1.560]`'s reflection step applies to `leastOf`'s search.

    -- [LJ-1.560]'s obligation, re-ascribed at leastOf's predicate, TYPE ONLY

**Write it FIRST and typecheck it ALONE.** If it does not apply, the formula has
no bound and the estimate above is void: say so in the first hour.
ESTIMATE: about 20 lines, under 3 minutes.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS ROW 5**, which is B10, which is the conjunct `GCHStatement` has
wanted since the campaign began.

**A NO-GO THAT SAYS THE REFLECTION STEP DOES NOT BOUND THIS SEARCH NAMES THE
LAST OPEN QUESTION ON THIS ROW**, and the mathematician will take it to the
owner rather than fund a sixth attempt.

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
  changed_files_none = ["agents/tasks/LJ-1-574/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-574/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-574/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-574/Probe574.agda"]
  changed_files_none = ["agents/tasks/LJ-1-574/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-574/review-of-*.md"]

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
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 154.642)
- CANDIDATE archive/dev/JOURNAL.md  (score 152.764)
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 149.916)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 135.119)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 131.514)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 58.759)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 49.871)
- CANDIDATE dev/literature/digest.md  (score 46.350)
- CANDIDATE dev/literature/terms-2026-08.md  (score 39.515)
- CANDIDATE dev/literature/geology.md  (score 33.391)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
