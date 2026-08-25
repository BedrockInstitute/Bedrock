# LJ-1.585: are rows 1 and 4 the same missing formula

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-585/Probe585.agda`:

    one-formula-two-rows :
      <`[LJ-1.568]`'s `Def` at `stage-card-upper`>
      → <row 1's residue> × <row 4, `StageCountedCoded`>

or, if one of the two does not follow, the term that says which and why. Land
nothing in `src/`.

**THIS IS A READING OF MINE AND I WANT IT MEASURED BEFORE ANYTHING IS FUNDED ON
IT.** The two type signatures look like the same object:

- `stage-card-upper : ... → ⟪ Lset α ⟫ ↪ ⟪ α ⟫`
  (`src/L/StageCardinal.lagda.md:564-566`), the AMBIENT injection.
- `StageCountedCoded = (δ Lδ : SL.S) → IsOrd (fst δ) → (fst Lδ ≡ Lset (fst δ))
  → InjL Lδ δ` (`agents/tasks/LJ-1-523/Probe523.agda:258-261`), which is row 4
  of `[LJ-1.564]`'s bill and is the CODED form of the same injection.

**AND `[LJ-1.580]`'s REOPENER FOR ROW 1 NAMES THAT SAME OBJECT**: "a formula,
with parameters in L, that describes an injection of `Lset β` into α."

**IF THEY ARE ONE, ONE PAYMENT CLEARS TWO OF THE BILL'S FIVE ROWS.** That is
worth one task to find out, and `[LJ-1.561]` did exactly this move for three
other rows and it held.

**DO NOT BUILD THE FORMULA.** `[LJ-1.584]` has it. This brief takes it as a
hypothesis and asks only what it buys.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-585/Probe585.agda::one-formula-two-rows"]

## SCOPE (write)
- agents/tasks/LJ-1-585/Probe585.agda
- agents/tasks/LJ-1-585/lj-1.585-report.md
- agents/tasks/LJ-1-585/review-of-one-formula-two-rows.md
- agents/tasks/LJ-1-585/runs/

## PREMISES

1. `[LJ-1.564]`'s bill is five rows. Basis: agents/tasks/LJ-1-564/Probe564.agda:456
2. Row 4 is `StageCountedCoded`. Basis: agents/tasks/LJ-1-523/Probe523.agda:258
3. `stage-card-upper` is the ambient bound. Basis: src/L/StageCardinal.lagda.md:564
4. `[LJ-1.580]` is a NO-GO and names the same object as its reopener. Basis: agents/tasks/LJ-1-580/review-of-beta-into-alpha-coded.md:117
5. Its `obligation-from-leg2` does not read the ambient injection. Basis: agents/tasks/LJ-1-580/Probe580.agda:303
6. `Def` is stated at its probe. Basis: agents/tasks/LJ-1-568/Probe568.agda:189
7. Every sufficient hypothesis implies `Def`. Basis: agents/tasks/LJ-1-568/Probe568.agda:377
8. `InjL` is a truncated `InjCode`. Basis: src/L/GCH.lagda.md:37
9. `[LJ-1.561]` made the same move for three rows and it held. Basis: agents/tasks/LJ-1-561/Probe561.agda:287
10. `[LJ-1.577]` asserted both legs were L-data and `[LJ-1.580]` measured otherwise. Basis: agents/tasks/LJ-1-580/review-of-beta-into-alpha-coded.md:40
11. A stop is a deliverable. Basis: AGENTS.md:43
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

Two typed statements that look like one object, and no term relating them.

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE PAIR.** Say at `file:line` what pair each
of the two wants: row 4 wants `(Lδ , δ)`, and row 1's residue wants whatever
`[LJ-1.580]` measured. **`[LJ-1.580]` recorded that `at-β→at-κ`
(`Probe580.agda:263`) carries its code to `(κᴸ , αᴸ)` and NOT `(βᴸ , αᴸ)`.**
**If the pairs differ, say so: that is the answer and it is a NO-GO.**

**BE READY FOR THE ANSWER TO BE NO.** `[LJ-1.577]` asserted both of `β↪α`'s legs
were built from L-data, and `[LJ-1.580]` measured that leg 2 is not
(`review-of-beta-into-alpha-coded.md:40`). **An assertion about these objects has
been wrong once this week. Measure, do not agree with me.**

**DO NOT BUILD THE FORMULA AND DO NOT BUILD EITHER ROW.** Take `Def` as a
hypothesis. AD12 gives this brief one obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE TWO PAIRS`.** Each at `file:line`, and whether
they unify.

**REQUIRED REPORT SECTION `## HOW MANY ROWS ONE FORMULA BUYS`.** One, two, or
neither, with the implication's name at `file:line`. **Do not read a discharge
into anything you did not inhabit.**

ESTIMATE: about 130 lines in the probe, of which the obligation is about 30.
BASIS: `[LJ-1.561]` built five implications of this shape at a comparable size.
Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is whether the two statements can be written in one file at all.

    -- row 1's residue and row 4, imported or restated, side by side, TYPE ONLY

**Write it FIRST and typecheck it ALONE.** ESTIMATE: about 20 lines, under 2
minutes.

## WHAT GO AND NO-GO EACH EARN

**A GO MEANS `[LJ-1.584]` PAYS TWO ROWS AND THE BILL DROPS TO THREE.**

**A NO-GO SAVES THE CAMPAIGN FROM PLANNING AGAINST A RESEMBLANCE**, which is
exactly the error `[LJ-1.577]` made about the two legs.

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
  changed_files_none = ["agents/tasks/LJ-1-585/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-585/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-585/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-585/Probe585.agda"]
  changed_files_none = ["agents/tasks/LJ-1-585/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-585/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 160.318)
- CANDIDATE archive/dev/JOURNAL.md  (score 152.019)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 143.033)
- CANDIDATE dev/ARCHIVE.md  (score 127.798)
- CANDIDATE archive/dev/DD-archived.md  (score 117.095)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 55.476)
- CANDIDATE dev/literature/devlin-II5.md  (score 42.028)
- CANDIDATE dev/literature/digest.md  (score 35.576)
- CANDIDATE dev/literature/geology.md  (score 28.481)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 28.180)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
