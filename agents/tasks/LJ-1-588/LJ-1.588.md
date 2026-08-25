# LJ-1.588: does gch-from-five need row 4 unrestricted

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-588/Probe588.agda`:

    gch-from-restricted-row4 :
      <`[LJ-1.564]`'s `gch-from-five`, with row 4 replaced by
       `[LJ-1.585]`'s `Row4Restricted`>

or the term naming the call site that needs row 4 unrestricted. Land nothing in
`src/`.

**`[LJ-1.585]` IS GO AND IT REFUTED MY READING, WHICH IS WHY I QUEUED IT.** I
said the stage-cardinality formula would pay rows 1 and 4 both. Its answer:
**"ONE AT MOST, AND NOT ROW 4. Never two."**

**BUT IT DID NOT SAY ROW 4 IS UNREACHABLE. IT SAID ROW 4 IS BOUGHT IN A
RESTRICTED FORM.** `def→row4-restricted` (`agents/tasks/LJ-1-585/Probe585.agda:172-173`)
is the implication, and `Row4Restricted` (`:163-166`) is row 4 carrying
`stage-card-upper`'s own two side conditions, **`δ ∈ sucV α₀` and `δ ∉ ω`**
(`src/L/StageCardinal.lagda.md:564-566`), with nothing else changed.

**AND IT GAVE THE REASON AS A PRINCIPLE:** **"THE HYPOTHESIS CANNOT BE STATED
MORE WIDELY THAN THE FUNCTION IT IS ABOUT."** Where the two conditions fail,
`stage-card-upper` has no value at all.

**SO THE QUESTION IS NOT WHETHER ROW 4 CAN BE WIDENED. IT IS WHETHER THE BILL
EVER NEEDS IT WIDE.** `gch-from-five` (`agents/tasks/LJ-1-564/Probe564.agda:456-463`)
is one term with one body. **Read where it spends row 4 and find out.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-588/Probe588.agda::gch-from-restricted-row4"]

## SCOPE (write)
- agents/tasks/LJ-1-588/Probe588.agda
- agents/tasks/LJ-1-588/lj-1.588-report.md
- agents/tasks/LJ-1-588/review-of-gch-from-restricted-row4.md
- agents/tasks/LJ-1-588/runs/

## PREMISES

1. `[LJ-1.585]` is GO. Basis: agents/tasks/LJ-1-585/lj-1.585-report.md:1
2. It buys row 4 only in the restricted form. Basis: agents/tasks/LJ-1-585/Probe585.agda:172
3. `Row4Restricted` carries two side conditions. Basis: agents/tasks/LJ-1-585/Probe585.agda:163
4. Those conditions are `stage-card-upper`'s own. Basis: src/L/StageCardinal.lagda.md:564
5. `gch-from-five` is the bill. Basis: agents/tasks/LJ-1-564/Probe564.agda:456
6. Row 4 is `StageCountedCoded`. Basis: agents/tasks/LJ-1-523/Probe523.agda:258
7. `[LJ-1.568]`'s `no-free-lunch-at-B9` is the imported implication. Basis: agents/tasks/LJ-1-568/Probe568.agda:454
8. `GCHStatement` quantifies over infinite L-cardinals. Basis: src/L/GCH.lagda.md:59
9. Its fourth hypothesis excludes ω. Basis: src/L/GCH.lagda.md:64
10. `[LJ-1.577]` asserted a resemblance and `[LJ-1.580]` measured it false. Basis: agents/tasks/LJ-1-580/review-of-beta-into-alpha-coded.md:40
11. A stop is a deliverable. Basis: AGENTS.md:43
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

A five-row bill, and a proof that the stage formula reaches row 4 only under two
side conditions. **Nothing says whether the bill needs more.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE SPEND SITE.** Read `gch-from-five`'s body
and say at `file:line` **every place row 4 is applied, and with what δ.**

**THE FOURTH HYPOTHESIS OF `GCHStatement` MAY ALREADY GIVE YOU ONE CONDITION.**
`src/L/GCH.lagda.md:64` reads `(⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)`. **Say whether that
propagates to the δ row 4 is spent at.** If it does, one of the two side
conditions is free and you should say so plainly.

**THE OTHER CONDITION IS `δ ∈ sucV α₀` AND IT IS A BOUND.** Say where `α₀` comes
from at the spend site and whether the bound holds there. **If it does not, that
is the answer and this task is a NO-GO with a named site.**

**DO NOT WIDEN `stage-card-upper` AND DO NOT WRITE A FORMULA.** `[LJ-1.585]`
proved the hypothesis cannot be stated more widely than the function.
`[LJ-1.584]` is writing the formula. AD12 gives this brief one obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## WHERE ROW 4 IS SPENT`.** Every site at
`file:line`, with the δ and whether both conditions hold there.

**REQUIRED REPORT SECTION `## WHAT THIS DOES TO THE BILL`.** Whether the
restricted row suffices. **Do not read a discharge into anything you did not
inhabit.**

ESTIMATE: about 140 lines in the probe, of which the obligation is about 30.
BASIS: `[LJ-1.585]` worked the same two terms at a comparable size. Comparables
are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the δ that `gch-from-five` spends row 4 at.

    -- that δ, with its hypotheses in scope, written out, TYPE ONLY

**Write it FIRST and typecheck it ALONE.** Everything else follows from what is
true of that one object. ESTIMATE: about 12 lines, under 90 seconds.

## WHAT GO AND NO-GO EACH EARN

**A GO MEANS `[LJ-1.584]`'S FORMULA PAYS ROW 4 AFTER ALL**, and the bill drops
by one without any new mathematics.

**A NO-GO NAMES THE SITE THAT NEEDS THE WIDE ROW**, and then the campaign knows
it must widen `stage-card-upper` itself, which nobody has priced.

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
  changed_files_none = ["agents/tasks/LJ-1-588/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-588/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-588/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-588/Probe588.agda"]
  changed_files_none = ["agents/tasks/LJ-1-588/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-588/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 169.976)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 169.299)
- CANDIDATE archive/dev/JOURNAL.md  (score 165.000)
- CANDIDATE dev/ARCHIVE.md  (score 143.675)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 141.295)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 61.692)
- CANDIDATE dev/literature/devlin-II5.md  (score 51.892)
- CANDIDATE dev/literature/digest.md  (score 37.871)
- CANDIDATE dev/literature/geology.md  (score 34.158)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 32.129)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
