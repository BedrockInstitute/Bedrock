# LJ-1.573: SqCollectAt, which is row 2 and nothing else

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-573/Probe573.agda`:

    sq-collect-at : <`SqCollect` at every ordinal L-cardinal>

which is `[LJ-1.571]`'s `SqCollectAt` (`agents/tasks/LJ-1-571/Probe571.agda:162-163`),
from `src/L/StageBound.lagda.md:44-48`. Land nothing in `src/`.

**`[LJ-1.571]` IS GO AND IT SHRANK ROW 2 TO EXACTLY THIS.** It reports, in its
own words: **"The bill stays at FIVE rows. The fifth row got smaller."** Row 2
was the bare ambient square law at every ordinal L-cardinal; **row 2 is now
`SqCollectAt`, and "everything else on the path is paid out of `src/`."** It
wrote that into the probe itself so nobody could read a discharge into it
(`Probe571.agda:232-234`).

**IT ALSO SETTLED THE CARRIER: AMBIENT, "and the answer was never close."**
`SqLaw : SV.S → Type (ℓ-suc ℓ)` (`agents/tasks/LJ-1-550/Probe550.agda:82`) and
**nothing under the arrow mentions `isL`, `Lset`, `𝒮ʟ`, a code, or the
satisfaction relation.**

**WHAT `SqCollect` ASKS IS A COLLECTION STEP AND THE TREE SAYS SO.**

    SqCollect α =
        ((δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq δ ∥₁)
      → ∥ SqFam α ∥₁

**A POINTWISE TRUNCATED EXISTENCE FOR EACH δ, TURNED INTO ONE TRUNCATED
FAMILY.** `src/L/StageBound.lagda.md:42` calls it "Collection of truncated
squares to a truncated family. Not inhabited." **That comment is a note and not
a measurement, and this task is the measurement.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-573/Probe573.agda::sq-collect-at"]

## SCOPE (write)
- agents/tasks/LJ-1-573/Probe573.agda
- agents/tasks/LJ-1-573/lj-1.573-report.md
- agents/tasks/LJ-1-573/review-of-sq-collect-at.md
- agents/tasks/LJ-1-573/runs/

## PREMISES

1. `[LJ-1.571]` is GO and shrank row 2 to `SqCollectAt`. Basis: agents/tasks/LJ-1-571/Probe571.agda:162
2. It states that the bill stays at five rows. Basis: agents/tasks/LJ-1-571/lj-1.571-report.md:1
3. It wrote the non-discharge into the probe. Basis: agents/tasks/LJ-1-571/Probe571.agda:232
4. `SqLaw` is ambient at every carrier. Basis: agents/tasks/LJ-1-550/Probe550.agda:82
5. `SqCollect` is a collection from pointwise to family. Basis: src/L/StageBound.lagda.md:44
6. The chapter's note calls it not inhabited. Basis: src/L/StageBound.lagda.md:42
7. `[LJ-1.564]`'s bill has this as row 2. Basis: agents/tasks/LJ-1-564/Probe564.agda:456
8. `[LJ-1.568]` found the same shape elsewhere needs DEFINABILITY and not choice. Basis: agents/tasks/LJ-1-568/Probe568.agda:189
9. `[LJ-1.560]` is GO and its obligation was an instantiation. Basis: agents/tasks/LJ-1-560/lj-1.560-report.md:1
10. `[LJ-1.526]` overturned an archived claim by reading the source. Basis: agents/tasks/LJ-1-526/lj-1.526-report.md:1
11. A stop is a deliverable. Basis: AGENTS.md:43
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

A row shrunk to one named input, a carrier verdict, and a chapter comment
saying the input is not inhabited. **No term and no refutation.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS WHETHER THIS IS A CHOICE PRINCIPLE.** Going
from `(δ : S) → ∥ sq δ ∥₁` to `∥ SqFam α ∥₁` is a uniform selection. **Say at
`file:line` whether the tree has anything that performs one**, and name it.

**`[LJ-1.568]` FOUND THAT THE NEIGHBOURING PROBLEM WANTS DEFINABILITY AND NOT
CHOICE.** Its `Def` needs no choice principle because the carve runs through
`hasSeparationL`, which takes an arbitrary formula (`src/L/Axioms/Full.lagda.md:144`).
**Ask whether the same move works here: if `sq δ` is picked by a formula rather
than chosen, the family may come free.** That is a hint and NOT a measurement.
**A measured cure does not transfer by analogy; re-measure it here.**

**DO NOT REACH FOR AN AMBIENT CHOICE PRINCIPLE.** If the only route needs one,
say so and stop: that is a ruling and the mathematician will carry it. **Do not
add an axiom and do not postulate.**

**THE CHAPTER'S COMMENT IS NOT EVIDENCE.** Read the surrounding code before you
believe it. `[LJ-1.526]` overturned an archived claim exactly this way.

**DO NOT ATTEMPT ROWS 1, 3, 4 OR 5.** AD12 gives this brief one obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## CHOICE OR DEFINABILITY`.** One paragraph, with
`file:line`, saying which this row actually needs.

**REQUIRED REPORT SECTION `## WHAT THIS DOES TO THE BILL`.** Say exactly which
rows you paid and which you did not. **Do not read a discharge into anything you
did not inhabit**, the way `[LJ-1.571]` did not.

ESTIMATE: about 160 lines in the probe, of which the obligation is about 40.
BASIS: `[LJ-1.571]` worked this row down to its input at a comparable size.
Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is `SqFam` itself.

    -- SqFam α, unfolded one step, TYPE ONLY

**Write it FIRST and typecheck it ALONE.** What the family has to BE decides
whether a formula can pick it. ESTIMATE: about 10 lines, under 60 seconds.

## WHAT GO AND NO-GO EACH EARN

**A GO TAKES THE BILL FROM FIVE ROWS TO FOUR**, the first row to leave it since
`[LJ-1.564]`.

**A NO-GO THAT SAYS THE ROW NEEDS A CHOICE PRINCIPLE IS A RULING**, and the
owner must hear it, because this development is proving `L ⊨ AC` and an ambient
choice assumption would be a different claim.

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
  changed_files_none = ["agents/tasks/LJ-1-573/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-573/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-573/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-573/Probe573.agda"]
  changed_files_none = ["agents/tasks/LJ-1-573/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-573/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 206.320)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 180.306)
- CANDIDATE archive/dev/JOURNAL.md  (score 176.802)
- CANDIDATE dev/ARCHIVE.md  (score 150.605)
- CANDIDATE archive/dev/DD-archived.md  (score 135.147)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 57.069)
- CANDIDATE dev/literature/devlin-II5.md  (score 53.786)
- CANDIDATE dev/literature/digest.md  (score 46.695)
- CANDIDATE dev/literature/terms-2026-08.md  (score 40.344)
- CANDIDATE dev/literature/geology.md  (score 38.571)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
