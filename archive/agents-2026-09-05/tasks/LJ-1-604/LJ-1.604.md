# LJ-1.604: is ingredient (iii) the same object as sq

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-604/Probe604.agda`:

    third-is-sq : <ingredient (iii) of `[LJ-1.594]`'s table> ↔ <a formula for
                   `sq`, `src/L/StageCardinal.lagda.md:17-19`>

**or the term that shows they are different objects.** Land nothing in `src/`.

**FOUR TASKS NOW POINT AT `sq` AND NOBODY HAS ASKED WHETHER IT IS INGREDIENT
(iii).** The arrivals, each independent:

- `[LJ-1.572]` unfolded B9's `g` by `refl` and bottomed out at `sq`
  (`agents/tasks/LJ-1-572/review-of-b9-g-definable.md:116`).
- `[LJ-1.594]` proposed "give `L.StageCardinal` a definable pairing instead of
  `sq`" as its route 2.
- `[LJ-1.597]` read `step`'s value equation and it is
  `fst (sq α α∈suc infα) (m , cnt m φ) ≡ y`.
- `[LJ-1.594]` separately writes that **"(iii) is the hypothesis"**
  (`agents/tasks/LJ-1-594/review-of-pairing-suffices.md:79`), and calls the
  pairing **"the smallest of the five"** (`:138`).

**`sq` IS A PAIRING.** Its type at `src/L/StageCardinal.lagda.md:17-19` is a
function `⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫` with an injectivity proof, and nothing else.
**So "the pairing" and "`sq`" LOOK like one object. That is a resemblance, and
resemblances have been wrong twice in this campaign.**

**MEASURE IT. DO NOT AGREE WITH ME.** `[LJ-1.577]` asserted two legs were both
L-data and `[LJ-1.580]` measured one was not. I claimed a formula would pay rows
1 and 4 and `[LJ-1.585]` answered "ONE AT MOST, AND NOT ROW 4". **This brief
exists because I would otherwise assert it.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-604/Probe604.agda::third-is-sq"]

## SCOPE (write)
- agents/tasks/LJ-1-604/Probe604.agda
- agents/tasks/LJ-1-604/lj-1.604-report.md
- agents/tasks/LJ-1-604/review-of-third-is-sq.md
- agents/tasks/LJ-1-604/runs/

## PREMISES

1. `[LJ-1.594]` writes that (iii) is the hypothesis. Basis: agents/tasks/LJ-1-594/review-of-pairing-suffices.md:79
2. It calls the pairing the smallest of the five and orders it last. Basis: agents/tasks/LJ-1-594/review-of-pairing-suffices.md:138
3. `sq` is a pairing with injectivity and nothing else. Basis: src/L/StageCardinal.lagda.md:17
4. `[LJ-1.572]` bottomed out at `sq`. Basis: agents/tasks/LJ-1-572/review-of-b9-g-definable.md:116
5. `[LJ-1.597]` read `sq` in the value equation. Basis: src/L/StageCardinal.lagda.md:283
6. `[LJ-1.585]` refuted a resemblance of mine by measurement. Basis: agents/tasks/LJ-1-585/Probe585.agda:163
7. `[LJ-1.580]` refuted another. Basis: agents/tasks/LJ-1-580/review-of-beta-into-alpha-coded.md:40
8. `[LJ-1.601]` is GO and re-priced (iv) at its base. Basis: agents/tasks/LJ-1-601/lj-1.601-report.md:1
9. `[LJ-1.568]` proved coding is describing, necessary and sufficient. Basis: agents/tasks/LJ-1-568/Probe568.agda:377
10. `hasSeparationL` takes an arbitrary formula. Basis: src/L/Axioms/Full.lagda.md:144
11. A stop is a deliverable. Basis: AGENTS.md:43
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

Four independent arrivals at one parameter, and a five-ingredient table whose
third entry is called a hypothesis. **No term relating them.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE TWO TYPES SIDE BY SIDE.** Write
ingredient (iii) as `[LJ-1.594]` states it and `sq` as the module states it, in
one file, and say at `file:line` what differs: the carrier, the arity, the side
conditions. **`[LJ-1.585]` found that SIDE CONDITIONS broke the last
resemblance. Check them first.**

**DO NOT BUILD A FORMULA FOR EITHER.** This brief asks whether they are one
object, not whether either is definable. **`[LJ-1.526]` did exactly this half
for B4 and `[LJ-1.528]` built the other half afterwards; that is the pattern
and it works.**

**IF THEY ARE ONE, SAY WHAT (iii) THEN COSTS.** `[LJ-1.594]` calls it the
smallest of the five, **but that is its judgement and not a measurement.** Say
whether you agree, at `file:line`.

**IF THEY ARE DIFFERENT, SAY WHICH IS STRONGER**, because that decides which one
a later brief should target.

**CAP EVERY TYPECHECK ON A WALL CLOCK YOU SET AND REPORT THE CAP.**

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE TWO OBJECTS`.** Carrier, arity and side
conditions for each, at `file:line`.

**REQUIRED REPORT SECTION `## WHAT (iii) COSTS IF THEY ARE ONE`.** Two sentences,
and say plainly whether "the smallest of the five" survives your read.

ESTIMATE: about 130 lines in the probe, of which the obligation is about 30.
BASIS: `[LJ-1.585]` and `[LJ-1.591]` did the same shape of comparison.
Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is whether the two can be written in one file at all.

    -- ingredient (iii) and sq, restated side by side, TYPE ONLY, capped

**Write it FIRST, typecheck it ALONE, cap it.** ESTIMATE: about 15 lines, cap at
two minutes.

## WHAT GO AND NO-GO EACH EARN

**A GO NAMES ONE OBJECT FOR FOUR ARRIVALS**, and if "smallest of the five"
holds, the route's last piece is also its cheapest.

**A NO-GO SAVES THE CAMPAIGN FROM FUNDING THE WRONG PAIRING**, which is the
error I have made twice on resemblances.

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
  changed_files_none = ["agents/tasks/LJ-1-604/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-604/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-604/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-604/Probe604.agda"]
  changed_files_none = ["agents/tasks/LJ-1-604/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-604/review-of-*.md"]

[[branch]]
# PARK, NOT ESCALATE. MEASURED on LJ-1.534, 2026-08-22: this row matched
# a heap wall FOUR times, exit 251 each, to attempt_max. A critic
# re-runs the same probe and re-hits the same wall, so an escalation can only
# loop. **A heap wall is a resource fact and no critic can adjudicate it.**
id = "heap-wall-park"
priority = 30
action = "park"

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
  Full entry: dev/LESSONS.md:2307
- **P-l. A statement may be ABOUT a concrete stage without dragging that stage's PRESENTATION into its type**
  **The law.** Being about a concrete position is not what costs. Naming a transparent construction in a statement's TYPE is. If the tower's stage values are `opaque` upstream, a theorem may quantify over, hypothesize about and conclude at `Sset ω` freely, because the stage is an ATOM to the elaborator and nothing unfolds. If instead the type mentions a transparent presentation, such as `⟪ sucV (...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2367
- **D-26. A well-founded key on a tower needs generation data, or it needs syntax**
  **Rule:** When a route must well-order a cumulative tower's stage, ask first what the stage's members CARRY. A stage built as the values of finitely many total operations carries its own generation data, so a well-founded key exists with NO syntax at all: the operation index, then the arguments, ordered recursively. A stage built as a definable power carries nothing: its members are sets, not c...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:1735
- **C-42. A refutation measures the site it names, and it never measures how far that site extends**
  **Rule:** A refutation is a measurement of ONE site. It says the statement there is false. **It says nothing about how many other sites carry the same false shape.** So when a refutation lands, the next action is not the cure. **It is the sweep: search the tree for the shape, and report the COUNT before you price the cure.** A cure funded against the named site is priced against a number nobody...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:3762

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev, archive/scripts, dev/ARCHIVE.md:
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 175.445)
- CANDIDATE archive/dev/JOURNAL.md  (score 174.939)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 168.228)
- CANDIDATE dev/ARCHIVE.md  (score 145.154)
- CANDIDATE archive/dev/DD-archived.md  (score 140.606)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 51.187)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 44.557)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 43.673)
- CANDIDATE dev/literature/geology.md  (score 36.669)
- CANDIDATE dev/literature/terms-2026-08.md  (score 34.726)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
