# LJ-1.576: restate LeastCardInjL over the CODE, which is the mathematician's answer

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-576/Probe576.agda`:

    least-card-inj-coded :
      <`LeastCardInjL` restated over the CODED injection `InjL`
       (`src/L/GCH.lagda.md:37-38`) instead of the ambient one,
       together with `leastOf` applied to it>

Land nothing in `src/`.

**`[LJ-1.573]` IS A NO-GO, UPHELD, AND IT ASKED THE MATHEMATICIAN A DIRECT
QUESTION. THIS BRIEF IS THE ANSWER: YES, TRY IT.** Its own words:

> **"can `LeastCardInjL` be restated over the CODED injection `InjL`
> (`src/L/GCH.lagda.md:37-38`) instead of the ambient one, so that `leastOf`
> untruncates the code and `readL` reads it"**

**WHY I RULE THAT IT IS WORTH THE TASK, IN THREE MEASURED FACTS.**

1. `[LJ-1.573]` proved row 2 is **the axiom of choice over a set-indexed
   family**: `SqCollect`'s antecedent and consequent are `SetChoice`'s
   implication letter for letter (`src/Base/Choice.lagda.md:55-56`). The index
   is an h-set and the fibre is not a proposition, **so no free untruncation
   applies to the FUNCTION.**
2. The archive already walked into this wall and named the way out.
   `[LJ-1.314]`'s verdict is **"Select the CODE, not the function: `InjCode` is
   a proposition, so `leastOf` untruncates it"**
   (`archive/dev/LJ-dispatch-index.md:371`). **That is an OLD result at an OLD
   tree and nothing may be funded against it**, but it is the same wall under
   the name `InjData` (`:362`).
3. `[LJ-1.568]` measured this week that the neighbouring rows want DEFINABILITY
   and not choice, and that a code is exactly what supplies it
   (`agents/tasks/LJ-1-568/Probe568.agda:189`, `:252`, `:368`).

**THE BLOCKER IS NAMED AND IT IS ONE LINE.** `LeastCardInjL.Inj γ` is
`⟪ fst α ⟫ ↪ ⟪ fst γ ⟫`, the AMBIENT function type
(`src/L/Cardinal.lagda.md:63-64`). **An arbitrary ambient injection carries no
code, so `leastOf` has nothing to be least among.**

**AND THE BRIDGE BACK ALREADY EXISTS IN `src/`.** `readL` turns a code into a
bare ambient injection with no truncation (`src/L/CantorBernstein.lagda.md:33-35`),
and `[LJ-1.573]` checked it at this row's own types as `inj-from-code`
(`agents/tasks/LJ-1-573/Probe573.agda:354-356`).

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-576/Probe576.agda::least-card-inj-coded"]

## SCOPE (write)
- agents/tasks/LJ-1-576/Probe576.agda
- agents/tasks/LJ-1-576/lj-1.576-report.md
- agents/tasks/LJ-1-576/review-of-least-card-inj-coded.md
- agents/tasks/LJ-1-576/runs/

## PREMISES

1. `[LJ-1.573]` is a NO-GO and its critic upheld it. Basis: agents/tasks/LJ-1-573/review-of-LJ-1-573-1.md:1
2. It proves `SqCollect` is `SetChoice`. Basis: src/Base/Choice.lagda.md:55
3. It names the ambient `Inj` as the blocker. Basis: src/L/Cardinal.lagda.md:63
4. It checked `readL` at this row's types. Basis: agents/tasks/LJ-1-573/Probe573.agda:354
5. `readL` turns a code into an ambient injection. Basis: src/L/CantorBernstein.lagda.md:33
6. `InjL` is a truncated `InjCode`. Basis: src/L/GCH.lagda.md:37
7. `InjCode` has four conjuncts. Basis: src/L/Cardinal.lagda.md:223
8. `[LJ-1.314]` named the cure at an old tree. Basis: archive/dev/LJ-dispatch-index.md:371
9. `[LJ-1.305]` is the same wall under another name. Basis: archive/dev/LJ-dispatch-index.md:362
10. `[LJ-1.568]` proved `Def` necessary and sufficient for the sibling rows. Basis: agents/tasks/LJ-1-568/Probe568.agda:368
11. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
12. A stop is a deliverable. Basis: AGENTS.md:43
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

A proof that row 2 is choice over the ambient function, a bridge from codes to
ambient injections in `src/`, and an archived verdict that selecting the code
is the cure. **No restatement.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE PROPOSITION CHECK.** `[LJ-1.314]`'s cure
turns on `InjCode` being a PROPOSITION. **Verify that at today's tree and say it
at `file:line`.** If `InjCode` is not an hProp here, `leastOf` does not
untruncate it and the whole route is closed: say so and stop. **That is an old
verdict and it must be re-measured, not assumed.**

**`[LJ-1.573]` WARNED THAT THE TWO LEASTS MAY DIFFER.** Its words: **"`κL`'s
least is a different predicate from `InjL`'s."** **Say at `file:line` whether
the restated `LeastCardInjL` still selects the same γ**, and if it does not, say
what changes. A restatement that selects a different object has not repaired the
row.

**DO NOT REACH FOR AN AMBIENT CHOICE PRINCIPLE.** `[LJ-1.573]` was forbidden it
and stopped honestly. The same rule binds here. **Do not add an axiom and do not
postulate.**

**DO NOT BUILD `SqCollectAt` ITSELF.** If the restatement lands, say what it now
costs and stop. AD12 gives this brief one obligation.

**DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## IS InjCode A PROPOSITION HERE`.** The measurement
at `file:line`, and what follows from it.

**REQUIRED REPORT SECTION `## WHAT ROW 2 NOW COSTS`.** Given the restatement,
say what remains before `SqCollectAt` is payable. **Do not read a discharge into
anything you did not inhabit**, the way `[LJ-1.570]` and `[LJ-1.571]` did not.

ESTIMATE: about 180 lines in the probe, of which the obligation is about 45.
BASIS: `[LJ-1.573]` worked this row to its question at a comparable size.
Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is whether `InjCode` is an hProp at today's tree.

    -- isProp (InjCode F a b), at this frame, INHABITED or refuted

**Write it FIRST and typecheck it ALONE.** The entire route rests on it and
`[LJ-1.314]`'s verdict is from an old tree. ESTIMATE: about 12 lines, under 90
seconds.

## WHAT GO AND NO-GO EACH EARN

**A GO OPENS ROW 2 WITHOUT A CHOICE PRINCIPLE**, which matters because this
development is PROVING `L ⊨ AC` and must not assume it ambiently.

**A NO-GO THAT SHOWS `InjCode` IS NOT AN hProp CLOSES THE ARCHIVE'S CURE AT
TODAY'S TREE**, which is worth as much: it would tell the mathematician the row
needs an owner ruling and not another attempt.

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
  changed_files_none = ["agents/tasks/LJ-1-576/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-576/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-576/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-576/Probe576.agda"]
  changed_files_none = ["agents/tasks/LJ-1-576/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-576/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 270.303)
- CANDIDATE archive/dev/JOURNAL.md  (score 201.671)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 193.973)
- CANDIDATE dev/ARCHIVE.md  (score 164.241)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 164.091)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 91.005)
- CANDIDATE dev/literature/devlin-II5.md  (score 54.906)
- CANDIDATE dev/literature/digest.md  (score 53.677)
- CANDIDATE dev/literature/geology.md  (score 45.568)
- CANDIDATE dev/literature/terms-2026-08.md  (score 37.029)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
