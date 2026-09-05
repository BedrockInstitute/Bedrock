# LJ-1.586: Def at absorbs, the twelfth parameter

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-586/Probe586.agda`:

    absorbs-definable : <`[LJ-1.568]`'s `Def a b g` at `g := absorbs`>

where `absorbs` is the twelfth parameter of `Devlin55.BoundedSubsetAt`
(`src/L/BoundedSubset.lagda.md:1392`). Land nothing in `src/`.

**`[LJ-1.580]` TRACED ROW 1'S BLOCK TO TWO UNCODED THINGS AND THIS IS ONE OF
THEM.** Its `count-applies-absorbs` (`agents/tasks/LJ-1-580/Probe580.agda:148`)
is `refl` and shows the counting parameter computes through
`comp-inj absorbs (stage-card-upper ...)`
(`src/L/BoundedSubset.lagda.md:1512-1513`). **`absorbs` is a bare `_↪_` with no
`Formula`.**

**`[LJ-1.584]` TAKES THE OTHER ONE**, the stage-cardinality bound. **This brief
takes `absorbs`, and the two are separate objects at separate pairs.**

**AND `absorbs` IS NOT A STRANGER TO THIS CAMPAIGN.** `[LJ-1.540]` is GO and
paid B7, `AbsorbsAt`, the AMBIENT injection
`⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫`. **So the function exists and is delivered;
what it lacks is a description.** `[LJ-1.561]` separately showed that `W` pays
B7 (`agents/tasks/LJ-1-561/Probe561.agda:388-391`), and `[LJ-1.568]` proved `W`
at a given `g` is EQUIVALENT to `Def` at that `g` (`:252`, `:377`).

**SO THIS OBLIGATION IS B7'S OWN MISSING PIECE, AND ROW 1 NEEDS IT TOO.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-586/Probe586.agda::absorbs-definable"]

## SCOPE (write)
- agents/tasks/LJ-1-586/Probe586.agda
- agents/tasks/LJ-1-586/lj-1.586-report.md
- agents/tasks/LJ-1-586/review-of-absorbs-definable.md
- agents/tasks/LJ-1-586/runs/

## PREMISES

1. `[LJ-1.580]` is a NO-GO and its critic upheld it. Basis: agents/tasks/LJ-1-580/review-of-beta-into-alpha-coded.md:11
2. Its `count-applies-absorbs` is `refl`. Basis: agents/tasks/LJ-1-580/Probe580.agda:148
3. `absorbs` is the twelfth parameter and a bare `_↪_`. Basis: src/L/BoundedSubset.lagda.md:1392
4. `code-inj` composes `absorbs` with the stage bound. Basis: src/L/BoundedSubset.lagda.md:1512
5. `[LJ-1.540]` is GO and paid B7. Basis: agents/tasks/LJ-1-540/lj-1.540-report.md:1
6. `[LJ-1.561]` pays B7 from `W`. Basis: agents/tasks/LJ-1-561/Probe561.agda:388
7. `Def` is sufficient for `W`. Basis: agents/tasks/LJ-1-568/Probe568.agda:252
8. Every sufficient hypothesis implies `Def`. Basis: agents/tasks/LJ-1-568/Probe568.agda:377
9. `Def` is stated at its probe. Basis: agents/tasks/LJ-1-568/Probe568.agda:189
10. `hasSeparationL` takes an arbitrary formula. Basis: src/L/Axioms/Full.lagda.md:144
11. `[LJ-1.533]` refuted a code for an ARBITRARY ambient injection. Basis: agents/tasks/LJ-1-533/lj-1.533-report.md:1
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

`absorbs` as a delivered ambient injection (B7, `[LJ-1.540]`), and a proof that
describing it is exactly what `W` at that `g` needs. **No description.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS WHETHER `absorbs` IS A PARAMETER OR A TERM.**
`src/L/BoundedSubset.lagda.md:1392` makes it the twelfth PARAMETER of the
module. **A parameter has no definition to describe.** Say at `file:line`
whether the module is ever instantiated with a specific `absorbs`, and if so,
with what. **If it is only ever a parameter, this obligation must be stated as
"for any `absorbs` that IS definable" and you say so before building.**

**THAT DISTINCTION IS THE WHOLE TASK AND I DO NOT KNOW THE ANSWER.** If
`[LJ-1.540]`'s B7 term is what instantiates it, describe THAT. If nothing
instantiates it, the row wants a hypothesis and not a construction, and the
mathematician needs to hear that sentence.

**DO NOT ATTEMPT A CODE FOR AN ARBITRARY AMBIENT INJECTION.** `[LJ-1.533]`
refuted it. **`absorbs` is one named injection with a delivered construction, or
it is a parameter; either way it is not the arbitrary case.**

**DO NOT BUILD THE STAGE-CARDINALITY BOUND.** `[LJ-1.584]` has it. AD12 gives
this brief one obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## PARAMETER OR TERM`.** The answer at `file:line`,
and what follows for the shape of the obligation.

**REQUIRED REPORT SECTION `## WHAT B7 AND ROW 1 EACH GET`.** Two sentences.
`[LJ-1.561]` pays B7 from `W`, and `[LJ-1.580]` needs `absorbs` coded for row 1.
**Say whether one description serves both.** Do not build either row.

ESTIMATE: about 180 lines in the probe, of which the obligation is about 45.
BASIS: `[LJ-1.568]` built `Def` and its two directions at a comparable size.
Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is `absorbs` itself: parameter, or instantiated term.

    -- every instantiation of Devlin55.BoundedSubsetAt's twelfth parameter,
    -- found by grep over src/, listed at file:line

**Do this FIRST and report the count.** **Never conclude a count from a command
containing `head`.** ESTIMATE: one grep and about 10 lines, under 10 minutes.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS B7'S MISSING PIECE AND ONE OF ROW 1'S TWO**, and with `[LJ-1.584]`
the pair would be complete.

**A NO-GO SAYING `absorbs` IS ONLY EVER A PARAMETER IS A FULL RESULT**, because
it would mean row 1 wants a hypothesis carried and not a term built, and that
changes what the mathematician queues next.

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
  changed_files_none = ["agents/tasks/LJ-1-586/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-586/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-586/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-586/Probe586.agda"]
  changed_files_none = ["agents/tasks/LJ-1-586/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-586/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 170.338)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 148.373)
- CANDIDATE archive/dev/JOURNAL.md  (score 137.653)
- CANDIDATE dev/ARCHIVE.md  (score 117.335)
- CANDIDATE archive/dev/DD-archived.md  (score 106.935)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 52.946)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 49.284)
- CANDIDATE dev/literature/terms-2026-08.md  (score 42.772)
- CANDIDATE dev/literature/digest.md  (score 34.080)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 28.215)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
