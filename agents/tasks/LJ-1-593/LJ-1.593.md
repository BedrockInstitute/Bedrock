# LJ-1.593: the coded square law, at the spelling its predecessor decided

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-593/Probe593.agda`:

    square-coded :
      (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
      → <a CODED injection of the pairs of κ into κ>

Land nothing in `src/`. **That spelling is not mine and I did not choose it.**

**`[LJ-1.589]` IS GO AND ITS WHOLE PURPOSE WAS TO FIX THIS TYPE.** `[LJ-1.581]`
recommended threading the infinity clause first because it "decides the shape of
the square-law brief rather than following it". It did. In `[LJ-1.589]`'s words:

> The square-law task must conclude a coded square at every κ that satisfies
> `IsOrd (fst κ)`, `IsCardinalL κ` and `(⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)`, in that
> spelling, because those three are what row 5 now carries (`SuccIntoPowerInf`,
> `agents/tasks/LJ-1-589/Probe589.agda:243-247`) and what the campaign's bill
> now passes down (`gch-from-five-inf`, `:421-429`).

**AND IT REFUTED THE TYPE I WOULD OTHERWISE HAVE QUEUED.** It says the task
**must NOT** be stated as `SquareStepInf` (`agents/tasks/LJ-1-581/Probe581.agda:427-432`),
because that type's clause `⟨ ω ∈ fst κ ⟩` **is refuted at ω**
(`agents/tasks/LJ-1-589/Probe589.agda:161-162`), which is an L-ordinal the
trophy's own clause admits (`:153-158`), and **no hypothesis the tree has repairs
that gap** (`:174-178`).

**IT ALSO ALLOWS ONE ALTERNATIVE.** The type "may equally be stated in
`CodedShift`'s two-hypothesis idiom" (`src/L/CodedShift.lagda.md:38-39`),
because the second hypothesis is derivable. **Either spelling is admissible;
say which you used.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-593/Probe593.agda::square-coded"]

## SCOPE (write)
- agents/tasks/LJ-1-593/Probe593.agda
- agents/tasks/LJ-1-593/lj-1.593-report.md
- agents/tasks/LJ-1-593/review-of-square-coded.md
- agents/tasks/LJ-1-593/runs/

## PREMISES

1. `[LJ-1.589]` is GO and fixes the spelling. Basis: agents/tasks/LJ-1-589/lj-1.589-report.md:1
2. Row 5 now carries the three hypotheses. Basis: agents/tasks/LJ-1-589/Probe589.agda:243
3. The bill passes them down. Basis: agents/tasks/LJ-1-589/Probe589.agda:421
4. `SquareStepInf`'s clause is refuted at ω. Basis: agents/tasks/LJ-1-589/Probe589.agda:161
5. ω is admitted by the trophy's own clause. Basis: agents/tasks/LJ-1-589/Probe589.agda:153
6. `CodedShift`'s idiom is the admissible alternative. Basis: src/L/CodedShift.lagda.md:38
7. `[LJ-1.581]` is a NO-GO on the earlier spelling. Basis: agents/tasks/LJ-1-581/Probe581.agda:427
8. `[LJ-1.556]` called my wider square type under-hypothesized. Basis: agents/tasks/LJ-1-556/lj-1.556-report.md:298
9. Its sections 1 and 2 are green and copyable. Basis: agents/tasks/LJ-1-556/Probe556.agda:1
10. `[LJ-1.567]` is GO and built `col-step`. Basis: agents/tasks/LJ-1-567/lj-1.567-report.md:1
11. `InjCode` is a proposition at today's tree. Basis: agents/tasks/LJ-1-576/Probe576.agda:77
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

A decided type, `[LJ-1.556]`'s green product and readings, `[LJ-1.567]`'s
`col-step`, and an ambient square law. **No coded square at any cardinal.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE SPELLING.** State the type in full, cite
`[LJ-1.589]`'s three hypotheses at `file:line`, and say which of the two
admissible spellings you took and why. **If you find a third, say so and justify
it against `[LJ-1.589]`'s refutation at ω.**

**COPY WHAT IS GREEN.** `[LJ-1.556]`'s sections 1 and 2 and `[LJ-1.567]`'s
`col-step` are committed. **Say which lines you took.**

**DO NOT RE-DISPATCH `[LJ-1.556]`'S TYPE**, which its own report calls
under-hypothesized, and **do not state `SquareStepInf`**, which `[LJ-1.589]`
refuted at ω.

**THIS IS THE LARGEST OBJECT LEFT ON THE BILL AND THE ESTIMATE IS THE LEAST
CERTAIN IN THE QUEUE.** Two dispatches have already returned NO-GO on it.
**Write the report as a skeleton first and fill it as runs land**, so a timeout
leaves something behind.

**DO NOT ATTEMPT ROW 5 ITSELF.** AD12 gives this brief one obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE SPELLING I USED`.** Which, and why, at
`file:line`.

**REQUIRED REPORT SECTION `## WHAT ROW 5 NOW NEEDS`.** `[LJ-1.574]` said step 3
is then a `hasSeparationL` over a description it already carries. **Say whether
you agree, at `file:line`.**

ESTIMATE: about 260 lines in the probe, of which the obligation is about 70.
BASIS: `[LJ-1.567]` built one formula of this chapter and `[LJ-1.566]` assembled
a code. **Least certain estimate in the queue, and I say so.** Comparables are
of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the pairs of κ as an L-set at THIS spelling.

    -- the pairs of κ, as an L-SET, under the three hypotheses, TYPE ONLY

**Write it FIRST and typecheck it ALONE.** `[LJ-1.556]` reports its section 1
delivers a product; **check it is the same object under these hypotheses.**
ESTIMATE: about 15 lines, under 2 minutes.

## WHAT GO AND NO-GO EACH EARN

**A GO REOPENS ROW 5**, and `[LJ-1.574]` says the rest of that row is already
built.

**A NO-GO AT THIS SPELLING IS THE THIRD ON THIS OBJECT AND WOULD BE A RULING**:
the mathematician would take to the owner that the coded square law is the
campaign's standing blocker, with three measured attempts behind it.

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
  changed_files_none = ["agents/tasks/LJ-1-593/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-593/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-593/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-593/Probe593.agda"]
  changed_files_none = ["agents/tasks/LJ-1-593/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-593/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 193.335)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 181.503)
- CANDIDATE archive/dev/JOURNAL.md  (score 166.277)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 139.208)
- CANDIDATE dev/ARCHIVE.md  (score 131.691)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 54.102)
- CANDIDATE dev/literature/devlin-II5.md  (score 52.571)
- CANDIDATE dev/literature/terms-2026-08.md  (score 43.787)
- CANDIDATE dev/literature/digest.md  (score 41.858)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 33.982)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
