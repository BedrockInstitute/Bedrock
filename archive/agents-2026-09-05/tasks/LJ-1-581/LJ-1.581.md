# LJ-1.581: an L-set injection code for the pairs of κ into κ

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-581/Probe581.agda`:

    pairs-into-kappa-coded :
      (κ : S) → IsOrd (fst κ) → IsCardinalL κ
      → <an L-set injection CODE from the pairs of κ into κ>

Land nothing in `src/`. **A code, not an ambient function.**

**`[LJ-1.574]` IS A NO-GO, UPHELD, AND IT NAMED THIS AS THE FIRST OF TWO WAYS
TO REOPEN ROW 5, LEAVING THE CHOICE TO ME. I CHOOSE THIS ONE.** Its own words:

> **"FUND STEP 2 AS ITS OWN TASK.** An L-set injection code from the pairs of κ
> into κ. `[LJ-1.552]` priced it as a chapter. If it lands, step 3 is a
> `hasSeparationL` over the description this file already carries, and the
> selection machinery of sections 3 and 4 is reused unchanged."

**SO THE WORK BELOW AND ABOVE THIS STEP IS ALREADY BUILT.** `[LJ-1.574]` carries
the description and the selection machinery; what it lacks is this one code.

**AND THIS IS THE SQUARE LAW, WHICH THE TREE HAS ONLY AMBIENTLY.**
`src/L/Cardinal.lagda.md:46` calls its injection type **"The ambient injection
type, as the square-law chain carries it."** `[LJ-1.556]` tried to internalize
the whole chapter and returned a NO-GO calling my type **under-hypothesized**.
**This brief does not re-dispatch that type.** It asks for the CODE at one
cardinal, which is what row 5 actually consumes.

**`InjCode` IS A PROPOSITION AT TODAY'S TREE**, measured this week by
`[LJ-1.576]` (`agents/tasks/LJ-1-576/Probe576.agda:77-84`). That is why a code
is worth more here than a function: it untruncates.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-581/Probe581.agda::pairs-into-kappa-coded"]

## SCOPE (write)
- agents/tasks/LJ-1-581/Probe581.agda
- agents/tasks/LJ-1-581/lj-1.581-report.md
- agents/tasks/LJ-1-581/review-of-pairs-into-kappa.md
- agents/tasks/LJ-1-581/runs/

## PREMISES

1. `[LJ-1.574]` is a NO-GO and its critic upheld it. Basis: agents/tasks/LJ-1-574/review-of-LJ-1-574-1.md:1
2. It names this step as the first reopener. Basis: agents/tasks/LJ-1-574/review-of-succ-assignment-definable.md:90
3. It states the machinery above and below is already built. Basis: agents/tasks/LJ-1-574/review-of-succ-assignment-definable.md:90
4. The tree's square law is ambient. Basis: src/L/Cardinal.lagda.md:46
5. `SquareLaw` is imported by `Cardinal`. Basis: src/L/Cardinal.lagda.md:22
6. `[LJ-1.556]` is a NO-GO and calls my wider type under-hypothesized. Basis: agents/tasks/LJ-1-556/lj-1.556-report.md:298
7. Its sections 1 and 2 are green and copyable. Basis: agents/tasks/LJ-1-556/Probe556.agda:1
8. `[LJ-1.567]` is GO and built `col-step`. Basis: agents/tasks/LJ-1-567/lj-1.567-report.md:1
9. `InjCode` is a proposition at today's tree. Basis: agents/tasks/LJ-1-576/Probe576.agda:77
10. `InjCode` has four conjuncts. Basis: src/L/Cardinal.lagda.md:223
11. `[LJ-1.51]` landed `SquareLaw` as a 775-line master. Basis: archive/dev/LJ-dispatch-index.md:100
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

An ambient square law, `[LJ-1.556]`'s green product and its two readings,
`[LJ-1.567]`'s `col-step`, and `[LJ-1.574]`'s description and selection
machinery. **No code at any cardinal.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS WHAT `[LJ-1.567]` LEFT.** It built `col-step`
and its report names the three things `SquareStep` still wants. **Read that
section and say at `file:line` which of the three this obligation actually
needs.** If it needs all three, say so and price them; if it needs one, say
which.

**COPY WHAT IS GREEN.** `[LJ-1.556]`'s sections 1 and 2 are described by its own
report as green Agda a chapter can copy: the product, its two readings, and the
pattern for turning a condition on the components into a formula and then into a
set. **Say which lines you took.**

**DO NOT RE-DISPATCH `[LJ-1.556]`'S TYPE.** Its report forbids it and calls the
type under-hypothesized. **The obligation here is the CODE at one cardinal under
`IsCardinalL`, and nothing wider.**

**NOTHING MAY BE FUNDED AGAINST THE 775-LINE FIGURE.** It is an old number at an
old tree for a different object, and `[LJ-1.556]` said so itself.

**DO NOT BUILD ROW 5 AND DO NOT TOUCH THE ASSIGNMENT.** `[LJ-1.574]` has the
machinery and will be re-queued when this lands. AD12 gives this brief one
obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## WHAT I COPIED`.** The lines taken from
`[LJ-1.556]` and `[LJ-1.567]`, at `file:line`, and what you changed.

**REQUIRED REPORT SECTION `## WHAT ROW 5 NOW NEEDS`.** Given this code, say what
remains before `[LJ-1.574]`'s obligation is payable. **Its report says step 3 is
then a `hasSeparationL` over a description it already carries: say whether you
agree, at `file:line`.**

ESTIMATE: about 230 lines in the probe, of which the obligation is about 60.
BASIS: `[LJ-1.567]` built one formula of this chapter at a comparable size and
`[LJ-1.566]` assembled a code. **Uncertain: the square law is the largest single
object on the remaining bill.** Comparables are of SHAPE and nothing may be
funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the pairs of κ as an L-set.

    -- the pairs of κ, as an L-SET with its two projections, TYPE ONLY

**Write it FIRST and typecheck it ALONE.** `[LJ-1.556]` reports its section 1
delivers the product and its two readings; **check whether that is the same
object** before you build anything on top of it. ESTIMATE: about 15 lines, under
90 seconds.

## WHAT GO AND NO-GO EACH EARN

**A GO REOPENS ROW 5**, which is B10, the conjunct `GCHStatement` has wanted
since the campaign began, and `[LJ-1.574]` says the rest of that row is already
built.

**A NO-GO THAT NAMES THE MISSING PIECE OF THE SQUARE LAW PRICES THE LARGEST
OBJECT ON THE BILL**, which nobody has done at today's tree.

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
  changed_files_none = ["agents/tasks/LJ-1-581/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-581/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-581/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-581/Probe581.agda"]
  changed_files_none = ["agents/tasks/LJ-1-581/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-581/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 193.106)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 176.378)
- CANDIDATE archive/dev/JOURNAL.md  (score 171.798)
- CANDIDATE dev/ARCHIVE.md  (score 142.573)
- CANDIDATE archive/dev/DD-archived.md  (score 137.501)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 59.135)
- CANDIDATE dev/literature/devlin-II5.md  (score 55.942)
- CANDIDATE dev/literature/terms-2026-08.md  (score 44.651)
- CANDIDATE dev/literature/geology.md  (score 37.214)
- CANDIDATE dev/literature/digest.md  (score 37.184)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
