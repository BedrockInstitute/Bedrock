# LJ-1.522: the definable powerset closure, from K being a limit level

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-522/Probe522.agda`:

    defPow-closed :
        (K is a limit level)
      → (every definable subset of a member of K, with a code and an
         environment in K, is a member of K)

**as a FRAME HYPOTHESIS discharged from the limit, not as a conjunct of any
formula.** Land nothing in `src/`.

**`[LJ-1.520]` IS GO AND ITS TABLE LEAVES EXACTLY ONE ROW UNPAID.** Of the nine
hypotheses the graded formula needs, two are no longer needed because `pins`
says them (`agents/tasks/LJ-1-520/Probe520.agda:108`), one is said by `transK`
(`:95`), five are ordinary hypotheses on `K` already stated in
`src/L/Condensation.lagda.md`, and the ninth is this one: **"`K` is closed
under the definable powerset of its members: nowhere in the tree, NOT SAID AND
NOT SAYABLE."**

**AND IT MEASURED WHY IT CANNOT GO IN THE FORMULA.** To say `K` holds the
definable subsets of its members needs a quantifier over those subsets, and the
only term available to bound it is `K` itself. **That is circular, so the
closure cannot be written `Δ₀` with `K` as the sole bound, and no work on the
formula will change it.**

**AND IT NAMED THE CURE.** `leafB` describes `d` as the definable powerset of
`w` and its second half is bounded by `K` (`src/L/Condensation.lagda.md:2398-2402`).
For that half to say what the unbounded `extAt` says, `K` must already hold
every definable subset of every member of `K` that has a code and an
environment in `K`. **"A transitive `K` does not give this. A limit level
does."**

**SO THE HYPOTHESIS GOES IN THE FRAME.** That is the same shape the `TFacts`
front reached at `[LJ-1.508]` and `[LJ-1.503]`: the weakest sufficient
hypothesis, stated where the carrier is a value, not forced into a
tower-generic type.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-522/Probe522.agda::defPow-closed"]

## SCOPE (write)
- agents/tasks/LJ-1-522/Probe522.agda
- agents/tasks/LJ-1-522/lj-1.522-report.md
- agents/tasks/LJ-1-522/review-of-defPow-closed.md
- agents/tasks/LJ-1-522/runs/

## PREMISES

1. `[LJ-1.520]` is GO and its cost table leaves this row unpaid. Basis: agents/tasks/LJ-1-520/lj-1.520-report.md:237
2. It measured that the closure cannot be written `Δ₀` with `K` as the sole bound. Basis: agents/tasks/LJ-1-520/lj-1.520-report.md:262
3. It named a limit level as what supplies it. Basis: agents/tasks/LJ-1-520/lj-1.520-report.md:259
4. `leafB` is the site whose bounded half needs it. Basis: src/L/Condensation.lagda.md:2398
5. `transK` already says the satisfier closure. Basis: src/L/Condensation.lagda.md:2517
6. `Σ₁` HAS an unbounded existential constructor. Basis: src/FOL/LevyHierarchy.lagda.md:75
7. A delivered `Σ₁` certificate already exists at the class carrier. Basis: src/L/BoundedSubset.lagda.md:145
8. `[LJ-1.228]` recorded that certificate. Basis: agents/tasks/LJ-1-228/lj-1.228-report.md:36
9. `[LJ-1.519]` is running the limit for a different statement. Basis: agents/tasks/LJ-1-519/LJ-1.519.md:1
10. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
11. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**`[LJ-1.520]` BUILT THE GRADED FORMULA AND `[LJ-1.516]` BUILT THE TRANSPORT.**
Eight of the nine hypotheses the grade needs are said or no longer needed.
**This is the ninth.**

## THE REASONING

**D-10, BEFORE ANY AGDA.** Say at `file:line` what the tree's notion of a limit
level is and whether `Lset` at a limit is the union of its predecessors. **If
the tree has no such reading, the limit cannot discharge the closure and the
task stops there**: that would say the cure `[LJ-1.520]` named is not available
in this tree, which is a finding about `src/L/Constructible.lagda.md` and not
about condensation.

**DO NOT PUT THE CLOSURE IN A FORMULA.** `[LJ-1.520]` measured that it is
circular there. If you find yourself writing a conjunct, stop and re-read its
`## WHAT THE GRADE COSTS`.

**DO NOT ASSUME `[LJ-1.519]`'s READING OF THE LIMIT.** It is running against
`devlin-II5.md` for a different statement. **Read the tree, not its brief.**

**DO NOT REBUILD THE GRADED FORMULA OR THE TRANSPORT.** `[LJ-1.520]` and
`[LJ-1.516]` delivered them.

**DO NOT POSTULATE.**

**REQUIRED REPORT SECTION `## WHAT THE GRADED FORMULA OWES AFTER THIS`.**
Re-walk `[LJ-1.520]`'s nine-row table with this row marked, and say whether any
row that it called "a hypothesis on `K`" is itself undelivered. **`[LJ-1.520]`
recorded those five as stated in `src/`; check that they are stated at the
frame this task uses, and say so at `file:line`.**

**REQUIRED REPORT SECTION `## THE UNCONSUMED CERTIFICATE`.** `[LJ-1.520]`
reports that a delivered `Σ₁` certificate exists at
`src/L/BoundedSubset.lagda.md:145-146` and is **unconsumed in both places it
occurs**. Say what consumes it after this task, or NOTHING. **Do not consume
it: that is the next task and not this one.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 160 lines in the probe, of which the obligation is
about 45. BASIS: `[LJ-1.520]` built the graded formula and a nine-row cost
table in a comparable file. Comparables are of SHAPE and nothing may be funded
against them.

## W3, THE WIDEST UNMEASURED TERM

It is the limit reading, because everything turns on it and `[LJ-1.520]` named
it without measuring it.

    limit-union : (K is a limit level) → (a member of K's definable powerset
                  appears at some earlier level)

**Write it FIRST, with the obligation omitted, and typecheck it ALONE.** If a
limit level does not decompose this way in this tree, the cure is unavailable
and the task stops at its cheapest point.

ESTIMATE for W3: about 25 lines and under 40 seconds. **Do not fund it against
`[LJ-1.520]`'s W3**, which came in at 43 lines and 2.43 s against my estimate
of 20 lines: **that brief's estimate was low and this one may be too.**

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS THE LAST HYPOTHESIS THE GRADED FORMULA NEEDS**, and leaves the
condensation leg with the transport, the grade and the closure all delivered.

**A NO-GO SAYS THE LIMIT CANNOT DISCHARGE IT IN THIS TREE**, which sends the
graded route back for a ruling and would be a finding about the constructible
hierarchy chapter rather than about condensation.

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
  changed_files_none = ["agents/tasks/LJ-1-522/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-522/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-522/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-522/Probe522.agda"]
  changed_files_none = ["agents/tasks/LJ-1-522/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-522/review-of-*.md"]

[[branch]]
id = "heap-wall-escalate"
priority = 30
action = "escalate"
head_slot = "coder_adversarial"

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 157.559)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 147.386)
- CANDIDATE archive/dev/JOURNAL.md  (score 140.515)
- CANDIDATE dev/ARCHIVE.md  (score 130.069)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 119.110)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 62.083)
- CANDIDATE dev/literature/digest.md  (score 49.577)
- CANDIDATE dev/literature/geology.md  (score 44.342)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 41.641)
- CANDIDATE dev/literature/terms-2026-08.md  (score 39.555)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
