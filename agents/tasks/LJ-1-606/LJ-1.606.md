# LJ-1.606: the crossing from an inner world to the ambient tower, row 3's one root

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-606/Probe606.agda`:

    inner-to-ambient : <the set-level commute clause (iii) needs, stated and
                        inhabited, or the term naming precisely what it lacks>

Land nothing in `src/`. **This is NOT a formula.**

**`[LJ-1.602]` IS A NO-GO AND IT FOUND THE ROOT OF ALL THREE FAILURES.** Row 3's
level-hood certificate has three clauses and all three have now failed:
`[LJ-1.582]` heap-walled on (i), `[LJ-1.598]` and `[LJ-1.595]` are NO-GO on (i)
and (ii), and `[LJ-1.602]` is NO-GO on (iii). **Its required section answers why:**

> "The three stops **share one root, the absence of any crossing from an inner
> world to the ambient tower**, but they priced three different objects... clause
> (iii) **NO formula at all but the set-level commute** (`Probe602.agda`, section
> 3). **Clause (iii) is the strongest of the three in the certificate's own
> currency.**"

**SO ROW 3 IS ONE PROBLEM WORN THREE WAYS, AND (iii) IS ITS STRONGEST FORM.**
That is why this brief takes the crossing itself and not a fourth clause
attempt.

**AND IT IS A DIFFERENT KIND OF OBJECT FROM EVERYTHING ELSE ON THE BILL.** Every
other open piece wants a `Formula`. **This one wants a set-level commute.** Do
not import the formula machinery and do not reach for `hasSeparationL`.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-606/Probe606.agda::inner-to-ambient"]

## SCOPE (write)
- agents/tasks/LJ-1-606/Probe606.agda
- agents/tasks/LJ-1-606/lj-1.606-report.md
- agents/tasks/LJ-1-606/review-of-inner-to-ambient.md
- agents/tasks/LJ-1-606/runs/

## PREMISES

1. `[LJ-1.602]` is a NO-GO and names the shared root. Basis: agents/tasks/LJ-1-602/lj-1.602-report.md:1
2. It states clause (iii) wants no formula but a set-level commute. Basis: agents/tasks/LJ-1-602/Probe602.agda:1
3. Clause (iii) is stated at `[LJ-1.578]`'s probe. Basis: agents/tasks/LJ-1-578/Probe578.agda:503
4. `[LJ-1.598]` is a NO-GO on clause (i). Basis: agents/tasks/LJ-1-598/lj-1.598-report.md:1
5. `[LJ-1.595]` is a NO-GO on clause (ii). Basis: agents/tasks/LJ-1-595/review-of-defines-cover.md:1
6. `[LJ-1.578]` names the remainder as three clauses. Basis: agents/tasks/LJ-1-578/Probe578.agda:525
7. `CoHyps` is `Co`'s two parameters. Basis: src/L/BoundedSubset.lagda.md:1555
8. `𝒟ₒ-intro` is the one route into a stage. Basis: src/L/Constructible.lagda.md:301
9. `defSet` reads under the world's inner satisfaction. Basis: src/L/Definability.lagda.md:111
10. `[LJ-1.570]` measured 41 lines for the piece below row 3. Basis: agents/tasks/LJ-1-570/Probe570.agda:251
11. A stop is a deliverable. Basis: AGENTS.md:43
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

Three measured stops on one root, and `[LJ-1.602]`'s section 3 stating the
commute. **No crossing.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS `[LJ-1.602]`'s SECTION 3.** Read it and state
the commute in your own probe at `file:line`. **If its statement is not precise
enough to restate, say so: that is a defect in the stop and worth knowing.**

**DO NOT WRITE A FORMULA.** `[LJ-1.602]` measured that clause (iii) wants none.
**If you find yourself reaching for `hasSeparationL` or `𝒟ₒ-intro`, stop and say
why**, because that would mean the stop's own characterisation is wrong.

**THE CROSSING IS THE ROOT OF THREE FAILURES, SO A REFUTATION IS AS VALUABLE AS
A BUILD.** If no crossing exists, say so with the evidence: that would price row
3 as a single wall rather than three, and the mathematician would take it to the
owner instead of funding a fourth clause.

**DO NOT ATTEMPT CLAUSES (i) OR (ii).** AD12 gives this brief one obligation.
Their stops are in the tree and worth reading, but they are not your target.

**CAP EVERY TYPECHECK ON A WALL CLOCK YOU SET AND REPORT THE CAP.** `[LJ-1.582]`
heap-walled on this family, so **report peak RSS as well as seconds**: on row 3
the heap has been the risk and not the deadline.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE COMMUTE, STATED`.** In full, at `file:line`,
with whether you inhabited it.

**REQUIRED REPORT SECTION `## DOES IT PAY ALL THREE CLAUSES`.** `[LJ-1.602]` calls
(iii) the strongest in the certificate's own currency. **Say whether the crossing
pays (i) and (ii) too, and do not read a discharge into anything you did not
inhabit.**

ESTIMATE: about 190 lines in the probe, of which the obligation is about 45.
BASIS: `[LJ-1.602]` reached section 3 at a comparable size. Comparables are of
SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the commute itself.

    -- LJ-1.602's section 3 commute, restated alone, TYPE ONLY, capped

**Write it FIRST, typecheck it ALONE, cap it, and report peak RSS.** ESTIMATE:
about 15 lines, cap at two minutes.

## WHAT GO AND NO-GO EACH EARN

**A GO MAY PAY ALL THREE CLAUSES AT ONCE**, because its predecessor calls (iii)
the strongest of them.

**A NO-GO PRICES ROW 3 AS ONE WALL RATHER THAN THREE**, which is a ruling the
owner must hear, and it would be the fourth measured failure on that row.

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
  changed_files_none = ["agents/tasks/LJ-1-606/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-606/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-606/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-606/Probe606.agda"]
  changed_files_none = ["agents/tasks/LJ-1-606/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-606/review-of-*.md"]

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
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 153.141)
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 149.794)
- CANDIDATE archive/dev/JOURNAL.md  (score 142.269)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 125.096)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 123.380)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 61.640)
- CANDIDATE dev/literature/digest.md  (score 42.214)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 41.219)
- CANDIDATE dev/literature/terms-2026-08.md  (score 32.018)
- CANDIDATE dev/literature/geology.md  (score 28.103)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
