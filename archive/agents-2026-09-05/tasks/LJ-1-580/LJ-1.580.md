# LJ-1.580: give β↪α a code, which is the cure row 1 turned out to need

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-580/Probe580.agda`:

    beta-into-alpha-coded : <`gap-is-a-code`, the interface
                             `[LJ-1.577]` wrote>
      (`agents/tasks/LJ-1-577/Probe577.agda:368`)

a CODE for the injection `β↪α` (`src/L/BoundedSubset.lagda.md:1578`). Land
nothing in `src/`.

**`[LJ-1.577]` IS A NO-GO, UPHELD, AND ITS VERDICT IS THE ONE THE CAMPAIGN WAS
WAITING FOR.** In its own words: **"IT IS A PORT DEFECT, AND THE DEFECT IS NOT
IN THE HYPOTHESIS. IT IS IN THE CONSTRUCTION."**

**THE LITERATURE STEP CAME BACK CLEAN.** Exactly one of Devlin 5.5's seven
steps reads "κ is a cardinal", and under `Assume V = L` the three size witnesses
that step consumes are all elements of L, **so the refutation may be taken at
L's own injections.** The mathematician's reading of the proof was right.

**BUT THE TREE DOES NOT INHERIT IT, AND THE REASON IS ONE TERM.** `β↪α`
(`src/L/BoundedSubset.lagda.md:1578`) is the inverse collapse after a code
selection, composed with the stage-cardinality bound, **and it carries no
`InjCode`.** Re-ascribing `cardκ` alone does not remove the demand; it converts
it into a statement about ONE injection, and `internal-plus-one-code` and
`residue-gives-569` measure that the converted demand is no cheaper.

**SO THE CURE IS A CONSTRUCTION AND NOT A RE-READING: GIVE `β↪α` A CODE.**

**THIS IS NOT `[LJ-1.533]`'S WALL AND `[LJ-1.577]` SAYS SO EXPLICITLY.** It is
**"Not a code for every ambient injection"**: `β↪α` is the composite of a
stage-cardinality bound and a code selection over the hull's term algebra, and
**both legs are built from L-data.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-580/Probe580.agda::beta-into-alpha-coded"]

## SCOPE (write)
- agents/tasks/LJ-1-580/Probe580.agda
- agents/tasks/LJ-1-580/lj-1.580-report.md
- agents/tasks/LJ-1-580/review-of-beta-into-alpha-coded.md
- agents/tasks/LJ-1-580/runs/

## PREMISES

1. `[LJ-1.577]` is a NO-GO and its critic upheld it. Basis: agents/tasks/LJ-1-577/review-of-bounded-subset-internal.md:1
2. Its verdict is a port defect in the construction. Basis: agents/tasks/LJ-1-577/lj-1.577-report.md:60
3. It wrote the interface `gap-is-a-code`. Basis: agents/tasks/LJ-1-577/Probe577.agda:368
4. It names `β↪α` as the term carrying no code. Basis: src/L/BoundedSubset.lagda.md:1578
5. It states both legs are built from L-data. Basis: agents/tasks/LJ-1-577/review-of-bounded-subset-internal.md:77
6. Devlin 5.5 opens `Assume V = L`. Basis: dev/literature/devlin-II5.md:147
7. `InjCode` has four conjuncts. Basis: src/L/Cardinal.lagda.md:223
8. `InjCode` is a proposition at today's tree. Basis: agents/tasks/LJ-1-576/Probe576.agda:77
9. `[LJ-1.566]` assembled an `InjCode` from four separate conjuncts. Basis: agents/tasks/LJ-1-566/lj-1.566-report.md:1
10. `[LJ-1.533]` refuted a code for an ARBITRARY ambient injection. Basis: agents/tasks/LJ-1-533/lj-1.533-report.md:1
11. `[LJ-1.568]` proved `Def` necessary and sufficient for the sibling rows. Basis: agents/tasks/LJ-1-568/Probe568.agda:368
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

A written interface, a clean literature verdict, and a proof that `InjCode` is a
proposition here. **No code for `β↪α`.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE TWO LEGS.** `[LJ-1.577]` says `β↪α` is a
composite: a stage-cardinality bound, and a code selection over the hull's term
algebra. **Name both at `file:line` and say for each whether it already carries
a code or must be given one.** If one of them is not built from L-data after
all, that contradicts `[LJ-1.577]` and you must say so.

**BUILD THE INTERFACE `[LJ-1.577]` WROTE, NOT A NEIGHBOUR OF IT.**
`gap-is-a-code` (`Probe577.agda:368`) is the exact type. **Import it rather than
restating it**, so it cannot drift.

**DO NOT ATTEMPT A CODE FOR AN ARBITRARY AMBIENT INJECTION.** `[LJ-1.533]`
refuted that and three later tasks confirmed the wall at their own sites. **This
task is the opposite case and its predecessor said so in those words.**

**`[LJ-1.566]` ASSEMBLED AN `InjCode` FROM FOUR CONJUNCTS AND ITS METHOD MAY
TRANSFER, OR MAY NOT.** Read it, and **re-measure rather than assume**: a
measured cure does not transfer by analogy.

**DO NOT ATTEMPT ROWS 2 TO 5.** AD12 gives this brief one obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE TWO LEGS`.** Each at `file:line`, with what it
cost to code, or the reason it could not be.

**REQUIRED REPORT SECTION `## WHAT THIS DOES TO ROW 1`.** Say whether row 1 is
now payable and what remains. **Do not read a discharge into anything you did
not inhabit**, which four predecessors have held to this week.

ESTIMATE: about 220 lines in the probe, of which the obligation is about 55.
BASIS: `[LJ-1.566]` assembled a comparable code. **The estimate is uncertain
because nobody has coded a composite injection before.** Comparables are of
SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the code selection leg, which may already carry what you need.

    -- the code selection inside β↪α, re-ascribed alone, TYPE ONLY

**Write it FIRST and typecheck it ALONE.** If that leg already produces a code,
half the obligation is delivered and the estimate is too high: say so.
ESTIMATE: about 15 lines, under 2 minutes.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS ROW 1, THE ONLY ROW THAT DEMANDS ANYTHING OF THE AMBIENT UNIVERSE**,
and it would mean `L ⊨ GCH` is reachable here without assuming V = L.

**A NO-GO THAT SHOWS ONE LEG CANNOT BE CODED IS A RULING**, and the owner will
hear it in the same hour it lands.

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
  changed_files_none = ["agents/tasks/LJ-1-580/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-580/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-580/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-580/Probe580.agda"]
  changed_files_none = ["agents/tasks/LJ-1-580/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-580/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 229.591)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 209.427)
- CANDIDATE archive/dev/JOURNAL.md  (score 195.923)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 157.138)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 156.729)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 71.655)
- CANDIDATE dev/literature/devlin-II5.md  (score 64.547)
- CANDIDATE dev/literature/digest.md  (score 56.800)
- CANDIDATE dev/literature/terms-2026-08.md  (score 40.174)
- CANDIDATE dev/literature/geology.md  (score 36.591)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
