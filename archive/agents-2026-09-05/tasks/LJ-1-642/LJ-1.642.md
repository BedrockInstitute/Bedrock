# LJ-1.642: clause (i) at the ordinal index, which is my ruling

## HEAD
head_slot: coder
machine: exclusive
agda_tier: heavy

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-642/Probe642.agda`:

    clause-i-at-ord : <clause (i) of the level-hood certificate, RESTATED so its
                       index carries `IsOrd (fst (T.val c))`, discharged from
                       `[LJ-1.598]`'s `graph-gives-level` plus its `Det` and
                       `Wit` suppliers>

Land nothing in `src/`. **Do not build `PreimageOrd`. The restatement is the
ruling and it removes that supplier.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-642/Probe642.agda::clause-i-at-ord"]

## MEASURED TODAY

- dependents: L.BoundedSubset => 3
- supply: PreimageOrd => 0

## SCOPE (write)
- agents/tasks/LJ-1-642/Probe642.agda
- agents/tasks/LJ-1-642/lj-1.642-report.md
- agents/tasks/LJ-1-642/review-of-clause-i-at-ord.md
- agents/tasks/LJ-1-642/runs/

## PREMISES

1. `[LJ-1.598]` asked the mathematician to decide the index before any supplier
   is funded, and named the two options. Basis:
   agents/tasks/LJ-1-598/lj-1.598-report.md:336
2. **MY RULING: RESTATE AT THE ORDINAL INDEX.** `graph-gives-level` already
   carries `IsOrd (fst (T.val c))` in its own signature and is green, so the
   restatement matches a term that exists rather than one that must be funded.
   Basis: agents/tasks/LJ-1-598/Probe598.agda:220
3. The alternative costs more than it buys: `[LJ-1.598]` measured that the graph
   gives a NON-level at non-ordinal indices and that no reading repair closes it.
   Basis: agents/tasks/LJ-1-598/lj-1.598-report.md:330
4. **THE FRAME, NOT THE TERM, IS THE RESOURCE RISK.** `[LJ-1.598]` measured that
   `[LJ-1.578]`'s file walls under the WIDE cap with warm dependencies, and that
   `[LJ-1.582]`'s wall is partly explained by it: any frame importing the
   certificate inherits a floor above the wide cap. This brief is HEAVY for that
   reason. Take your clause by RESTATEMENT as `[LJ-1.598]` did, not by importing
   the certificate. Basis: agents/tasks/LJ-1-598/lj-1.598-report.md:341

5. **A NAMED FAILURE MODE FROM THE ARCHIVE, AND IT IS THE ONE TO WATCH.**
   `[LJ-1.34]` attacked a certificate before and closed NO-GO for a specific
   reason: "the Delta-0 certificate does NOT close: the delivered leaves carry
   unbounded quantifiers". If your `Det` or `Wit` supplier delivers a leaf with
   an unbounded quantifier, you have reproduced that, and saying so early is
   cheaper than finding it at the join. Basis:
   archive/dev/LJ-dispatch-index.md:52
6. **THE LITERATURE HAS AN ERRATA INVENTORY FOR EXACTLY THIS.** `digest.md`
   names Mathias's WS section 10 as the inventory of FALSE Delta-0 claims for
   syntax. Read it before you certify a leaf as bounded. Basis:
   dev/literature/digest.md:69

## WHAT IS DELIVERED ALREADY

`[LJ-1.598]`'s sixteen names all land and are metered green. What it could not
close is `Det` and `Wit` at any `ψ`, `CodedLevels`, and `PreimageOrd`. Premise 2
removes the last of those four; the first three remain yours.

## THE REASONING

Three clauses make the certificate and all three are attempted and open. This
one is the only one whose blocker was a QUESTION rather than a construction, and
the question is now answered. Whether the remaining three suppliers fall out at
the ordinal index is what this measures.

## W3, THE WIDEST UNMEASURED TERM

`Det` and `Wit` at a general `ψ`. Estimate 150 to 300 lines, basis:
`[LJ-1.598]`'s own probe carries sixteen names and reached the residue without
them (agents/tasks/LJ-1-598/lj-1.598-report.md:1). If the frame walls at HEAVY,
that is a finding and you report the floor before you report the term.

## WHAT GO AND NO-GO EACH EARN

**GO** closes clause (i) at the index I ruled. **NO-GO** earns which of `Det`,
`Wit` or `CodedLevels` does not fall out, which prices the certificate's
remainder exactly.
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
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-642/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-642/review-of-LJ-*-*.md"]

[[branch]]
id = "accept-failed"
priority = 14
action = "escalate"
head_slot = "coder_adversarial"

  [branch.when]
  exit_code = 1
  obligations_delta_max = -1
  changed_files_none = ["agents/tasks/LJ-1-642/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-642/Probe642.agda"]
  changed_files_none = ["agents/tasks/LJ-1-642/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-642/review-of-*.md"]

[[branch]]
# PARK, NOT ESCALATE. A heap wall is a resource fact and no critic can
# adjudicate it (MEASURED on LJ-1.534).
id = "heap-wall-park"
priority = 30
action = "park_and_split"

  [branch.when]
  heap_wall = true

[[branch]]
# CLOSES BACKLOG ITEM 30, MEASURED ON LJ-1.630 2026-08-25. A REAL failed
# landing carries a named Agda error and NEITHER companion file: the coder
# edits the target directly and leaves ad-hoc runs/*.out. Both rows above
# demand a companion (Probe or review-of), so that return matched NOTHING
# and the task parked with its evidence invisible. This row is the catch-all
# and it sits BELOW heap-wall-park, so a wall still parks.
id = "no-go-bare"
priority = 40
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 123.838)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 116.340)
- CANDIDATE archive/dev/JOURNAL.md  (score 111.339)
- CANDIDATE dev/ARCHIVE.md  (score 105.491)
- CANDIDATE archive/dev/DD-archived.md  (score 97.979)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 35.486)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 31.341)
- CANDIDATE dev/literature/digest.md  (score 31.297)
- CANDIDATE dev/literature/terms-2026-08.md  (score 22.723)
- CANDIDATE dev/literature/geology.md  (score 20.075)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
