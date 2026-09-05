# LJ-1.595: clause (ii) of the level-hood certificate

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-595/Probe595.agda`:

    defines-cover : <`Cert.DefinesCover`, clause (ii) of the level-hood
                     certificate>
      (`agents/tasks/LJ-1-578/Probe578.agda:244-251`)

**Clause (ii) only.** Land nothing in `src/`.

**`[LJ-1.578]` NAMED ROW 3'S REMAINDER AS A TYPE AND NOT AS PROSE**, which is
why this brief can be written. The remainder is ONE object with THREE clauses
(`agents/tasks/LJ-1-578/Probe578.agda:525-534`):

| clause | at | what it says |
|---|---|---|
| (i) `Cert.DefinesLevel` | `Probe578.agda:234-240` | **`[LJ-1.582]` has it** |
| **(ii) `Cert.DefinesCover`** | `Probe578.agda:244-251` | the covering ordinal of a hull member is defined the same way |
| (iii) `BChain.DefinesLevelAcross` | `Probe578.agda:503-510` | the same formula, read in the COLLAPSE, pins the true level there |

**THE THREE ARE DEVLIN'S OWN CHAIN, SPLIT AT THE TREE'S JOINTS**, and clause (i)
is Devlin's (b) (`dev/literature/devlin-II5.md:99`).

**CLAUSE (ii) IS THE SIBLING OF CLAUSE (i) AND `[LJ-1.578]` SAYS SO: "the
covering ordinal... is defined THE SAME WAY."** That is a resemblance, and this
campaign has been wrong about resemblances twice this week. **Check it before
you rely on it.**

**THIS BRIEF DOES NOT ASSUME `[LJ-1.582]` LANDED.** If its work is in the tree,
reuse it and say what you took; if it is not, build clause (ii) alone. **Do not
stop on its account.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-595/Probe595.agda::defines-cover"]

## SCOPE (write)
- agents/tasks/LJ-1-595/Probe595.agda
- agents/tasks/LJ-1-595/lj-1.595-report.md
- agents/tasks/LJ-1-595/review-of-defines-cover.md
- agents/tasks/LJ-1-595/runs/

## PREMISES

1. `[LJ-1.578]` names the remainder as three clauses. Basis: agents/tasks/LJ-1-578/Probe578.agda:525
2. Clause (ii) is stated at its probe. Basis: agents/tasks/LJ-1-578/Probe578.agda:244
3. Clause (i) is stated at its probe. Basis: agents/tasks/LJ-1-578/Probe578.agda:234
4. Clause (i) is Devlin's (b). Basis: dev/literature/devlin-II5.md:99
5. `CoHyps` is `Co`'s two parameters. Basis: src/L/BoundedSubset.lagda.md:1555
6. `[LJ-1.570]` measured 41 lines for the piece below. Basis: agents/tasks/LJ-1-570/Probe570.agda:251
7. `𝒟ₒ-intro` is the one route into a stage. Basis: src/L/Constructible.lagda.md:301
8. `AtStage` is the one external-to-inner bridge. Basis: src/L/Axioms/Separation.lagda.md:119
9. `[LJ-1.562]` measured both `AtStage` hypotheses payable at a sibling formula. Basis: agents/tasks/LJ-1-562/lj-1.562-report.md:1
10. `[LJ-1.585]` refuted a resemblance of mine by measurement. Basis: agents/tasks/LJ-1-585/Probe585.agda:163
11. `[LJ-1.580]` refuted another. Basis: agents/tasks/LJ-1-580/review-of-beta-into-alpha-coded.md:40
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

A typed statement of all three clauses and everything on row 3 below them.

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE RESEMBLANCE.** `[LJ-1.578]` says the
covering ordinal is defined "the same way" as the level. **Read both statements
and say at `file:line` what differs**: the binder, the arity, the side
conditions. **If nothing differs but a name, say so and the clause is short. If
something does, that difference IS this task.**

**`[LJ-1.562]` PAID BOTH `AtStage` HYPOTHESES AT A DIFFERENT FORMULA.**
**Re-measure Δ₀-ness and the constants here.** A measured cure does not transfer
by analogy.

**REUSE `[LJ-1.582]`'S WORK IF IT IS IN THE TREE.** Say which lines you took. If
its directory is absent, note that and build alone. **Do not cite a file you did
not open**: a brief of mine cited `agents/tasks/LJ-1-572/LJ-1.572.md` last hour
and that directory does not exist.

**DO NOT BUILD CLAUSES (i) OR (iii).** AD12 gives this brief one obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## HOW CLAUSE (ii) DIFFERS FROM (i)`.** At
`file:line`, with the verdict same or different.

**REQUIRED REPORT SECTION `## WHAT CLAUSE (ii) COST`.** A measured line count and
time, and one sentence on whether clause (iii) looks comparable. **Do not price
it; say only what your own numbers suggest.**

ESTIMATE: about 190 lines in the probe, of which the obligation is about 45.
BASIS: `[LJ-1.562]` and `[LJ-1.536]` worked the same machinery. Comparables are
of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the covering ordinal itself.

    -- the covering ordinal of a hull member, at the stage's inner world,
    -- TYPE ONLY

**Write it FIRST and typecheck it ALONE.** If it will not state at the inner
world, the clause is about a different object than clause (i) and you say so
before spending the estimate. ESTIMATE: about 15 lines, under 2 minutes.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS THE SECOND OF THREE CLAUSES**, and with `[LJ-1.582]` row 3 would want
only clause (iii).

**A NO-GO SHOWING (ii) IS NOT (i)'S SIBLING RE-PRICES THE CERTIFICATE**, which
the campaign has been treating as one object split three ways.

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
  changed_files_none = ["agents/tasks/LJ-1-595/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-595/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-595/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-595/Probe595.agda"]
  changed_files_none = ["agents/tasks/LJ-1-595/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-595/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 193.947)
- CANDIDATE archive/dev/JOURNAL.md  (score 189.815)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 169.821)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 138.162)
- CANDIDATE archive/dev/DD-archived.md  (score 133.805)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 65.729)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 47.665)
- CANDIDATE dev/literature/digest.md  (score 42.940)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 41.553)
- CANDIDATE dev/literature/primary-sources.md  (score 35.219)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
