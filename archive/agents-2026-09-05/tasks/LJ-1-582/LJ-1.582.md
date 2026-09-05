# LJ-1.582: clause (i) of the level-hood certificate, funded at last

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-582/Probe582.agda`:

    defines-level : <`Cert.DefinesLevel`, clause (i) of the level-hood
                     certificate>
      (`agents/tasks/LJ-1-578/Probe578.agda:234-240`)

**Clause (i) only.** Land nothing in `src/`.

**`[LJ-1.578]` STOPPED BECAUSE MY BRIEF FORBADE IT TO CONTINUE, AND IT WAS
RIGHT TO STOP.** Its one sentence: **"What is left is the level-hood
certificate, and the brief refuses to fund it."** It quoted my own clause back
at me (`agents/tasks/LJ-1-578/LJ-1.578.md:85`). **I am now funding it, one
clause at a time.**

**IT NAMED THE REMAINDER AS A TYPE AND NOT AS PROSE**, which is why this brief
can be written at all. The remainder is ONE object with THREE clauses
(`agents/tasks/LJ-1-578/Probe578.agda:525-534`):

| clause | at | what it says |
|---|---|---|
| **(i) `Cert.DefinesLevel`** | `Probe578.agda:234-240` | at the STAGE's inner world, a formula over hull codes has `Lset δ` as its only witness |
| (ii) `Cert.DefinesCover` | `Probe578.agda:244-251` | the covering ordinal of a hull member is defined the same way |
| (iii) `BChain.DefinesLevelAcross` | `Probe578.agda:503-510` | the same formula, read in the COLLAPSE, pins the true level there |

**AND IT PLACED THEM IN THE SOURCE.** The three clauses are **Devlin's own
chain, split at the tree's joints**, and clause (i) is Devlin's (b)
(`dev/literature/devlin-II5.md:99`).

**EVERYTHING ELSE ON ROW 3 IS PAID.** `[LJ-1.578]`'s own section says so, and
`[LJ-1.570]` measured 41 lines for the piece below it.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-582/Probe582.agda::defines-level"]

## SCOPE (write)
- agents/tasks/LJ-1-582/Probe582.agda
- agents/tasks/LJ-1-582/lj-1.582-report.md
- agents/tasks/LJ-1-582/review-of-defines-level.md
- agents/tasks/LJ-1-582/runs/

## PREMISES

1. `[LJ-1.578]` is a NO-GO and its critic upheld it. Basis: agents/tasks/LJ-1-578/review-of-cohyps-supplied.md:14
2. It names the remainder as one object with three clauses. Basis: agents/tasks/LJ-1-578/Probe578.agda:525
3. Clause (i) is stated at its probe. Basis: agents/tasks/LJ-1-578/Probe578.agda:234
4. Clause (i) is Devlin's (b). Basis: dev/literature/devlin-II5.md:99
5. `[LJ-1.570]` measured 41 lines for the piece below. Basis: agents/tasks/LJ-1-570/Probe570.agda:251
6. `CoHyps` is `Co`'s two parameters. Basis: src/L/BoundedSubset.lagda.md:1555
7. `𝒟ₒ-intro` is the one route into a stage. Basis: src/L/Constructible.lagda.md:301
8. `defSet` reads under the world's inner satisfaction. Basis: src/L/Definability.lagda.md:111
9. `AtStage` is the one external-to-inner bridge. Basis: src/L/Axioms/Separation.lagda.md:119
10. `[LJ-1.562]` measured both `AtStage` hypotheses payable at a sibling formula. Basis: agents/tasks/LJ-1-562/lj-1.562-report.md:1
11. `[LJ-1.121]` priced a level-hood certificate at 2.8k to 3.3k at an OLD tree. Basis: archive/dev/LJ-dispatch-index.md:198
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

A typed statement of all three clauses, everything on row 3 below them, and a
measurement that `AtStage`'s two hypotheses are payable at a sibling formula.
**No clause.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE FORMULA.** Clause (i) wants a formula
over hull codes whose only witness at the stage's inner world is `Lset δ`.
**Write that formula and say at `file:line` what it says, before you prove
anything about it.**

**`[LJ-1.562]` PAID BOTH `AtStage` HYPOTHESES AT A SIBLING FORMULA AND THAT MAY
NOT TRANSFER.** It measured the formula `[LJ-1.536]` needed, not this one.
**Re-measure Δ₀-ness and the constants here. A measured cure does not transfer
by analogy.**

**NOTHING MAY BE FUNDED AGAINST THE 2.8k TO 3.3k FIGURE.** `[LJ-1.121]` priced a
level-hood certificate at an old tree and did not build it. **That number is for
the whole certificate, and this brief funds ONE of its three clauses.** Report
what clause (i) actually cost.

**DO NOT BUILD CLAUSES (ii) OR (iii).** AD12 gives this brief one obligation,
and the point of splitting the certificate is that each clause is separately
checkable and separately priced.

**READ DEVLIN'S (b) BEFORE YOU WRITE THE FORMULA.**
`dev/literature/devlin-II5.md:99` is the source clause (i) came from. **Say in a
LITERATURE USED section what it gives you and what it leaves to the reader.**

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE FORMULA AND ITS UNIQUENESS`.** The formula, and
how you proved `Lset δ` is its ONLY witness.

**REQUIRED REPORT SECTION `## WHAT CLAUSE (i) COST`.** A measured line count and
time, and one sentence on whether clauses (ii) and (iii) look comparable. **Do
not price them; say only what your own numbers suggest.**

ESTIMATE: about 200 lines in the probe, of which the obligation is about 50.
BASIS: `[LJ-1.562]` and `[LJ-1.536]` worked the same machinery at a comparable
size. Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is uniqueness, not existence.

    -- "Lset δ is the ONLY witness", stated alone at the inner world, TYPE ONLY

**Write it FIRST and typecheck it ALONE.** A formula that has `Lset δ` among its
witnesses is easy; one that has it as the only witness is the clause. **If the
uniqueness will not even state, say so before spending the estimate.**
ESTIMATE: about 15 lines, under 2 minutes.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS ONE OF THE THREE CLAUSES OF A CERTIFICATE THAT HAS BLOCKED THIS
TREE SINCE `[LJ-1.7]`**, and gives the first real price for the other two.

**A NO-GO ON UNIQUENESS NAMES WHY THE CERTIFICATE HAS NEVER BEEN BUILT**, which
is worth as much: four hundred dispatches have named it and none has stated the
hard half.

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
  changed_files_none = ["agents/tasks/LJ-1-582/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-582/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-582/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-582/Probe582.agda"]
  changed_files_none = ["agents/tasks/LJ-1-582/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-582/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 204.372)
- CANDIDATE archive/dev/JOURNAL.md  (score 202.572)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 194.024)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 144.566)
- CANDIDATE archive/dev/DD-archived.md  (score 144.248)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 64.886)
- CANDIDATE dev/literature/digest.md  (score 58.286)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 49.867)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 42.789)
- CANDIDATE dev/literature/terms-2026-08.md  (score 36.269)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
