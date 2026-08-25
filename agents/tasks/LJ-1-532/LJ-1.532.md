# LJ-1.532: row six, whose one membership is the approximation itself

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-532/Probe532.agda`:

    approx-in-K : (g : S) → ⟨ γ ⊨ ApproxAt-at-g ⟩
                → ⟨ fst g ∈ fst (lookup K γ) ⟩

**the approximation function itself lies in `K`**, which is the one membership
row six of the chain wants. Land nothing in `src/`.

**`[LJ-1.530]` IS GO AND THE CHAIN IS DOWN TO TWO ROWS.** It built `wK`, `dK`,
`zK`, `entryK` and `domK`, and re-walked the whole table
(`agents/tasks/LJ-1-530/lj-1.530-report.md`, `## WHAT THE CHAIN OWES AFTER
THIS`): **rows one to five are BUILT.** Rows six and seven are not examined by
anyone.

**AND IT CORRECTED MY COUNT. THE TABLE HAS SEVEN ROWS, NOT SIX.** I wrote "six
rows" into two briefs. `[LJ-1.525]`'s table
(`agents/tasks/LJ-1-525/lj-1.525-report.md:194-202`) carries a seventh,
`LevelHood.levelHoodB` against level-hood of the carrier
(`src/L/BoundedSubset.lagda.md:108`). **Row seven is not this task and it is
not forgotten.**

**ROW SIX IS ONE BOUNDED EXISTENTIAL.**
`graphBndAt = ∃̇∈ (var K) (A.approxBndAt ∧̇ S.stepBndAt)`
(`src/L/Condensation.lagda.md:2492-2493`). Rows three and five already transfer
its two conjuncts. **What is left is the witness: the bound says the
approximation is IN `K`, and the machine's `LsetGraphAt` does not.**

**THE ARCHIVE PRICES IT AND SAYS NOBODY RAN IT.**
`agents/tasks/LJ-1-228/lj-1.228-report.md:128-130`: "`[LJ-1.123]` section 3
named it: the two-way decode of the bounded level-hood `graphBndAt`, GO at 150
to 250 probe lines. **Nobody ran it.**" **That is a price for the two-way
decode, not for this one membership. Do not fund yourself against it.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-532/Probe532.agda::approx-in-K"]

## SCOPE (write)
- agents/tasks/LJ-1-532/Probe532.agda
- agents/tasks/LJ-1-532/lj-1.532-report.md
- agents/tasks/LJ-1-532/review-of-approx-in-K.md
- agents/tasks/LJ-1-532/runs/

## PREMISES

1. `[LJ-1.530]` is GO and rows one to five are built. Basis: agents/tasks/LJ-1-530/lj-1.530-report.md:1
2. It built `dK`. Basis: agents/tasks/LJ-1-530/Probe530.agda:131
3. It built `wK`. Basis: agents/tasks/LJ-1-530/Probe530.agda:243
4. It built `zK`. Basis: agents/tasks/LJ-1-530/Probe530.agda:169
5. Row six's membership is named as a type. Basis: agents/tasks/LJ-1-527/lj-1.527-report.md:234
6. `graphBndAt` is the bounded existential. Basis: src/L/Condensation.lagda.md:2492
7. `[LJ-1.228]` records the archive price and that nobody ran it. Basis: agents/tasks/LJ-1-228/lj-1.228-report.md:128
8. Row seven exists and is unexamined. Basis: src/L/BoundedSubset.lagda.md:108
9. `[LJ-1.522]` closed `K` under definable subsets at a limit. Basis: agents/tasks/LJ-1-522/Probe522.agda:356
10. `[LJ-1.525]` built row one. Basis: agents/tasks/LJ-1-525/Probe525.agda:150
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THIS MORNING THE CONDENSATION LEG HAD A WALL DESCRIBED IN SENTENCES. IT NOW
HAS A SEVEN ROW TABLE WITH FIVE ROWS BUILT.** `[LJ-1.525]`, `[LJ-1.527]` and
`[LJ-1.530]` did that in three dispatches, twice by finding work that already
existed rather than building it.

## THE REASONING

**D-10, BEFORE ANY AGDA.** The approximation `g` is a FUNCTION, recorded as a
set of pairs. **Say at `file:line` what `K` is at this frame and what it would
take for a set of pairs to be one of its members.** `[LJ-1.522]` closed `K`
under definable subsets of its members and `[LJ-1.530]` put `𝒟ₒ w` in `K`;
**say whether `g` is reachable from either.** If it is not, name what `g` is
built from and STOP: an approximation stated nowhere to be in `K` is the same
shape of finding as `[LJ-1.494]`'s, at a different carrier, and saying so is
worth more than a term.

**THIS IS `K`, NOT A STAGE.** `[LJ-1.494]` and `[LJ-1.517]` measured that the
tree does not bound `hierL δ` by a STAGE. **That is a different question from
membership in `K` and its answer does not transfer.** Do not cite it as
settling this and do not assume it does not.

**DO NOT REBUILD ROWS ONE TO FIVE.** `[LJ-1.530]` lists each with its
`file:line`. Cite them.

**DO NOT ATTEMPT ROW SEVEN.** AD12 gives this brief one obligation, and row
seven is `LevelHood.levelHoodB`, a different statement at a different site.

**DO NOT SPEND THE `Σ₁` CERTIFICATES.** The chain is not complete.

**DO NOT POSTULATE.**

**REQUIRED REPORT SECTION `## ROW SEVEN, LOOKED AT ONCE`.** No dispatch has
examined `LevelHood.levelHoodB` (`src/L/BoundedSubset.lagda.md:108`). **Say in
three sentences what it asks and whether any of rows one to six bears on it.
Do not build it.** The chain cannot be closed without knowing.

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 170 lines in the probe, of which the obligation is
about 45. BASIS: `[LJ-1.530]` built five memberships at this frame in a
comparable file. Comparables are of SHAPE and nothing may be funded against
them, and the archive's 150 to 250 is for a different statement.

## W3, THE WIDEST UNMEASURED TERM

It is what the approximation is built from, because membership in `K` is
decided by that and by nothing else.

    -- g, as a set, at file:line, with whatever puts it in K or fails to

**Do this FIRST, before any term, and write it into the report as you go.** If
`g` comes from a construction the tree never places in `K`, the row is not
payable at this frame and the task stops at its cheapest point.

ESTIMATE for W3: about 20 lines of reading and under 30 seconds of Agda. **Do
not fund it against `[LJ-1.530]`'s numbers**: that closed memberships of
members, and this asks about a function.

## WHAT GO AND NO-GO EACH EARN

**A GO LEAVES THE CHAIN WITH ROW SEVEN ALONE**, and the two `Σ₁` certificates
unconsumed since `[LJ-1.228]` come within one row of a consumer.

**A NO-GO NAMES WHAT THE APPROXIMATION IS MISSING**, which is the same shape of
finding `[LJ-1.494]` produced at a stage, now at `K`, and it would tell the
mathematician whether the two carriers share one obstruction or two.

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
  changed_files_none = ["agents/tasks/LJ-1-532/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-532/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-532/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-532/Probe532.agda"]
  changed_files_none = ["agents/tasks/LJ-1-532/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-532/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 201.090)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 171.344)
- CANDIDATE archive/dev/JOURNAL.md  (score 165.021)
- CANDIDATE dev/ARCHIVE.md  (score 141.077)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 134.174)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 68.199)
- CANDIDATE dev/literature/digest.md  (score 39.409)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 38.654)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 36.911)
- CANDIDATE dev/literature/terms-2026-08.md  (score 33.996)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
