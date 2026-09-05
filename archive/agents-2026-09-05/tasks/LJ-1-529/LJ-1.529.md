# LJ-1.529: the range clause, which needs only the re-basing

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-529/Probe529.agda`:

    range-clause :
        (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → ⟨ fst y ∈ fst b ⟩

**the second of the four `InjCode` conjuncts, over the carve re-based on
`swo-rank′`.** Land nothing in `src/`.

**`[LJ-1.524]` IS GO AND IT TRIAGED THE REMAINING THREE.** It closed `svAt`,
then gave a verdict on each of the others, each checked at its `file:line`:

- **the range clause: NEEDS ONLY THE `swo-rank′` RE-BASING.** `Carve.val`
  (`agents/tasks/LJ-1-524/Probe524.agda:225-228`) already gives what it wants.
- **`injAt`: needs the re-basing AND one lemma.**
- **`domAt`: half the re-basing, half a NEW THEOREM.**

**SO THIS IS THE CHEAPEST OF THE THREE AND IT IS FIRST.**

**THE RE-BASING IS A KNOWN, MEASURED COST.** `[LJ-1.521]` measured that
`[LJ-1.490]`'s `Bound`, `C` and `bnd` (`agents/tasks/LJ-1-490/Probe490.agda:211-232`)
are built on `swo-rank`, the rank `[LJ-1.497]` REFUTED, and must be re-based on
`swo-rank′`: **"a re-spelling of eleven lines and not a new proof, but it is not
free and nobody has done it."** Do it here; it binds three of the four
conjuncts and this is the first task that needs it.

**`Q` IS INSTANTIATED, NOT HYPOTHESISED.** That is the mathematician's ruling
and `[LJ-1.524]` confirmed it against a real consumer. Take `Q` at
`ord-set-witness a oa .fst` (`agents/tasks/LJ-1-521/Probe521.agda:1162-1164`).

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-529/Probe529.agda::range-clause"]

## SCOPE (write)
- agents/tasks/LJ-1-529/Probe529.agda
- agents/tasks/LJ-1-529/lj-1.529-report.md
- agents/tasks/LJ-1-529/review-of-range-clause.md
- agents/tasks/LJ-1-529/runs/

## PREMISES

1. `[LJ-1.524]` is GO and closed `svAt`. Basis: agents/tasks/LJ-1-524/lj-1.524-report.md:1
2. It reports the range clause needs only the re-basing. Basis: agents/tasks/LJ-1-524/lj-1.524-report.md:1
3. `Carve.val` already gives what the clause wants. Basis: agents/tasks/LJ-1-524/Probe524.agda:225
4. The clause's type is in the cardinal chapter. Basis: src/L/Cardinal.lagda.md:228
5. `[LJ-1.521]` measured the re-basing at eleven lines. Basis: agents/tasks/LJ-1-521/lj-1.521-report.md:1
6. `Bound`, `C` and `bnd` are built on the refuted rank. Basis: agents/tasks/LJ-1-490/Probe490.agda:211
7. `swo-rank′` is the replacement. Basis: agents/tasks/LJ-1-515/Probe515.agda:112
8. `swo-rank′-∅` is proved. Basis: agents/tasks/LJ-1-515/Probe515.agda:218
9. `rankFo-adequate′` is built. Basis: agents/tasks/LJ-1-521/Probe521.agda:1006
10. The `Q` witness is delivered. Basis: agents/tasks/LJ-1-521/Probe521.agda:1162
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**ONE OF THE FOUR CONJUNCTS IS CLOSED AND THE OTHER THREE ARE TRIAGED.**
`[LJ-1.524]` did both. **This is the second, and after it only `injAt`'s one
lemma and `domAt`'s new theorem remain.**

## THE REASONING

**D-10, BEFORE ANY AGDA.** `[LJ-1.521]` calls the re-basing eleven lines.
**Count them yourself at `agents/tasks/LJ-1-490/Probe490.agda:211-232` and say
whether the number holds.** If `Bound`, `C` or `bnd` needs more than a
substitution of `swo-rank′` for `swo-rank`, name what and STOP: the three
conjuncts that ride on this re-basing would then all be mispriced.

**DO THE RE-BASING, DO NOT WORK AROUND IT.** The refuted rank must not appear
in your file. If you find yourself keeping `swo-rank` to make something close,
that is the finding.

**DO NOT BUILD `injAt` OR `domAt`.** AD12 gives this brief one obligation.
`[LJ-1.524]` measured that `domAt-in` (`src/L/Coding/Model.lagda.md:294-296`)
asks for the CONVERSE of `rankFo-adequate′` and that nothing in the tree
supplies it. **That converse is the coding leg's remaining wall and it is not
this task.**

**DO NOT HYPOTHESISE `Q`.** Instantiate, by the standing ruling.

**DO NOT POSTULATE.**

**REQUIRED REPORT SECTION `## WHAT THE RE-BASING ACTUALLY COST`.** In lines and
seconds, against `[LJ-1.521]`'s figure of eleven. **If it is more, say by how
much: three conjuncts are priced against that number.**

**REQUIRED REPORT SECTION `## WHAT `injAt` NEEDS AFTER THIS`.** `[LJ-1.524]`
says one lemma. **Name it as a type and say whether the tree states it.** Do
not build it.

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 210 lines in the probe, of which the obligation is
about 30 and the re-basing about eleven, the rest being the rebuilt carve and
adequacy. BASIS: `[LJ-1.524]` rebuilt this telescope and closed a sibling
conjunct in a comparable file. Comparables are of SHAPE and nothing may be
funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the re-basing, because three conjuncts are priced against eleven lines
and nobody has written one of them.

    -- Bound, C and bnd, with swo-rank′ in place of swo-rank

**Write it FIRST, with the obligation omitted, and typecheck it ALONE.** If the
substitution does not go through, the range clause is not the cheapest of the
three and the triage `[LJ-1.524]` gave must be re-read.

ESTIMATE for W3: about 15 lines and under 40 seconds. **Do not fund it against
`[LJ-1.524]`'s numbers**: that closed a conjunct over the OLD carve.

## WHAT GO AND NO-GO EACH EARN

**A GO CLOSES THE SECOND CONJUNCT AND PAYS THE RE-BASING FOR THE OTHER TWO**,
leaving `injAt`'s lemma and `domAt`'s converse as the only named work on this
leg.

**A NO-GO AT THE RE-BASING SAYS THREE CONJUNCTS ARE MISPRICED**, which is worth
knowing before either of the other two is ordered.

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
  changed_files_none = ["agents/tasks/LJ-1-529/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-529/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-529/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-529/Probe529.agda"]
  changed_files_none = ["agents/tasks/LJ-1-529/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-529/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 168.767)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 153.819)
- CANDIDATE dev/ARCHIVE.md  (score 153.698)
- CANDIDATE archive/dev/JOURNAL.md  (score 148.184)
- CANDIDATE archive/dev/DD-archived.md  (score 125.980)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 48.694)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 43.047)
- CANDIDATE dev/literature/digest.md  (score 40.395)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 31.195)
- CANDIDATE dev/literature/terms-2026-08.md  (score 30.731)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
