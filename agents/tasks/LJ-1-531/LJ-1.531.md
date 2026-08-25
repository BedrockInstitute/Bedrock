# LJ-1.531: the rank is injective, which is all injAt still wants

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-531/Probe531.agda`:

    rank-at′-inj :
        (a : S) (oa : IsOrd (fst a)) (m m' : S)
        (mx : ⟨ fst m ∈ fst a ⟩) (mx' : ⟨ fst m' ∈ fst a ⟩)
      → fst (rank-at′ a oa m mx) ≡ fst (rank-at′ a oa m' mx')
      → fst m ≡ fst m'

**the replacement rank is injective on the members of `a`.** Land nothing in
`src/`.

**`[LJ-1.529]` IS GO AND IT NAMED THIS AS THE ONLY THING `injAt` STILL WANTS.**
It closed the range clause, the second of the four `InjCode` conjuncts, and
**paid the `swo-rank′` re-basing that three conjuncts ride on**. Its own words:
"The re-basing half is now paid: `Bound′`, `C` and `bnd` above are the codomain
and the bound `injAt` also wants, and they are written. I did not build the
lemma." It gave the type in the shape the consumer needs
(`agents/tasks/LJ-1-529/lj-1.529-report.md`, `## WHAT `injAt` NEEDS AFTER
THIS`).

**THE RE-BASING COST THREE TIMES ITS ESTIMATE AND YOU SHOULD KNOW THE NUMBER.**
`[LJ-1.521]` called it eleven lines. `[LJ-1.529]` measured **33 code lines**:
`Bound′` (`agents/tasks/LJ-1-529/Probe529.agda:101-131`) is 23 and
`rank-bound′` (`:133-142`) is 10, **of which 20 of the 23 are `[LJ-1.490]`'s
line for line.** Take `[LJ-1.529]`'s `Bound′` and `rank-bound′` at their
delivered shapes; do not re-derive them and do not re-price them.

**WHY THIS IS THE RIGHT SHAPE OF LEMMA.** `swo-rank′` is a rank over the
predecessors, and `[LJ-1.515]` proved `swo-rank′-∅` and `swo-rank′-∅-only`
(`agents/tasks/LJ-1-515/Probe515.agda:218-231`). **Injectivity is the third
property of that family and nobody has asked for it.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-531/Probe531.agda::rank-at′-inj"]

## SCOPE (write)
- agents/tasks/LJ-1-531/Probe531.agda
- agents/tasks/LJ-1-531/lj-1.531-report.md
- agents/tasks/LJ-1-531/review-of-rank-at-inj.md
- agents/tasks/LJ-1-531/runs/

## PREMISES

1. `[LJ-1.529]` is GO and closed the range clause. Basis: agents/tasks/LJ-1-529/lj-1.529-report.md:1
2. It names this lemma as all `injAt` still wants. Basis: agents/tasks/LJ-1-529/lj-1.529-report.md:1
3. It paid the re-basing, at 33 lines against an estimate of eleven. Basis: agents/tasks/LJ-1-529/Probe529.agda:101
4. `rank-bound′` is delivered there. Basis: agents/tasks/LJ-1-529/Probe529.agda:133
5. `[LJ-1.524]` reported `injAt` needs the re-basing and one lemma. Basis: agents/tasks/LJ-1-524/lj-1.524-report.md:261
6. `rank-at′` is defined in `[LJ-1.521]`'s probe. Basis: agents/tasks/LJ-1-521/Probe521.agda:1006
7. `swo-rank′` is the rank it packages. Basis: agents/tasks/LJ-1-515/Probe515.agda:112
8. `swo-rank′-∅` is proved. Basis: agents/tasks/LJ-1-515/Probe515.agda:218
9. `swo-rank′-∅-only` is proved beside it. Basis: agents/tasks/LJ-1-515/Probe515.agda:228
10. `preds` has exactly the members of `a`. Basis: agents/tasks/LJ-1-513/Probe513.agda:103
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**TWO OF THE FOUR CONJUNCTS ARE CLOSED AND THE RE-BASING IS PAID FOR ALL
FOUR.** `[LJ-1.524]` closed `svAt`, `[LJ-1.529]` closed the range clause.
**After this lemma, `injAt` is the third, and only `domAt`'s converse remains
named.**

## THE REASONING

**D-10, BEFORE ANY AGDA.** A rank over the predecessors is injective only if
distinct members have distinct predecessor sets. **Say at `file:line` whether
the order `swo-rank′` recurses on is extensional in that sense.** If two
distinct members of `a` can have the same predecessors, the lemma is FALSE and
you must refute it rather than fail to build it. **`[LJ-1.497]` refuted a rank
statement in this same family and that is a respectable return.**

**USE `swo-rank′-∅-only` IF IT HELPS.** `[LJ-1.515]` built it beside
`swo-rank′-∅` and no dispatch has consumed it. It says the rank is `∅` ONLY at
a minimal element, which is the base case of an injectivity argument.

**DO NOT REBUILD `Bound′` OR `rank-bound′`.** `[LJ-1.529]` delivered them at 33
lines. Take them.

**DO NOT BUILD `injAt` ITSELF.** AD12 gives this brief one obligation.
`[LJ-1.529]` says the codomain and the bound are already written, so `injAt`
is the next task and a short one.

**DO NOT TOUCH `domAt`.** `[LJ-1.524]` measured that `domAt-in` asks for the
CONVERSE of `rankFo-adequate′` and that nothing in the tree supplies it. That
is the leg's remaining wall and it is not this task.

**DO NOT POSTULATE.**

**REQUIRED REPORT SECTION `## WHAT `injAt` NEEDS AFTER THIS`.** If the lemma
lands, say whether `injAt` is now a composition of delivered terms, at
`file:line`. **Do not build it.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 190 lines in the probe, of which the obligation is
about 45 and the rest is the rebuilt carve, rank and bound. BASIS:
`[LJ-1.529]` rebuilt the same telescope and closed a conjunct in a comparable
file. Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is extensionality of the order, because injectivity of a rank over
predecessors stands or falls on it.

    preds-distinguish : (a : S) (oa : IsOrd (fst a)) (m m' : S)
                      → (their predecessor sets agree) → fst m ≡ fst m'

**Write it FIRST, and typecheck it ALONE.** If it will not form, the lemma is
false, `injAt` needs a different argument, and the task stops at its cheapest
point having refuted rather than failed.

ESTIMATE for W3: about 25 lines and under 40 seconds. **Do not fund it against
`[LJ-1.529]`'s numbers**: that re-based a bound and this argues extensionality.

## WHAT GO AND NO-GO EACH EARN

**A GO LEAVES `injAt` A COMPOSITION OF DELIVERED TERMS** and the coding leg
with one named wall.

**A REFUTATION SAYS THE RANK IS NOT INJECTIVE**, which would mean `injAt`
cannot be had from this rank at all and the conjunct needs a different
argument. **That is a real outcome and the brief prefers it to a failure.**

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
  changed_files_none = ["agents/tasks/LJ-1-531/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-531/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-531/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-531/Probe531.agda"]
  changed_files_none = ["agents/tasks/LJ-1-531/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-531/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 186.012)
- CANDIDATE archive/dev/JOURNAL.md  (score 167.910)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 158.446)
- CANDIDATE dev/ARCHIVE.md  (score 146.531)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 126.295)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 57.634)
- CANDIDATE dev/literature/devlin-II5.md  (score 55.191)
- CANDIDATE dev/literature/digest.md  (score 41.487)
- CANDIDATE dev/literature/terms-2026-08.md  (score 38.697)
- CANDIDATE dev/literature/geology.md  (score 30.919)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
