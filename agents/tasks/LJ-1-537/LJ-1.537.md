# LJ-1.537: the approximating function, as a set of the model

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-537/Probe537.agda`:

    approx-carve : (a : S) (oa : IsOrd (fst a)) (m : S) → ⟨ fst m ∈ fst a ⟩
                 → Σ[ f ∈ S ] (f satisfies fnAt, assignAt and supAt)

**the graph of `swo-rank′` restricted to the ∈-predecessors of `m`, AS A SET OF
THE MODEL, with its three satisfaction properties.** Land nothing in `src/`.

**THIS IS THE CODING LEG'S LAST NAMED WORK AND `[LJ-1.521]` SPELLED ITS
SHAPE.** Its words: "**THE CONVERSE MUST EXHIBIT AN APPROXIMATING FUNCTION
`f`**, that is, the graph of `swo-rank′` restricted to the ∈-predecessors of a
member, AS A SET OF THE MODEL, and prove it satisfies `fnAt`, `assignAt` and
`supAt`. `[LJ-1.518]`'s `Witness` is the model for how such a set is carved
(`Probe521.agda:1046-1160` here). **That is the next task, and it is bigger.**"

**WHY IT IS THE LAST.** Of the four `InjCode` conjuncts, `[LJ-1.524]` closed
`svAt`, `[LJ-1.529]` closed the range clause, `[LJ-1.531]` built the lemma
`injAt` wanted. **`domAt` is the fourth**, and `[LJ-1.524]` measured that
`domAt-in` (`src/L/Coding/Model.lagda.md:294-296`) asks for the CONVERSE of
`rankFo-adequate′` and that nothing in the tree supplies it.

**THE CARVE HAS A DELIVERED MODEL AND YOU SHOULD READ IT BEFORE YOU WRITE.**
`[LJ-1.521]`'s `Witness` at `agents/tasks/LJ-1-521/Probe521.agda:1046-1160` is
114 lines that carve a set of the model for a related purpose. **It is a model
of METHOD, not a term to import.**

**AND THE RANK IS DELIVERED WITH THREE PROPERTIES.** `swo-rank′`
(`agents/tasks/LJ-1-515/Probe515.agda:112-113`), `swo-rank′-ord` (`:115-117`),
`swo-rank′-∅` (`:218-221`), `swo-rank′-∅-only` (`:228-231`), and injectivity
from `[LJ-1.531]`. **The function you carve is the graph of a rank that is
fully characterised.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-537/Probe537.agda::approx-carve"]

## SCOPE (write)
- agents/tasks/LJ-1-537/Probe537.agda
- agents/tasks/LJ-1-537/lj-1.537-report.md
- agents/tasks/LJ-1-537/review-of-approx-carve.md
- agents/tasks/LJ-1-537/runs/

## PREMISES

1. `[LJ-1.521]` names this as the next task and spells its shape. Basis: agents/tasks/LJ-1-521/lj-1.521-report.md:384
2. `Witness` is the delivered model for the carve. Basis: agents/tasks/LJ-1-521/Probe521.agda:1046
3. `domAt-in` is what the converse serves. Basis: src/L/Coding/Model.lagda.md:294
4. `[LJ-1.524]` measured nothing in the tree supplies it. Basis: agents/tasks/LJ-1-524/lj-1.524-report.md:261
5. `swo-rank′` is delivered. Basis: agents/tasks/LJ-1-515/Probe515.agda:112
6. Its ordinality is delivered. Basis: agents/tasks/LJ-1-515/Probe515.agda:115
7. `swo-rank′-∅` is proved. Basis: agents/tasks/LJ-1-515/Probe515.agda:218
8. `swo-rank′-∅-only` is proved. Basis: agents/tasks/LJ-1-515/Probe515.agda:228
9. `[LJ-1.531]` proved the rank injective. Basis: agents/tasks/LJ-1-531/lj-1.531-report.md:1
10. `preds` has exactly the members of `a`. Basis: agents/tasks/LJ-1-513/Probe513.agda:103
11. `rankFo-adequate′` is the direction already built. Basis: agents/tasks/LJ-1-521/Probe521.agda:1006
12. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
13. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
14. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THREE OF THE FOUR `InjCode` CONJUNCTS ARE CLOSED OR ONE COMPOSITION AWAY.**
The rank is replaced and fully characterised, the adequacy is built, the
re-basing is paid. **This is the fourth conjunct's one missing input and the
leg's last named work.**

## THE REASONING

**D-10, BEFORE ANY AGDA.** `hasSeparationL` and `hasReplacementL`
(`src/L/Axioms/Full.lagda.md:144-146`, `:277-280`) are the two generators of an
L-element set and **both take a `Formula`**. `[LJ-1.533]` proved that by type
argument at a different site. **Say at `file:line` which generator you will use
and what formula you will give it.** If neither can carve the graph of
`swo-rank′`, name why and STOP: that would say the converse is unreachable by
the tree's own set-forming rules, which is the sharpest finding this leg could
produce.

**THE THREE PROPERTIES ARE THE OBLIGATION, NOT DECORATION.** A set that is not
provably a function under `fnAt`, or does not assign under `assignAt`, or does
not bound under `supAt`, pays nothing. **Build all three or report which
resisted.**

**DO NOT BUILD `domAt-in` OR `domAt`.** AD12 gives this brief one obligation.
`[LJ-1.521]` calls this the next task and the conjunct the one after.

**DO NOT IMPORT `[LJ-1.521]`'s `Witness`.** Read its method; carve your own.

**DO NOT WEAKEN THE RESTRICTION.** The graph must be over the ∈-predecessors of
`m`, which is what `[LJ-1.513]`'s `preds` gives.

**DO NOT POSTULATE.**

**REQUIRED REPORT SECTION `## WHAT `domAt` NEEDS AFTER THIS`.** If the carve
lands, say whether `domAt-in` is now a composition of delivered terms, at
`file:line`, and whether `domAt` closes with it. **Do not build either.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: **`[LJ-1.521]` called this bigger than its own work and
I take that at face value.** Its `Witness` carve is 114 lines
(`Probe521.agda:1046-1160`) for a related purpose, and this task adds three
satisfaction proofs on top. **Report what it actually cost; I give no total.**

## W3, THE WIDEST UNMEASURED TERM

It is the formula the generator wants, because `[LJ-1.533]` proved no set is
formed without one and nobody has written this one.

    -- the Formula that carves the graph of swo-rank′ over preds

**Write it FIRST, with the three properties omitted, and typecheck it ALONE.**
If the rank's recursion cannot be said in the object language at this arity,
the carve is out of reach and the task stops at its cheapest point.

ESTIMATE for W3: about 35 lines and under 60 seconds. **Do not fund it against
`[LJ-1.518]`'s or `[LJ-1.521]`'s numbers**: both carved sets for a different
purpose.

## WHAT GO AND NO-GO EACH EARN

**A GO LEAVES THE CODING LEG WITH `domAt` ALONE**, and all four `InjCode`
conjuncts within one dispatch of each other.

**A NO-GO AT THE FORMULA SAYS THE RANK'S GRAPH CANNOT BE CARVED IN THIS
MODEL**, which would refute the coded-injection route at its last step and is a
ruling-grade finding after thirteen dispatches.

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
  changed_files_none = ["agents/tasks/LJ-1-537/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-537/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-537/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-537/Probe537.agda"]
  changed_files_none = ["agents/tasks/LJ-1-537/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-537/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 156.032)
- CANDIDATE archive/dev/JOURNAL.md  (score 145.613)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 142.683)
- CANDIDATE dev/ARCHIVE.md  (score 115.798)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 114.254)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 55.062)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 43.117)
- CANDIDATE dev/literature/terms-2026-08.md  (score 35.409)
- CANDIDATE dev/literature/digest.md  (score 33.610)
- CANDIDATE dev/literature/geology.md  (score 32.229)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
