# LJ-1.524: svAt, the first of the four conjuncts, with Q determined

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-524/Probe524.agda`:

    svAt-at-carve : (the svAt conjunct of InjCode, over the delivered rank carve)

**with `Q` INSTANTIATED at `ord-set-witness a oa .fst`, not carried as a
hypothesis.** Land nothing in `src/`.

**`[LJ-1.521]` IS GO AND `svAt` IS THE ONE CONJUNCT WITH EVERY INPUT.** Its
report says so and names all four steps
(`agents/tasks/LJ-1-521/lj-1.521-report.md`, `## WHAT THE FOUR CONJUNCTS NEED
NOW`):

- `rank-graph-out` (`agents/tasks/LJ-1-490/Probe490.agda:111-116`) turns each
  pair in the carve into satisfaction of `rankFo Q a`. DELIVERED.
- `rankFo-adequate′` (`agents/tasks/LJ-1-521/Probe521.agda:1006`) turns each
  satisfaction into the pair equality. DELIVERED.
- `pr-inj` (`src/V/Coding.lagda.md:178-179`) splits it. DELIVERED.
- `↾-reflects` (`src/FOL/ZFStructure.lagda.md:164-167`) lifts it. DELIVERED.

**THE MATHEMATICIAN HAS RULED THE `Q` QUESTION AND THIS BRIEF CARRIES THE
RULING.** `[LJ-1.521]` measured that `RankCoded` (`Probe490.agda:289-292`)
quantifies over an arbitrary `Q` while `rankFo-adequate′` consumes
`ord-reads-Q Q a oa`, so **no conjunct is provable at an arbitrary `Q`**, and it
named two ways out: carry `hQ` in the telescope, or instantiate `Q` at
`ord-set-witness a oa .fst` (`Probe521.agda:1162-1164`).

**RULING: INSTANTIATE.** `GCHStatement` consumes these conjuncts through
`InjL a b = ∥ Σ[ F ∈ S ] InjCode F a b ∥₁` (`src/L/GCH.lagda.md:37-38`), and
**neither `InjL` nor `InjCode` names a `Q`**. So `Q` is internal to the
construction, nothing downstream can want a different one, and the witness is
delivered. **A determined telescope beats a hypothesised one when the witness
exists.** If instantiation costs something the report must say what.

**ONE RE-SPELLING IS NEEDED AND IT IS NOT THIS TASK.** `[LJ-1.521]` measured
that `[LJ-1.490]`'s `Bound`, `C` and `bnd` (`Probe490.agda:211-232`) are built
on `swo-rank`, the rank `[LJ-1.497]` refuted, and must be re-based on
`swo-rank′`: "a re-spelling of eleven lines and not a new proof, but it is not
free and nobody has done it". **It binds three of the four conjuncts and `svAt`
is not one of them.** Do it only if `svAt` needs it, and say so.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-524/Probe524.agda::svAt-at-carve"]

## SCOPE (write)
- agents/tasks/LJ-1-524/Probe524.agda
- agents/tasks/LJ-1-524/lj-1.524-report.md
- agents/tasks/LJ-1-524/review-of-svAt-at-carve.md
- agents/tasks/LJ-1-524/runs/

## PREMISES

1. `[LJ-1.521]` is GO and `rankFo-adequate′` is built with no holes. Basis: agents/tasks/LJ-1-521/Probe521.agda:1006
2. Its report names `svAt` as having every input delivered. Basis: agents/tasks/LJ-1-521/lj-1.521-report.md:1
3. `ord-set-witness` is the delivered witness for `Q`. Basis: agents/tasks/LJ-1-521/Probe521.agda:1162
4. `RankCoded` quantifies over an arbitrary `Q` today. Basis: agents/tasks/LJ-1-490/Probe490.agda:289
5. `rank-graph-out` reads the carve. Basis: agents/tasks/LJ-1-490/Probe490.agda:111
6. `svAt` is declared in the coding chapter. Basis: src/L/Coding/Model.lagda.md:210
7. `svAt-in` reduces it. Basis: src/L/Coding/Model.lagda.md:238
8. `pr-inj` splits the pair equality. Basis: src/V/Coding.lagda.md:178
9. `↾-reflects` lifts the carrier equality. Basis: src/FOL/ZFStructure.lagda.md:164
10. `InjL` names no `Q`. Basis: src/L/GCH.lagda.md:37
11. `Bound`, `C` and `bnd` are built on the refuted rank. Basis: agents/tasks/LJ-1-490/Probe490.agda:211
12. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
13. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
14. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**TWELVE DISPATCHES BUILT THE CODING LEG AND `[LJ-1.521]` CLOSED ITS
ADEQUACY.** `[LJ-1.497]` refuted the old one, `[LJ-1.513]` removed the universe
obstruction, `[LJ-1.515]` delivered the replacement rank, `[LJ-1.518]` supplied
the missing hypothesis, `[LJ-1.521]` built the adequacy. **This is the first
conjunct those five were for.**

## THE REASONING

**D-10, BEFORE ANY AGDA.** `[LJ-1.521]` lists four steps for `svAt`. **Check
each at its `file:line` and say whether the types compose end to end.** If a
step's output is not the next step's input, name the adapter and STOP rather
than writing one silently: an unrecorded adapter is how a four-step chain
becomes a five-step one nobody priced.

**DO NOT CARRY `hQ` IN THE TELESCOPE.** The ruling is instantiation. If
instantiation fails, that is a finding against the ruling and you report it;
you do not switch to the other option on your own.

**DO NOT BUILD THE OTHER THREE CONJUNCTS.** AD12 gives this brief one
obligation, and three of them need the `swo-rank′` re-basing that this task
does not do.

**DO NOT REVERT TO `swo-rank` AND DO NOT REBUILD `rankFo-adequate′`.**

**DO NOT POSTULATE.**

**REQUIRED REPORT SECTION `## WHAT INSTANTIATING Q COST`.** One paragraph: what
the telescope looks like after, and whether anything that was provable at an
arbitrary `Q` is now not. **If the answer is "nothing", say it in those
words.**

**REQUIRED REPORT SECTION `## THE OTHER THREE`.** For `domAt`, `injAt` and the
range clause, say whether each now needs only the `swo-rank′` re-basing or
something more, at `file:line`. **Do not build them.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 200 lines in the probe, of which the obligation is
about 50 and the rest is the rebuilt carve and adequacy. BASIS: `[LJ-1.521]`
rebuilt this telescope and the adequacy in a comparable file. Comparables are
of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the instantiation, because the ruling rests on it and nobody has fed
`ord-set-witness`'s `Q` to a conjunct.

    -- rankFo-adequate′ applied at Q := ord-set-witness a oa .fst

**Write it FIRST, with the obligation omitted, and typecheck it ALONE.** If the
witness's `Q` does not satisfy the adequacy's own hypothesis at this frame, the
ruling is wrong and the task stops at its cheapest point.

ESTIMATE for W3: about 20 lines and under 40 seconds. **Do not fund it against
`[LJ-1.521]`'s numbers**: that built the adequacy and this applies it once.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO CLOSES THE FIRST OF THE FOUR CONJUNCTS** and confirms the `Q` ruling
against a real consumer.

**A NO-GO AT THE INSTANTIATION REFUTES THE RULING**, and the telescope carries
`hQ` instead. That is a cheap correction and worth having before three more
conjuncts are built on the wrong choice.

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
  changed_files_none = ["agents/tasks/LJ-1-524/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-524/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-524/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-524/Probe524.agda"]
  changed_files_none = ["agents/tasks/LJ-1-524/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-524/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 186.750)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 170.106)
- CANDIDATE archive/dev/JOURNAL.md  (score 144.707)
- CANDIDATE dev/ARCHIVE.md  (score 141.426)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 124.638)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 69.048)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 54.963)
- CANDIDATE dev/literature/digest.md  (score 48.141)
- CANDIDATE dev/literature/terms-2026-08.md  (score 42.904)
- CANDIDATE dev/literature/geology.md  (score 32.085)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
