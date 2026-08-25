# LJ-1.541: domAt, the fourth and last conjunct

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-541/Probe541.agda`:

    domAt-at-carve : (the domAt conjunct of InjCode, over the rank carve,
                      with Q instantiated)

**the fourth and last of the four `InjCode` conjuncts.** Land nothing in
`src/`.

**`[LJ-1.537]` IS GO AND IT SAYS `domAt` CLOSES WITH IT.** `approx-carve`
(`agents/tasks/LJ-1-537/Probe537.agda:616-620`) is built with no holes and no
postulate, and its report names every piece of `domAt-in`:

**THE SATISFACTION HALF.** `rankFo Q a` (`agents/tasks/LJ-1-521/Probe521.agda:493-501`)
at the pair `prʟ x r`, `r := rank-at′ a oa x xa`, asks four existentials and
three conjuncts:

- `var zero ≐ con Q` at `q := Q`: **`refl`**.
- `prAtL (s3 zero) (suc zero) zero`: **`prʟ-fst`**
  (`src/L/Coding/Model.lagda.md:329-330`).
- `var (suc zero) ∈̇ con a`: **the hypothesis**.
- `fnAt ∧̇ assignAt ∧̇ supAt`: **`approx-carve a oa x xa`**, `[LJ-1.537]`.

**THE BOUND HALF.** `pr x r ∈ fst bnd` is `rank-bound′`, delivered by
`[LJ-1.529]` (`agents/tasks/LJ-1-529/Probe529.agda:133-140`), reaching
`rank-at′` through `rank-at′-val` (`agents/tasks/LJ-1-521/Probe521.agda:438-442`).

**AND `domAt-out` WAS ALREADY DELIVERED** by `[LJ-1.524]`, with `domAt-intro`
(`src/L/Coding/Model.lagda.md:298-305`) taking the two directions and nothing
else.

**`[LJ-1.537]` STATES THAT AS A READING OF THE TYPES AND NOT AS A
MEASUREMENT**, and says so in its own words. **You are the measurement.** If a
piece does not fit where its report says it does, that is the finding and you
report it against the `file:line` above.

**`Q` IS INSTANTIATED, NOT HYPOTHESISED.** Standing ruling, confirmed at
`[LJ-1.524]` and used by `[LJ-1.529]` and `[LJ-1.531]`. Take `Q` at
`ord-set-witness a oa .fst` (`agents/tasks/LJ-1-521/Probe521.agda:1162-1164`).

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-541/Probe541.agda::domAt-at-carve"]

## SCOPE (write)
- agents/tasks/LJ-1-541/Probe541.agda
- agents/tasks/LJ-1-541/lj-1.541-report.md
- agents/tasks/LJ-1-541/review-of-domAt-at-carve.md
- agents/tasks/LJ-1-541/runs/

## PREMISES

1. `[LJ-1.537]` is GO and `approx-carve` is built. Basis: agents/tasks/LJ-1-537/Probe537.agda:616
2. Its report names every piece of `domAt-in`. Basis: agents/tasks/LJ-1-537/lj-1.537-report.md:1
3. `domAt-in` is the direction that was missing. Basis: src/L/Coding/Model.lagda.md:294
4. `domAt-intro` takes the two directions and nothing else. Basis: src/L/Coding/Model.lagda.md:298
5. `prʟ-fst` splits the pair. Basis: src/L/Coding/Model.lagda.md:329
6. `rankFo` is delivered. Basis: agents/tasks/LJ-1-521/Probe521.agda:493
7. `rank-at′-val` reaches the rank's value. Basis: agents/tasks/LJ-1-521/Probe521.agda:438
8. `rank-bound′` is delivered. Basis: agents/tasks/LJ-1-529/Probe529.agda:133
9. The `Q` witness is delivered. Basis: agents/tasks/LJ-1-521/Probe521.agda:1162
10. `[LJ-1.524]` delivered `domAt-out` and closed `svAt`. Basis: agents/tasks/LJ-1-524/lj-1.524-report.md:277
11. `[LJ-1.531]` proved the rank injective, which closed `injAt`'s lemma. Basis: agents/tasks/LJ-1-531/lj-1.531-report.md:1
12. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
13. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
14. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THIS IS THE FOURTH OF FOUR.** `[LJ-1.524]` closed `svAt`, `[LJ-1.529]` closed
the range clause and paid the re-basing, `[LJ-1.531]` built the lemma `injAt`
wanted, `[LJ-1.537]` built the carve `domAt` wanted. **Fifteen dispatches on
this leg, and this is the composition they were for.**

## THE REASONING

**D-10, BEFORE ANY AGDA.** `[LJ-1.537]` lists four pieces for the satisfaction
half and one for the bound half. **Check each at its `file:line` and say
whether the types compose end to end.** `[LJ-1.537]` says its environment is
already the one `rankFo` builds and points at `runs/Pin.agda:46-62` as its own
check. **Re-run that check yourself; do not take it on the report's word.**

**IF A PIECE DOES NOT FIT, NAME IT AND STOP.** Fifteen dispatches stand behind
this composition. **An adapter written silently would hide which of them was
mispriced.**

**DO NOT REBUILD `approx-carve`, `rank-bound′` OR `rankFo`.** All three are
delivered in predecessors' probes. Rebuild at their delivered types; do not
import a probe.

**DO NOT HYPOTHESISE `Q`.** Instantiate, by the standing ruling.

**DO NOT CLAIM `InjCode`.** AD12 gives this brief one obligation, and the four
conjuncts assembled into `InjCode` is the next task.

**DO NOT POSTULATE.**

**REQUIRED REPORT SECTION `## ALL FOUR CONJUNCTS`.** One row per conjunct with
its `file:line` and whether it is now delivered: `svAt` (`[LJ-1.524]`), the
range clause (`[LJ-1.529]`), `injAt` (`[LJ-1.531]`'s lemma plus the
composition), `domAt` (this task). **Say plainly whether `InjCode` is now a
composition of delivered terms, and do not build it.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 220 lines in the probe, of which the obligation is
about 55 and the rest is the rebuilt carve, rank, bound and adequacy. BASIS:
`[LJ-1.537]` rebuilt most of that telescope in a comparable file at 2.29 s cold.
Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the environment match, because `[LJ-1.537]` checked it in a side file and
nobody has run the two together.

    -- approx-carve's f, in the environment rankFo builds, at the pair

**Write it FIRST, with the obligation omitted, and typecheck it ALONE.** If the
environments differ, say by how much: that is the adapter nobody has priced and
it belongs in the record, not inside a term.

ESTIMATE for W3: about 25 lines and under 45 seconds. **Do not fund it against
`[LJ-1.537]`'s numbers**: that built a carve and this places one.

## WHAT GO AND NO-GO EACH EARN

**A GO CLOSES THE FOURTH OF FOUR CONJUNCTS**, and `InjCode`, which
`GCHStatement` consumes through `InjL`, becomes a composition of delivered
terms for the first time.

**A NO-GO NAMES WHICH OF FIFTEEN DISPATCHES WAS MISPRICED**, which is worth
more than a term, and the brief would rather have that than an adapter nobody
recorded.

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
  changed_files_none = ["agents/tasks/LJ-1-541/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-541/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-541/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-541/Probe541.agda"]
  changed_files_none = ["agents/tasks/LJ-1-541/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-541/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 130.770)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 128.489)
- CANDIDATE archive/dev/JOURNAL.md  (score 109.389)
- CANDIDATE dev/ARCHIVE.md  (score 108.492)
- CANDIDATE archive/dev/PLAN-archived.md  (score 95.943)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 58.764)
- CANDIDATE dev/literature/geology.md  (score 35.732)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 33.536)
- CANDIDATE dev/literature/terms-2026-08.md  (score 33.326)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 29.634)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
