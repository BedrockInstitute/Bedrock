# LJ-1.555: land CardAboveL, and measure what a landing costs

## HEAD
head_slot: coder
machine: exclusive

## THE OBLIGATION

Land ONE term into `src/`:

    CardAboveL : <the statement [LJ-1.528] proved>

moved from `agents/tasks/LJ-1-528/Probe528.agda` into the chapter where it
belongs, with `make check` green.

**THIS IS THE FIRST LANDING THIS CAMPAIGN HAS ATTEMPTED, AND THAT IS THE POINT.**
`[LJ-1.544]` counted `[LJ-1.523]`'s ten bridge inputs and found four of the
seven paid ones are **"PAID, in a probe"** and not in the tree
(`agents/tasks/LJ-1-544/lj-1.544-report.md`). A term in a probe is not in the
build, is not checked by `make check`, and is not available to any other
chapter. **Nobody has measured what moving one costs.**

**WHY THIS TERM AND NOT ANOTHER.** `[LJ-1.528]` built `CardAboveL` under
`--safe` with no choice and no postulate, `[LJ-1.526]` proved it reduces B4, and
`[LJ-1.526]` also overturned the archive's claim that `IsCardinal` is never
inhabited. **It is the most finished term the campaign has**, and it appears
nowhere in `src/` today: `grep -rn CardAboveL src/` returns nothing.

## OBLIGATION NAMES
obligations = ["src/L/StageCardinal.lagda.md::CardAboveL"]

**THE CHAPTER ABOVE IS A PROPOSAL AND NOT A RULING.** `src/L/StageCardinal.lagda.md`
holds the neighbouring cardinal material (`:22`, `:100-104`, `:124-129`).
**If you judge another chapter correct, land it there, say why at `file:line`,
and put the real path in your report's first line.** State the obligation name
you actually delivered.

## SCOPE (write)
- src/L/StageCardinal.lagda.md
- agents/tasks/LJ-1-555/lj-1.555-report.md
- agents/tasks/LJ-1-555/review-of-CardAboveL-landing.md
- agents/tasks/LJ-1-555/runs/

## PREMISES

1. `[LJ-1.528]` built `CardAboveL` and paid B4. Basis: agents/tasks/LJ-1-528/Probe528.agda:70
2. Its probe is committed. Basis: agents/tasks/LJ-1-528/Probe528.agda:3
3. `[LJ-1.526]` proved the reduction it discharges. Basis: agents/tasks/LJ-1-528/Probe528.agda:5
4. `[LJ-1.544]` counted four inputs paid only in probes. Basis: agents/tasks/LJ-1-544/lj-1.544-report.md:1
5. `src/L/StageCardinal.lagda.md` holds neighbouring cardinal material. Basis: src/L/StageCardinal.lagda.md:100
6. `IsCardinalL` is stated by `InjCode`. Basis: src/L/Cardinal.lagda.md:230
7. `make check` is the gate before any commit. Basis: AGENTS.md:74
8. Never commit a generated file. Basis: AGENTS.md:71
9. The program commits, by explicit path from the task's scope. Basis: AGENTS.md:78
10. Chapter style is ruled. Basis: dev/STYLE-agda.md:1
11. Literate Agda and prose rules are ruled. Basis: dev/STYLE-i18n.md:1
12. No mathematical prose until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

A `--safe`, choice-free proof in a probe, and a reduction that consumes it.
**Neither is in the build.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE CHAPTER.** Say at `file:line` which
chapter you will land in and what its existing imports are. **If landing there
creates an import cycle, say so and name the chapter that does not.**

**THE PROSE RULE BINDS AND IT IS NARROW.** `AGENTS.md:69` forbids mathematical
prose until both trophies are proved in the tree. **Write the code, the comments
inside it, and nothing else.** Do not write a chapter introduction and do not
explain the mathematics in prose.

**MEASURE THE LANDING AND REPORT IT AS NUMBERS.** This is the task's second
deliverable and the campaign has no figure for it. Report: lines added to `src/`,
`make check` wall time before and after, and any import you had to add.

**DO NOT WEAKEN THE STATEMENT TO MAKE IT LAND.** If the probe's term needs a
hypothesis the chapter cannot supply, **say which and stop.** A named stop here
is worth more than a landed but weaker term.

**DO NOT LAND ANY OTHER PROBE TERM.** AD12 gives this brief one obligation.
The other three probe-only inputs stay where they are.

**DO NOT POSTULATE. NEVER COMMIT AND NEVER PUSH.** The program commits, by
explicit path from this task's scope.

**REQUIRED REPORT SECTION `## WHAT THE LANDING COST`.** The numbers above, and
one sentence saying whether the other three probe-only inputs look comparable.

**REQUIRED REPORT SECTION `## WHAT MOVED AND WHAT DID NOT`.** Say whether
`Probe528.agda` still typechecks after the move, and whether you left it
importing the landed term or duplicated it. **Duplication is a defect: say so if
you had to.**

ESTIMATE: about 60 lines added to `src/`, plus `make check`. BASIS: the probe's
term plus its statement. **The `make check` time is the unmeasured part and it
is why this task is `machine: exclusive`.** Comparables are of SHAPE and nothing
may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is `make check` itself, at this tree, today.

    -- make check, green, BEFORE any edit, with its wall time recorded

**Run it FIRST and record the time.** If the tree is not green before you touch
it, stop and say so: nothing this task does would be attributable.
ESTIMATE: unmeasured, and that is the point of running it first.

## WHAT GO AND NO-GO EACH EARN

**A GO PUTS THE FIRST BRIDGE INPUT IN THE TREE AND PRICES THE OTHER THREE.**
Until a term is in `src/` it is not in the build, and the trophy case is in
`src/`.

**A NO-GO THAT NAMES THE IMPORT CYCLE OR THE MISSING HYPOTHESIS TELLS THE
CAMPAIGN THAT ITS PROBE WORK DOES NOT LAND AS IT STANDS**, which is the most
important thing the mathematician could learn this week.

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
  changed_files_none = ["agents/tasks/LJ-1-555/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-555/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-555/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-555/Probe555.agda"]
  changed_files_none = ["agents/tasks/LJ-1-555/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-555/review-of-*.md"]

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

MANDATORY for kind `build` (writes a master under src/. The heaviest bundle, because a build is where seconds and lines are actually spent.):

- **P-h. Definability walks are module-parameterized, never function-parameterized**
  **Rule:** A definability walk (the `defSet≡` extensionality of an InL-idiom constructibility lemma) takes its set arguments as parameters of a module, not of a function, and those parameters stay ABSTRACT through the walk: the formulas and the readers never mention a concrete `sett` body (`slice`, `satSet`, a stage over them); the instantiation at real sets happens only at the lemma-assembly le...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:200
- **P-k. A read lemma is stated where its consumers use it, not where its proof ends**
  **The law.** When a lemma exists so that consumers can rewrite with it, its stated right-hand side must be **the form the consumers actually need**, not the form the proof happened to reach. If it stops one layer early, every consumer re-normalizes the missing layer, and the same conversion is paid once per consumer instead of once in total. **Absorb the last layer into the lemma and seal it**,...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2453
- **P-l. A statement may be ABOUT a concrete stage without dragging that stage's PRESENTATION into its type**
  **The law.** Being about a concrete position is not what costs. Naming a transparent construction in a statement's TYPE is. If the tower's stage values are `opaque` upstream, a theorem may quantify over, hypothesize about and conclude at `Sset ω` freely, because the stage is an ATOM to the elaborator and nothing unfolds. If instead the type mentions a transparent presentation, such as `⟪ sucV (...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2357
- **P-m. The check-cost rate is a content-class certificate, and instantiation is the expensive class**
  **Rule:** Seconds per line identify a block's CONTENT CLASS before any profile is run, and line count alone predicts nothing. **Parameterized content**, whose definitions check at bound variables under a module telescope, checks near **0.01 s per line**. **Instantiation content**, which states object-language formulas at a concrete carrier, proves decodes that walk the satisfaction relation, an...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2512
- **P-n. Satisfaction content at a concrete carrier is a payable floor, not a defect**
  **Rule:** When a proof states object-language formulas at a CONCRETE carrier and proves their two-way decodes, the elaborator normalizes the carrier's presentation at every such definition, and **named branches with written types do not remove that cost**. I-5's cure applies to a missing type, not to this; if every hot branch already carries a written type, the remaining cost is the machinery a...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2535
- **R-35. Union representations are meta-poisoned; state memberships at small indices**
  **Rule:** Index or path extraction from the representation of a union of an open term (`⟪ ⋃ x ⟫`-level fiber extraction, `separation-ax` over a union) leaves unsolved metas or churns the presentation machinery; state the membership at the SMALL INDEX instead (an existential over `⟪ y ⟫` with the inclusion applied), and keep constructions at the stuck-member level.
  Full entry: dev/LESSONS.md:808
- **R-38. A consumer's alias of a transparent imported operation is a birth site**
  **Rule:** P-c extends one layer up: when a consumer names a composite of a TRANSPARENT imported operation (a derived op whose body reaches an imported sett/union tower), the consumer's alias is itself a birth site and must be sealed opaque with its spec inside, even though the imported operation was delivered transparent. Transparent-by-delivery kit operations (the Images F10 and the left/right...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:855
- **R-40. A deep successor-chain membership witness normalizes super-linearly; climb by small closures**
  **Rule:** An ordinal-membership premise stated at a deep iterated successor (`+ω-iter n`, a `sucV`-chain) forces the conversion checker to normalize the whole chain against the level's union representation, and the cost is super-linear in the depth. State the witness at a SHALLOW index and climb by the limit-ordinal successor closure (`limit-succ-mem`, `L.Rud.Hierarchy:455`), one step per line....
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:955
- **I-5. Inner-world truncation branches carry written types**
  **Rule:** In the inner world, every `PT.rec`/`PT.map` branch gets a named `where` function with a WRITTEN type; a branch whose type is left to inference re-elaborates the inner satisfaction machinery per constraint and reads as a conversion wall. The trap's target class is wider than the retiring stack recorded: it fires on equations between iterated Kuratowski pairs, not only on disjunctions o...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:1255
- **C-12. Agda runs under a hard heap cap; parallel writers under a quota**
  **Rule:** Every agda invocation runs under a GHC heap cap (`GHCRTS=-M<n>g`) so a runaway typecheck dies with a clean "Heap exhausted" exit instead of OOM-killing the machine; the orchestrator's audits run at `-M16g` and `make` exports a default. Sub-agent concurrency is TIERED (owner-widened 2026-08-02 once the caps and the watchdog were live): WIDE mode for routine batches, up to FOUR concurre...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2135
- **D-10. Price the truth of a recorded residue before pricing its proof**
  **Rule:** A residue recorded under the wall protocol names a TARGET, and a target can be false; before dispatching a discharge batch, spend the five minutes checking the target's truth at the intended generality (a Tarskian or cardinality obstruction is the usual killer), and record the corrected target beside the original.
  Full entry: dev/LESSONS.md:1375
- **C-22. A dispatched agent writes its deliverable incrementally, never at the end**
  **Rule:** When an agent's deliverable is a file, the brief must require it WRITTEN EARLY as a skeleton and filled incrementally, saving after each answer lands. An agent that researches for its whole budget and leaves the writing to the end returns nothing when the budget runs out, and its research dies with it. A partial dossier is a real deliverable; an unwritten perfect one is not.
  Full entry: dev/LESSONS.md:2297

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev, archive/scripts, dev/ARCHIVE.md:
- CANDIDATE archive/dev/JOURNAL.md  (score 229.482)
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 220.195)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 206.208)
- CANDIDATE dev/ARCHIVE.md  (score 175.178)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 173.637)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 53.345)
- CANDIDATE dev/literature/digest.md  (score 49.067)
- CANDIDATE dev/literature/devlin-II5.md  (score 39.250)
- CANDIDATE dev/literature/terms-2026-08.md  (score 37.237)
- CANDIDATE dev/literature/geology.md  (score 36.329)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
