# LJ-1.624: land CardAboveL, from a recipe with numbers instead of my guesses

## HEAD
head_slot: coder
machine: exclusive

## THE OBLIGATION

Land ONE term into `src/`:

    CardAboveL : <the statement [LJ-1.528] proved>

at **`src/L/CardinalAbove.lagda.md`**, a NEW master, plus one import line in
`src/Everything.lagda.md`.

## OBLIGATION NAMES
obligations = ["src/L/CardinalAbove.lagda.md::CardAboveL"]

**THREE LANDING ATTEMPTS HAVE FAILED AND ALL THREE BRIEFS WERE MINE.**
`[LJ-1.555]` failed on a chapter with an import cycle and a scope too narrow to
commit its own result. `[LJ-1.599]` and `[LJ-1.616]` heap-walled silently at
18.79 s and 19.32 s. **`[LJ-1.622]` has now measured why, and this brief is
written from its recipe rather than from another guess of mine.**

**THE CAUSE, MEASURED.** `[LJ-1.622]`: the 18.79 s and 19.32 s **"matches the
14 s cost of `[LJ-1.526]`'s probe plus a 4 s master, so the landing must not
import that probe"** — `[LJ-1.528]`'s own probe calls it "a 14 s module"
(`agents/tasks/LJ-1-528/Probe528.agda:99`) — **"and must not re-run `make check`
as part of the landing run."**

**AND THE MASTER FITS EASILY ONCE THE INTERFACES ARE WARM.** With the eleven
`src` interfaces warm at `-M2g`, the whole four-part ladder plus the term peaks
at **843,366,400 bytes, 39.3 percent of the cap, in 3.91 s**, leaving **1.3 GB
of headroom**.

**THE THREE THINGS THE RECIPE ORDERS, AND THEY ARE NOT MINE:**

1. **Write scope names BOTH paths**, the master and the one aggregator line,
   because `[LJ-1.555]`'s named neither and its result "was green in its
   worktree and absent from the branch": `git log --all -- src/L/CardinalAbove.lagda.md`
   is empty at `62c52de1`.
2. **Do not import `[LJ-1.526]`'s probe and do not run `make check` in the
   landing run.**
3. **Start with a floor check at the `[LJ-1.559]` discipline.** If the
   worktree's warm floor reads about 766 MB and 3 s as `[LJ-1.622]`'s did, the
   elaboration fits. **If the floor reads far higher, the wall is in that
   worktree's `_build` and not in the term, and you must bisect the build state
   instead of the term again.**

## SCOPE (write)
- src/L/CardinalAbove.lagda.md
- src/Everything.lagda.md
- agents/tasks/LJ-1-624/lj-1.624-report.md
- agents/tasks/LJ-1-624/review-of-CardAboveL-landing.md
- agents/tasks/LJ-1-624/runs/

## PREMISES

1. `[LJ-1.622]` is GO and gives the landing recipe. Basis: agents/tasks/LJ-1-622/lj-1.622-report.md:1
2. `[LJ-1.528]`'s probe calls itself a 14 s module. Basis: agents/tasks/LJ-1-528/Probe528.agda:99
3. `[LJ-1.619]` measured the import closure at 29.5 percent of a `-M2g` cap. Basis: agents/tasks/LJ-1-619/lj-1.619-report.md:1
4. `[LJ-1.555]` measured the import graph over 102 masters. Basis: agents/tasks/LJ-1-555/review-of-CardAboveL-landing.md:56
5. It names both write paths and the corrected obligation. Basis: agents/tasks/LJ-1-555/review-of-CardAboveL-landing.md:81
6. `L.BoundedSubset` imports and instantiates `L.StageCardinal`. Basis: src/L/BoundedSubset.lagda.md:1397
7. `[LJ-1.528]` built `CardAboveL` under `--safe` with no choice. Basis: agents/tasks/LJ-1-528/Probe528.agda:638
8. `[LJ-1.526]` proved the reduction it discharges. Basis: agents/tasks/LJ-1-526/lj-1.526-report.md:1
9. `[LJ-1.559]` established the floor-first discipline. Basis: agents/tasks/LJ-1-559/lj-1.559-report.md:1
10. `make check` is the gate before any commit. Basis: AGENTS.md:74
11. The program commits by explicit path from the task's scope. Basis: AGENTS.md:78
12. No mathematical prose until both trophies are proved. Basis: AGENTS.md:69
13. Chapter style is ruled. Basis: dev/STYLE-agda.md:1

## WHAT IS DELIVERED ALREADY

A `--safe`, choice-free proof in a probe, a measured chapter placement, a
measured import floor, and a measured cause for three failures. **Nothing from
this campaign is in `src/`.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE FLOOR.** Run `[LJ-1.622]`'s floor check
first and report peak RSS and seconds. **About 766 MB and 3 s means proceed.
Far higher means stop and bisect the `_build` state, not the term.**

**DO NOT IMPORT `[LJ-1.526]`'s PROBE.** That is the measured cause of two silent
walls. **If `CardAboveL` cannot be stated without it, say so and stop**: that
would be a different problem than the one measured.

**DO NOT RUN `make check` IN THE LANDING RUN.** `AGENTS.md:74` makes it the gate
before a commit, and the program commits, not you. **Say in your report that you
did not run it and why.**

**WRITE THE REPORT AS A SKELETON FIRST AND FILL IT AS RUNS LAND.** Three
predecessors left almost nothing between them.

**THE PROSE RULE BINDS AND IT IS NARROW.** Write the code and the comments
inside it. A new master gets no chapter introduction.

**`src/Everything.lagda.md` GETS EXACTLY ONE LINE.** Do not reorder it.

**DO NOT LAND ANY OTHER PROBE TERM. DO NOT WEAKEN THE STATEMENT.**

**DO NOT POSTULATE. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE FLOOR, THEN THE TERM`.** Peak RSS and seconds
for each, against `[LJ-1.622]`'s 766 MB / 3 s and 843 MB / 3.91 s.

**REQUIRED REPORT SECTION `## WHAT IS NOW IN SRC`.** The path, the line
count, and the one aggregator line. **If nothing landed, say that plainly.**

ESTIMATE: about 590 lines added to `src/` plus one aggregator line, at about
843 MB and 3.91 s. BASIS: `[LJ-1.622]` measured exactly this ladder.
**That is a measurement and not a comparable**, and it is the first landing
figure this campaign has had.

## W3, THE WIDEST UNMEASURED TERM

It is this worktree's warm floor.

    -- the eleven src interfaces warm, one trivial term, peak RSS and seconds

**Do this FIRST and report both numbers before touching the master.** ESTIMATE:
about 766 MB and 3 s if the worktree matches `[LJ-1.622]`'s.

## WHAT GO AND NO-GO EACH EARN

**A GO PUTS THE FIRST TERM OF THIS CAMPAIGN INTO THE TREE**, after three
failures that were all mine.

**A NO-GO WITH A FLOOR FAR ABOVE 766 MB SAYS THE WALL IS THE WORKTREE'S
`_build`**, which is a different defect from any measured so far and belongs to
the maintainer, not to the mathematics.

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
  changed_files_none = ["agents/tasks/LJ-1-624/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-624/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-624/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-624/Probe624.agda"]
  changed_files_none = ["agents/tasks/LJ-1-624/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-624/review-of-*.md"]

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

MANDATORY for kind `build` (writes a master under src/. The heaviest bundle, because a build is where seconds and lines are actually spent.):

- **P-h. Definability walks are module-parameterized, never function-parameterized**
  **Rule:** A definability walk (the `defSet≡` extensionality of an InL-idiom constructibility lemma) takes its set arguments as parameters of a module, not of a function, and those parameters stay ABSTRACT through the walk: the formulas and the readers never mention a concrete `sett` body (`slice`, `satSet`, a stage over them); the instantiation at real sets happens only at the lemma-assembly le...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:200
- **P-k. A read lemma is stated where its consumers use it, not where its proof ends**
  **The law.** When a lemma exists so that consumers can rewrite with it, its stated right-hand side must be **the form the consumers actually need**, not the form the proof happened to reach. If it stops one layer early, every consumer re-normalizes the missing layer, and the same conversion is paid once per consumer instead of once in total. **Absorb the last layer into the lemma and seal it**,...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2463
- **P-l. A statement may be ABOUT a concrete stage without dragging that stage's PRESENTATION into its type**
  **The law.** Being about a concrete position is not what costs. Naming a transparent construction in a statement's TYPE is. If the tower's stage values are `opaque` upstream, a theorem may quantify over, hypothesize about and conclude at `Sset ω` freely, because the stage is an ATOM to the elaborator and nothing unfolds. If instead the type mentions a transparent presentation, such as `⟪ sucV (...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2367
- **P-m. The check-cost rate is a content-class certificate, and instantiation is the expensive class**
  **Rule:** Seconds per line identify a block's CONTENT CLASS before any profile is run, and line count alone predicts nothing. **Parameterized content**, whose definitions check at bound variables under a module telescope, checks near **0.01 s per line**. **Instantiation content**, which states object-language formulas at a concrete carrier, proves decodes that walk the satisfaction relation, an...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2522
- **P-n. Satisfaction content at a concrete carrier is a payable floor, not a defect**
  **Rule:** When a proof states object-language formulas at a CONCRETE carrier and proves their two-way decodes, the elaborator normalizes the carrier's presentation at every such definition, and **named branches with written types do not remove that cost**. I-5's cure applies to a missing type, not to this; if every hot branch already carries a written type, the remaining cost is the machinery a...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2545
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
  **Rule:** Every agda invocation runs under a GHC heap cap (`GHCRTS=-M<n>g`) so a runaway typecheck dies with a clean "Heap exhausted" exit instead of OOM-killing the machine; the orchestrator's audits run at `-M16g` and `make` exports a default. **OWNER-RULED 2026-08-23, SECOND RULING THE SAME DAY: WIDE and HEAVY split apart again, WIDE smaller and concurrent.** The first ruling that date flatt...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2135
- **D-10. Price the truth of a recorded residue before pricing its proof**
  **Rule:** A residue recorded under the wall protocol names a TARGET, and a target can be false; before dispatching a discharge batch, spend the five minutes checking the target's truth at the intended generality (a Tarskian or cardinality obstruction is the usual killer), and record the corrected target beside the original.
  Full entry: dev/LESSONS.md:1375
- **C-22. A dispatched agent writes its deliverable incrementally, never at the end**
  **Rule:** When an agent's deliverable is a file, the brief must require it WRITTEN EARLY as a skeleton and filled incrementally, saving after each answer lands. An agent that researches for its whole budget and leaves the writing to the end returns nothing when the budget runs out, and its research dies with it. A partial dossier is a real deliverable; an unwritten perfect one is not.
  Full entry: dev/LESSONS.md:2307

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev, archive/scripts, dev/ARCHIVE.md:
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 234.810)
- CANDIDATE archive/dev/JOURNAL.md  (score 224.390)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 224.049)
- CANDIDATE dev/ARCHIVE.md  (score 192.519)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 189.363)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 49.762)
- CANDIDATE dev/literature/devlin-II5.md  (score 45.393)
- CANDIDATE dev/literature/digest.md  (score 42.234)
- CANDIDATE dev/literature/terms-2026-08.md  (score 40.808)
- CANDIDATE dev/literature/formalizations-landscape.md  (score 30.273)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
