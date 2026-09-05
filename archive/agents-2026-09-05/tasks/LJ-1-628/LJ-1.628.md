# LJ-1.628: land ingredient (i) in L.Constructible, the second landing

## HEAD
head_slot: coder
machine: exclusive
agda_tier: heavy

## THE OBLIGATION

Land ONE term into `src/`:

    <ingredient (i) of `class-pred`, as `[LJ-1.613]` proved it and
     `[LJ-1.625]` sited it>

at **`src/L/Constructible.lagda.md`**.

## OBLIGATION NAMES
obligations = ["src/L/Constructible.lagda.md::class-pred-i"]

**THE NAME ABOVE IS A PROPOSAL.** `[LJ-1.625]` sited the row but did not name
it. **Choose the name the chapter's style wants, put the real one in your
report's first line, and state the obligation you delivered.**

**THE LANDING PATH IS PROVEN NOW, AND IT WAS NOT YESTERDAY.** `[LJ-1.626]`
landed `least-at-site` into `src/L/StageCardinal.lagda.md` and `[LJ-1.599]`
landed `CardAboveL` into a new master; both are committed. **Five landing
attempts failed before those two, and none of the failures was the mathematics:**
the whole-tree conjunct on `src/Everything.lagda.md` walls at HEAD ALONE under
WIDE, 1.88 GB against a 2 GB cap, with no task's content in it. **The owner
ruled HEAVY for any task whose scope touches a wired master, and this brief
declares `agda_tier: heavy` from the start.**

**`[LJ-1.625]` SITED THIS ONE AND IT NEEDS NOTHING NEW.**

> **(i)** — host `L.Constructible` (`Section-1`, `agents/tasks/LJ-1-625/Probe625.agda:107-119`;
> **every open is one of its own lines**, `src/L/Constructible.lagda.md:29-37`).
> **New import lines: none.**

**AND IT CARRIES A BLOCKER YOU MUST NOT WALK INTO.** The natural-looking home,
`L.Definability`, is a CYCLE: the rows need `Lset` and `𝒟ₒ` from
`L.Constructible`, and `L.Constructible` already imports `L.Definability`
(`src/L/Constructible.lagda.md:37`). **`L.Constructible` is the host. Do not
move it.**

## SCOPE (write)
- src/L/Constructible.lagda.md
- agents/tasks/LJ-1-628/lj-1.628-report.md
- agents/tasks/LJ-1-628/review-of-class-pred-i.md
- agents/tasks/LJ-1-628/runs/

## PREMISES

1. `[LJ-1.625]` is GO and sites ingredient (i) at `L.Constructible`. Basis: agents/tasks/LJ-1-625/Probe625.agda:107
2. Every open it needs is already one of the host's lines. Basis: src/L/Constructible.lagda.md:29
3. `L.Definability` is a cycle for this row. Basis: src/L/Constructible.lagda.md:37
4. `[LJ-1.613]` proved ingredient (i). Basis: agents/tasks/LJ-1-613/Probe613.agda:137
5. `[LJ-1.626]` landed the sibling row at a wired master. Basis: agents/tasks/LJ-1-626/lj-1.626-report.md:1
6. `least-at-site` is in the tree. Basis: src/L/StageCardinal.lagda.md:271
7. `CardAboveL` is in the tree. Basis: src/L/CardinalAbove.lagda.md:1
8. `[LJ-1.622]` found importing a probe is what walls a landing. Basis: agents/tasks/LJ-1-528/Probe528.agda:99
9. `[LJ-1.619]` measured the import closure well under cap. Basis: agents/tasks/LJ-1-619/lj-1.619-report.md:1
10. `make check` is the gate before any commit. Basis: AGENTS.md:74
11. The program commits by explicit path from the task's scope. Basis: AGENTS.md:78
12. No mathematical prose until both trophies are proved. Basis: AGENTS.md:69
13. Chapter style is ruled. Basis: dev/STYLE-agda.md:1

## WHAT IS DELIVERED ALREADY

Two terms in `src/`, a measured siting for this one, and a proven landing
procedure. **Ingredient (i) is still only in a probe.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE FLOOR.** Typecheck
`src/L/Constructible.lagda.md` UNCHANGED at HEAVY and record peak RSS and
seconds. **That is your baseline.** `[LJ-1.626]` read 1.37 s and 322 MB for its
own host at WIDE; **this chapter is bigger and you are at `-M4g`, so report what
you actually see rather than expect that.**

**DO NOT IMPORT ANY PROBE.** `[LJ-1.622]` measured that importing a 14 s probe
is what walled two landings. **Take the term from `[LJ-1.613]` by RE-STATING it
in the chapter.** This is the one place where re-typing beats importing, against
R-42's usual advice, and `[LJ-1.626]` did it successfully: **say in your report
that you did it and why.**

**DO NOT RUN `make check` IN THE LANDING RUN.** It is the gate before a commit
and the program commits. **Say you did not run it.**

**DO NOT ADD AN IMPORT LINE.** `[LJ-1.625]` measured that every open this row
needs is already one of the host's. **If you find you need one, that refutes its
siting: say so and stop.**

**THE PROSE RULE BINDS.** The row and the comments inside it, nothing else.

**WRITE THE REPORT AS A SKELETON AND FILL EACH CELL AS IT LANDS. NEVER RETURN A
PLACEHOLDER.**

**DO NOT LAND (iv) OR (v).** AD12 gives this brief one obligation, and they are
sited for later briefs.

**DO NOT POSTULATE. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE FLOOR, THEN THE ROW`.** Peak RSS and seconds
for the chapter unchanged, then with the row, both at HEAVY.

**REQUIRED REPORT SECTION `## WHAT IS NOW IN SRC`.** The path, the row's name,
the line count, and whether any import or `using` changed. **If nothing landed,
say so plainly.**

ESTIMATE: about 15 lines added to `src/L/Constructible.lagda.md`. BASIS:
`[LJ-1.626]` landed the sibling row in eight in-fence lines plus comments.
Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the host chapter's own current cost at HEAVY.

    -- src/L/Constructible.lagda.md UNCHANGED, typechecked at -M4g, RSS and seconds

**Do this FIRST and report both numbers before touching the file.**

## WHAT GO AND NO-GO EACH EARN

**A GO PUTS A THIRD TERM IN THE TREE** and confirms that `[LJ-1.625]`'s siting
generalises past the one row it was tested on.

**A NO-GO NEEDING A NEW IMPORT REFUTES THAT SITING**, which would matter for
(iv) and (v) too and should be reported as such.

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
  changed_files_none = ["agents/tasks/LJ-1-628/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-628/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-628/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-628/Probe628.agda"]
  changed_files_none = ["agents/tasks/LJ-1-628/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-628/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 231.749)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 216.705)
- CANDIDATE archive/dev/JOURNAL.md  (score 195.276)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 177.052)
- CANDIDATE dev/ARCHIVE.md  (score 176.242)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 55.366)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 50.225)
- CANDIDATE dev/literature/digest.md  (score 43.847)
- CANDIDATE dev/literature/terms-2026-08.md  (score 39.629)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 35.600)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
