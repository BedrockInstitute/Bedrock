# LJ-1.630: land ingredient (iv) in L.BoundedSubset

## HEAD
head_slot: coder
machine: exclusive
agda_tier: heavy

## THE OBLIGATION

Land ONE term into `src/`:

    <ingredient (iv) of `class-pred`, as `[LJ-1.613]`/`[LJ-1.601]`/`[LJ-1.608]`
     proved it and `[LJ-1.625]` sited it>

at **`src/L/BoundedSubset.lagda.md`**.

## OBLIGATION NAMES
obligations = ["src/L/BoundedSubset.lagda.md::class-pred-iv"]

**THE NAME ABOVE IS A PROPOSAL.** `[LJ-1.625]` sited the row but did not name
it. **Choose the name the chapter's style wants and state what you delivered.**

**THREE TERMS ARE NOW IN THE TREE AND THE PATH IS PROVEN.**

| term | host | commit |
|---|---|---|
| `least-at-site` | `L.StageCardinal` | `612fa31f` |
| `CardAboveL` | `L.CardinalAbove` (new master) | `3c229d2d` |
| `class-pred-i` | `L.Constructible` | `3fb69c02` |

**AND THE COST IS NOW UNDERSTOOD, WHICH IT WAS NOT FOR THE FIRST FIVE
ATTEMPTS.** It tracks how many masters depend on the host, counted by
`grep -rl "import <host>" src/`:

| host | dependents | what it cost |
|---|---|---|
| `L.Constructible` | **71** | heap-walled HEAVY warm, 4.38 GiB, needed an 8 GB manual run |
| `L.BoundedSubset` | 3 | not yet measured |
| `L.Choice.Faithful` | 2 | not yet measured |
| `L.StageCardinal` | 2 | landed at 21.9 percent of a 2 GB cap |

**YOUR HOST HAS 3 DEPENDENTS, THE SAME CLASS AS THE ONE THAT LANDED EASILY
AND NOT THE ONE THAT NEEDED 8 GB.** That is the reason this brief is HEAVY and
not superheavy. **If it walls anyway, that refutes the reading and you must say
so with the numbers.**

**`[LJ-1.625]` SITED THIS ONE.** It measured the host already imports every name the statement opens and already instantiates the site (`src/L/BoundedSubset.lagda.md:882` and `:1397`), with NO new import lines.

## MEASURED TODAY

- dependents: L.BoundedSubset => 3
- supply: rec-graph => 0

## SCOPE (write)
- src/L/BoundedSubset.lagda.md
- agents/tasks/LJ-1-630/lj-1.630-report.md
- agents/tasks/LJ-1-630/review-of-class-pred-iv.md
- agents/tasks/LJ-1-630/runs/

## PREMISES

1. `[LJ-1.625]` is GO and sites the four ingredients. Basis: agents/tasks/LJ-1-625/lj-1.625-report.md:1
2. Its probe carries this ingredient's siting. Basis: agents/tasks/LJ-1-625/Probe625.agda:107
3. `least-at-site` is in the tree. Basis: src/L/StageCardinal.lagda.md:271
4. `CardAboveL` is in the tree. Basis: src/L/CardinalAbove.lagda.md:1
5. `class-pred-i` is in the tree. Basis: src/L/Constructible.lagda.md:1
6. `[LJ-1.613]` proved ingredients (i) and (ii). Basis: agents/tasks/LJ-1-613/Probe613.agda:137
7. `[LJ-1.601]` proved (iv)'s base. Basis: agents/tasks/LJ-1-601/lj-1.601-report.md:1
8. `[LJ-1.608]` proved (iv)'s limit. Basis: agents/tasks/LJ-1-608/lj-1.608-report.md:1
9. `[LJ-1.600]` proved (v). Basis: agents/tasks/LJ-1-600/lj-1.600-report.md:1
10. `[LJ-1.622]` found importing a probe is what walls a landing. Basis: agents/tasks/LJ-1-528/Probe528.agda:99
11. `make check` is the gate before any commit. Basis: AGENTS.md:74
12. The program commits by explicit path from the task's scope. Basis: AGENTS.md:78
13. No mathematical prose until both trophies are proved. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

Three terms in `src/`, a measured siting for this one, and a cost model that
tracks the host's dependent count. **This ingredient is still only in a probe.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE FLOOR AT HEAVY.** Typecheck `src/L/BoundedSubset.lagda.md`
UNCHANGED at `-M4g` and record peak RSS and seconds. **That is your baseline and
the campaign does not have it for this chapter.**

**DO NOT IMPORT ANY PROBE.** `[LJ-1.622]` measured that importing a 14 s probe
is what walled two landings. **RE-STATE the term in the chapter.** This reverses
R-42's usual advice on purpose; `[LJ-1.626]` did it successfully. **Say you did
it and why.**

**DO NOT RUN `make check` IN THE LANDING RUN.** The program commits, not you.

**DO NOT ADD AN IMPORT LINE.** `[LJ-1.625]` measured the opens this row needs
are already the host's. **If you need one, that refutes its siting: stop and say
so**, because it would matter for the remaining ingredient too.

**THE PROSE RULE BINDS.** The row and its comments, nothing else.

**NEVER RETURN A PLACEHOLDER.** Fill each report cell as it lands.

**DO NOT LAND ANY OTHER INGREDIENT.** AD12 gives this brief one obligation.

**DO NOT POSTULATE. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE FLOOR, THEN THE ROW`.** Peak RSS and seconds
for the chapter unchanged, then with the row, both at HEAVY.

**REQUIRED REPORT SECTION `## DID THE DEPENDENT COUNT PREDICT IT`.** Two
sentences. Your host has 3 dependents against `L.Constructible`'s 71.
**Say whether the cost tracked that**, because the next landing is priced on it.

**REQUIRED REPORT SECTION `## WHAT IS NOW IN SRC`.** Path, name, line count,
and whether any import or `using` changed.

ESTIMATE: about 15 lines added to `src/L/BoundedSubset.lagda.md`. BASIS: `[LJ-1.626]` landed a
sibling row in eight in-fence lines plus comments. Comparables are of SHAPE and
nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the host's own current cost at HEAVY.

    -- src/L/BoundedSubset.lagda.md UNCHANGED, typechecked at -M4g, peak RSS and seconds

**Do this FIRST and report both numbers before touching the file.**

## WHAT GO AND NO-GO EACH EARN

**A GO PUTS A FOURTH TERM IN THE TREE** and tests the dependent-count cost model
on a second host.

**A NO-GO THAT WALLS AT A LOW DEPENDENT COUNT REFUTES THAT MODEL**, which the
mathematician needs before pricing any further landing.

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
  changed_files_none = ["agents/tasks/LJ-1-630/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-630/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-630/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-630/Probe630.agda"]
  changed_files_none = ["agents/tasks/LJ-1-630/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-630/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 183.612)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 172.664)
- CANDIDATE archive/dev/JOURNAL.md  (score 157.703)
- CANDIDATE dev/ARCHIVE.md  (score 145.041)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 138.789)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 42.655)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 35.626)
- CANDIDATE dev/literature/digest.md  (score 32.250)
- CANDIDATE dev/literature/terms-2026-08.md  (score 30.026)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 25.327)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
