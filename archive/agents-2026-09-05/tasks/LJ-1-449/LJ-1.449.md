# LJ-1.449: state the truncated route's one open statement ONCE, in the tree

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Land ONE term in `src/L/StageBound.lagda.md`, the master `[LJ-1.442]` creates:

    bounded-modulo-collect : SqCollect α → ⟨ x ∈ˢ Lset κ ⟩

where `SqCollect` is stated in that same chapter, once, as the only thing the
TRUNCATED route still owes:

    SqCollect : S → Type (ℓ-suc ℓ)
    SqCollect α =
        ((δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq δ ∥₁)
      → ∥ SqFam α ∥₁

`SqFam` is already in the chapter, landed by `[LJ-1.442]`. The body feeds
`L.SquareLawClosed`'s landed `sq-trunc-closed` into `SqCollect`'s hypothesis,
then hands the result to the chapter's own `bounded-from-trunc`. **It proves no
new mathematics. It states, in the tree, exactly what is left.**

**READ TWO REPORTS BEFORE ANYTHING ELSE, AND STOP IF EITHER FAILS ITS TEST:**

- `agents/tasks/LJ-1-442/lj-1.442-report.md`. If it does not exist, or its
  verdict is not `GO`, or `src/L/StageBound.lagda.md` is not in the tree, write
  nothing and stop.
- `agents/tasks/LJ-1-445/lj-1.445-report.md`. If it does not exist, or its
  verdict is not `GO`, or `src/L/SquareLawClosed.lagda.md` is not in the tree,
  write nothing and stop.

Say in your report which test failed. **THIS TASK SUPERSEDES `[LJ-1.443]`,
WHICH NAMES THE SAME OBLIGATION AND GATES ON `[LJ-1.440]`.** `[LJ-1.440]` never
wrote into this tree, so that gate can only fail. Do not read `[LJ-1.443]`'s
brief and do not take a type from it.

## OBLIGATION NAMES
obligations = ["src/L/StageBound.lagda.md::bounded-modulo-collect"]

## SCOPE (write)
- src/L/StageBound.lagda.md
- dev/ledger.toml
- agents/tasks/LJ-1-449/lj-1.449-report.md
- agents/tasks/LJ-1-449/review-of-bounded-modulo-collect.md
- agents/tasks/LJ-1-449/runs/
- `src/Everything.lagda.md` (R18, program-generated: wire the master here, because acceptance conjunct 3 refuses a catalog that does not import it)

## PREMISES

1. The supply half is `sq-trunc-closed` with an EMPTY hypothesis telescope, and `[LJ-1.445]` lands it. Basis: agents/tasks/LJ-1-437/Probe437.agda:345
2. `[LJ-1.437]` is GO on that supply half. Basis: agents/tasks/LJ-1-437/lj-1.437-report.md:17
3. The consumer half is `bounded-from-trunc`, and `[LJ-1.442]` lands it. Basis: agents/tasks/LJ-1-434/Probe434.agda:127
4. `[LJ-1.434]` is GO on that consumer half. Basis: agents/tasks/LJ-1-434/lj-1.434-report.md:51
5. The gap between them is already named as a type by the coder who found it, and it is not inhabited there. Basis: agents/tasks/LJ-1-434/Probe434.agda:56
6. The one site in `src/` that demands the family as DATA is `limit-step`'s last argument. Basis: src/L/StageCardinal.lagda.md:397
7. The cross-count a truncated branch family would need is refuted green at a second site in this tree. Basis: agents/tasks/LJ-1-408/Probe408.agda:95
8. `[LJ-1.391]` proves this residue EQUIVALENT to a `2-Constant` endomap over the band, and records that paying the endomap is not a cheaper target. Basis: agents/tasks/LJ-1-391/lj-1.391-report.md:56
9. The exact criterion is Kraus, Escardo, Coquand and Altenkirch, Theorem 16: split support if and only if a weakly constant endomap. Basis: dev/literature/truncation-and-selection.md:158
10. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
11. The architecture is a CANDIDATE and only a measurement settles it. Basis: dev/pod/screen.toml:10
12. `make check` is the gate before any commit. Basis: AGENTS.md:75
13. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69
14. One SRC collection after LJ-1. Basis: dev/pod/direction.md:37

## WHAT IS DELIVERED ALREADY

Both sides of the statement are proved and, after `[LJ-1.445]` and
`[LJ-1.442]`, both sit in `src/`.

- **The supply.** `[LJ-1.437]` is GO on `sq-trunc-closed` at a GENERIC band
  with NO module hypothesis (`agents/tasks/LJ-1-437/Probe437.agda:345-348`).
  That is the domain of `SqCollect`, inhabited outright.
- **The consumer.** `[LJ-1.434]` is GO on `bounded-from-trunc`
  (`agents/tasks/LJ-1-434/Probe434.agda:127-128`). That takes the codomain of
  `SqCollect` to the bounded-subset lemma's conclusion.

## WHAT IS MISSING

**THE STATEMENT BETWEEN THEM HAS NEVER BEEN WRITTEN IN ONE PLACE.** It is
`Distance` in one probe (`agents/tasks/LJ-1-434/Probe434.agda:56-64`) and
`EndomapAt` in another (`agents/tasks/LJ-1-391/Probe391.agda:153-156`). Two
names, two probe files, no chapter. `[LJ-2.5]` cannot rule on a statement that
lives in scattered probes under different names.

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE WHOLE RISK OF THIS TASK.**

The two landed terms were written by different tasks against different
notations, and **no file in this tree has ever held both**. Quote both types at
`file:line` before you write a line of the obligation:

- `sq-trunc-closed` quantifies `(δ : V ℓ)` and reads membership as `∈`
  (`agents/tasks/LJ-1-437/Probe437.agda:345-348`).
- `SqFam` quantifies `(δ : S)` and reads membership as `∈ˢ`
  (`agents/tasks/LJ-1-434/Probe434.agda:44-48`).

**Say whether the two are the same type, definitionally, and give the evidence
at `file:line`.** If they are, the composition is direct. If they are not, say
exactly what stands between them and DO NOT hide it inside a `subst`: name the
repackaging in a section `## WHAT THE JOIN COST`, and report it as a finding.

**THE SHAPE.**

1. Add `import L.SquareLawClosed` to `src/L/StageBound.lagda.md`. That master
   is registered before this one, so the import is legal. Check the two line
   numbers in `src/Everything.lagda.md` and quote them.
2. State `SqCollect` in the chapter, at the shape above, generic in `α`.
3. Build `bounded-modulo-collect`: apply the hypothesis to `sq-trunc-closed`,
   then apply `bounded-from-trunc` to the result.
4. Update `dev/ledger.toml`.

**DO NOT INHABIT `SqCollect` AND DO NOT POSTULATE IT.** It is a module
parameter of the obligation and nothing else. An axiom, an `AC`-shaped
postulate or a `--safe`-off escape is a STOP and not a route. DD9 says a new
principle is stated as a type.

**DO NOT CLAIM THAT `SqCollect` IS FALSE.** Nothing in this tree refutes it.
What is refuted is a route to it (`agents/tasks/LJ-1-408/Probe408.agda:95-104`).

**A SECOND ROUTE IS OPEN AND THIS TASK DOES NOT DECIDE BETWEEN THEM.**
`[LJ-1.447]` and `[LJ-1.448]` state the same counting leg's residue as a
statement about two ordinals instead of a choice principle. **Name that in one
sentence in `## WHAT IS LEFT` and do not rank the two.** The ranking is
`[LJ-2.5]`'s and it is the owner's.

**PROSE IS FROZEN.** Write the chapter's code and the comments inside it. Write
no mathematical prose and no narrative section (`AGENTS.md:69`).

**THE RATIO BAR IS LIVE.** The bar is 0.0123 seconds per in-fence line and the
divisor is the non-blank line count inside the ` ```agda ` fences of your write
scope. This task adds few lines to a chapter `[LJ-1.442]` already measured, so
expect the escalation. Do not pad. **Report the two numbers in a section
`## THE RATIO`.**

**W2 (DD4).** `SqCollect` is written once, generic in `α`. Name no band, no
numeral and no site.

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 25 in-fence lines added. BASIS: the composition is
two applications and one type definition; the delivered comparable of SHAPE is
`agents/tasks/LJ-1-420/Probe420.agda:97-99`, where a whole assembly term is
three lines under a stated telescope. Comparables are of SHAPE and never of
size, and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is whether the two landed types MEET with no repackaging:

    domains-meet :
        ((δ : V ℓ) → ⟨ δ ∈ sucV α ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥) → ∥ sq δ ∥₁)
      → ((δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq δ ∥₁)

**Write it as the identity function, typecheck it ALONE with the obligation
omitted from the chapter, and report the result.** If it checks as the
identity, the join is free and you say so. If it does not, the elaborator's
error at `file:line` IS the finding, and it is worth more than the obligation:
it says the campaign's supply half and consumer half have been stating one
family two ways for fifty dispatches.

ESTIMATE for W3: three lines and under one second on top of the chapter's own
cost. BASIS: it is an identity function between two spellings of one telescope.

Report the median wall time and peak RSS over three forced rechecks at the
pane's caliber, and run `make check` before and after the chapter changes.

## WHAT GO AND NO-GO EACH EARN

**A GO GIVES `[LJ-2.5]` ONE TYPE TO RULE ON.** It says, as a term in the tree,
that the bounded-subset lemma's conclusion follows from `SqCollect` alone, with
the supply half already proved unconditionally.

**A NO-GO IS WORTH AS MUCH.** It says either a premise is not in the tree, or
the two halves do not meet, or the gate refuses the join. The second is the
most valuable outcome this task can produce and the brief asks for it by name.

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
# A D-10 STOP RUNS NO AGDA, SO IT EXITS 0 AND MATCHES NO exit_code 42 BRANCH.
# `[LJ-1.440]` parked `no-match` seven times for exactly this gap
# (dev/pod/transitions/2026-08.jsonl:832). A stated NO-GO is the critic's
# input and never a close, so this routes to the critic and the critic's
# return closes the task.
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-449/review-of-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["src/L/StageBound.lagda.md"]
  changed_files_none = ["agents/tasks/LJ-1-449/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-449/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 187.854)
- CANDIDATE archive/dev/JOURNAL.md  (score 185.788)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 173.451)
- CANDIDATE archive/dev/DD-archived.md  (score 171.267)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 169.538)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 57.045)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 56.261)
- CANDIDATE dev/literature/digest.md  (score 41.113)
- CANDIDATE dev/literature/geology.md  (score 40.858)
- CANDIDATE dev/literature/terms-2026-08.md  (score 36.095)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
