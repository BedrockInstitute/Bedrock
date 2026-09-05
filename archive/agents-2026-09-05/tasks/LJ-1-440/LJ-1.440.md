# LJ-1.440: land the truncated square law in the tree

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Land ONE term in a NEW master, `src/L/SquareLawClosed.lagda.md`:

    sq-trunc-closed :
        (α₀ : V ℓ) → IsOrd α₀
      → (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
      → ∥ sq δ ∥₁

and register the chapter in `src/Everything.lagda.md`, on the line after
`import L.Cardinal` (`src/Everything.lagda.md:375`).

**READ `agents/tasks/LJ-1-437/lj-1.437-report.md` BEFORE ANYTHING ELSE. IF THAT
FILE DOES NOT EXIST, OR ITS VERDICT IS NOT `GO`, WRITE NOTHING AND STOP.** Say
in your report which of the two happened. This task has one premise and that
report is it. A landing built on a report you cannot open is the defect the
independent audit of 2026-08-20 measured twice
(`dev/pod/audit-2026-08-20.md:34`).

## OBLIGATION NAMES
obligations = ["src/L/SquareLawClosed.lagda.md::sq-trunc-closed"]

## SCOPE (write)
- src/L/SquareLawClosed.lagda.md
- src/Everything.lagda.md
- dev/ledger.toml
- agents/tasks/LJ-1-440/lj-1.440-report.md
- agents/tasks/LJ-1-440/review-of-sq-trunc-closed.md

## PREMISES
- `[LJ-1.437]` is the only supplier of this term, and its report is the premise. Basis: agents/tasks/LJ-1-437/LJ-1.437.md:9
- A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
- The chapter that defines `sq` cannot hold this term: it is imported by the cardinal chapter. Basis: src/L/Cardinal.lagda.md:22
- So the home is a new master after the cardinal chapter in the build order. Basis: src/Everything.lagda.md:375
- The consumer of a square law sits later in that order. Basis: src/Everything.lagda.md:387
- The chapter already exports the truncated form UNDER `Init`, and this term is the same shape without that hypothesis. Basis: src/L/Ordinal/SquareLaw.lagda.md:963
- `make check` is the gate before any commit. Basis: AGENTS.md:75
- No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69
- The size ledger is the only admissible source for a standing size figure. Basis: AGENTS.md:17
- The architecture is a CANDIDATE and only a measurement settles it. Basis: dev/pod/screen.toml:10

## WHAT IS DELIVERED ALREADY

`[LJ-1.437]` is asked for exactly this term with an EMPTY hypothesis telescope,
in `agents/tasks/LJ-1-437/Probe437.agda`. Its report records the joined file's
median wall time and peak RSS, and this task is priced against those numbers
and not against an estimate.

## WHAT IS MISSING

**THE TERM IS IN `agents/` AND THE TREE CANNOT USE IT.** A probe is not a
library. Until the term sits under `src/` and `Everything` imports it, no
master can read it and no trophy can be wired to it.

## THE REASONING

**D-10, BEFORE ANY AGDA.** Open `agents/tasks/LJ-1-437/lj-1.437-report.md`,
quote its VERDICT line at `file:line`, and quote the type it says it inhabited.
**If the verdict is not `GO`, stop there and report.** If the type differs from
the obligation above, say where and STOP; do not repair a mismatch by weakening
the obligation.

**THE SHAPE.**

1. Create `src/L/SquareLawClosed.lagda.md` with the chapter header the style
   guide requires (`dev/STYLE-agda.md`, `dev/STYLE-i18n.md`).
2. Move `[LJ-1.437]`'s file into it. The probe's module parameters `α₀` and
   `oα₀` become arguments of the landed term, so the chapter's module takes
   `{ℓ}` and `lem` only.
3. Add `import L.SquareLawClosed` to `src/Everything.lagda.md` after
   `import L.Cardinal`.
4. Update `dev/ledger.toml` for the new master.

**PROSE IS FROZEN AND THIS TASK DOES NOT BREAK THE FREEZE.** Write the chapter
title, the code, and the comments inside the code. **Write no mathematical
prose and add no `<!--en-->` narrative section.** The Boundary clause is
`AGENTS.md:69`. If the style checks demand a prose block that this freeze
forbids, that conflict is a STOP: name the two rules at `file:line` and report.

**THE RATIO BAR IS LIVE AND THIS IS THE TASK THAT MEETS IT.** The bar is
0.0123 seconds per in-fence line, and its divisor is the non-blank line count
inside the ` ```agda ` fences of your write scope. `[LJ-1.437]`'s probe carried
no fence and counted zero; this chapter carries them all. A green return at or
above the bar is ESCALATED to a critic, which is a review and not a failure.
**Report the two numbers, the measured seconds and the in-fence line count, in
a section `## THE RATIO`, so the critic does not have to recompute them.**

**W2 (DD4).** The landed term stays generic in `ℓ`, in `α₀` and in `δ`. Name no
band, no numeral and no site.

**W3, THE WIDEST UNMEASURED TERM.** It is `make check` over the whole tree with
one new master in the import graph:

    make check

**THE PROBE.** Run `make check` ONCE before you write anything, and record its
wall time. That is the baseline. Run it again after the chapter lands, and
report the difference. The unmeasured term is what one more master costs the
gate, and it is unmeasured because this campaign has landed nothing in `src/`.
While you work, run the individual checks and not the whole gate
(`AGENTS.md:75`). A heap event is a WALL event: report it and stop.

**NEVER COMMIT AND NEVER PUSH.** Leave the working tree exactly as your report
describes it. The program commits, by explicit path from this task's scope.

**C-42.** In a section `## WHAT THIS DOES NOT MEASURE`, say plainly that
landing the SUPPLY of the truncated square law measures nothing about the
CONSUMER. Name at `file:line` the consumer's module parameter
(`src/L/StageCardinal.lagda.md:17-20`), which is untruncated today, and say
that this task does not change it.

ESTIMATE for the Agda: about 240 in-fence lines. BASIS: `[LJ-1.437]`'s
estimate, itself taken from two delivered comparables of SHAPE,
`agents/tasks/LJ-1-406/Probe406.agda` at 117 non-blank non-comment lines and
`agents/tasks/LJ-1-407/Probe407.agda` at 176. **Replace this estimate with
`[LJ-1.437]`'s MEASURED line count as soon as you have opened its report, and
say in the report that you did.** Comparables of SHAPE and never of size, and
nothing may be funded against them.

## WHAT GO AND NO-GO EACH EARN

**A GO PUTS THE FIRST TERM OF THIS CAMPAIGN IN THE TREE.** It says the
truncated square law holds at every infinite band ordinal, in `src/`, with an
empty hypothesis telescope, and `make check` is green. Say in the report what
the gate cost before and after.

**A NO-GO IS WORTH AS MUCH.** It says either the premise is not in the tree,
or the gate refuses one more master, or the prose freeze and the style checks
conflict. Each of those is a fact the campaign needs before it lands anything
else, and it names the file and the line.

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
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["src/L/SquareLawClosed.lagda.md"]
  changed_files_none = ["agents/tasks/LJ-1-440/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-440/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 214.986)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 201.817)
- CANDIDATE archive/dev/JOURNAL.md  (score 194.504)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 175.999)
- CANDIDATE dev/ARCHIVE.md  (score 174.008)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 49.590)
- CANDIDATE dev/literature/devlin-II5.md  (score 49.168)
- CANDIDATE dev/literature/digest.md  (score 42.320)
- CANDIDATE dev/literature/terms-2026-08.md  (score 40.157)
- CANDIDATE dev/literature/geology.md  (score 34.092)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
