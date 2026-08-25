# LJ-1.444: land the ambient route's endpoint, with its one residue named

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Land ONE term in `src/L/StageBound.lagda.md`, the master `[LJ-1.442]` creates:

    chain-upper :
        AmbToCoded
      → (δ : V ℓ) → IsOrd δ → ⟨ δ ∈ˢ sucV α₀ ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
      → ⟪ Lset δ ⟫ ↪ ⟪ δ ⟫

where `AmbToCoded` is stated in the same chapter, once, at the type
`[LJ-1.414]` delivered (`agents/tasks/LJ-1-414/Probe414.agda:134-139`):

    AmbToCoded : Type (ℓ-suc ℓ)
    AmbToCoded =
        (x : S) (ox : IsOrd (fst x)) → ⟨ ω ∈ˢ fst x ⟩
      → (d : S) → ⟨ fst d ∈ˢ fst x ⟩ → (⟨ fst d ∈ˢ ω ⟩ → Empty.⊥)
      → ∥ ⟪ fst x ⟫ ↪ ⟪ fst d ⟫ ∥₁
      → ∥ Σ[ F ∈ S ] InjCode F x d ∥₁

**READ `agents/tasks/LJ-1-442/lj-1.442-report.md` BEFORE ANYTHING ELSE. IF
THAT FILE DOES NOT EXIST, OR ITS VERDICT IS NOT `GO`, OR
`src/L/StageBound.lagda.md` IS NOT IN THE TREE, WRITE NOTHING AND STOP.** Say
in your report which of the three happened.

**THIS TASK DOES NOT DEPEND ON `[LJ-1.441]` AND MUST NOT WAIT FOR IT.**
`[LJ-1.441]` asks whether `AmbToCoded` can be discharged at the ONE site the
chain uses. Whatever it returns, the right landing today is the term under its
named hypothesis. If `[LJ-1.441]` returns GO, a later brief discharges the
parameter; that is a change to this chapter, not to this obligation.

## OBLIGATION NAMES
obligations = ["src/L/StageBound.lagda.md::chain-upper"]

## SCOPE (write)
- src/L/StageBound.lagda.md
- dev/ledger.toml
- agents/tasks/LJ-1-444/lj-1.444-report.md
- agents/tasks/LJ-1-444/review-of-chain-upper.md
- agents/tasks/LJ-1-444/runs/
- `src/Everything.lagda.md` (R18, program-generated: wire the new master here, because acceptance conjunct 3 refuses a catalog that does not import it)

## PREMISES

1. `[LJ-1.420]` built exactly this term in a probe, under exactly this one hypothesis, and it is green. Basis: agents/tasks/LJ-1-420/Probe420.agda:97
2. The hypothesis is taken from the probe that typechecked, never from a brief. Basis: agents/tasks/LJ-1-414/Probe414.agda:134
3. `[LJ-1.414]` is a NO-GO on that name: HALF A has no producer at a generic pair, and the term is a hole. Basis: agents/tasks/LJ-1-414/Probe414.agda:139
4. HALF B of the same statement is green and is not the block. Basis: agents/tasks/LJ-1-414/Probe414.agda:115
5. The conclusion is the consumer chapter's own delivered statement, not a new claim. Basis: src/L/StageCardinal.lagda.md:564
6. `L.StageCardinal` sits before `L.BoundedSubset` in the build order, so a master after the latter can read both. Basis: src/Everything.lagda.md:393
7. A predecessor taken as a hypothesis is the REPORT and never the brief; a report that names its statement FALSE may not become a hypothesis. Basis: dev/pod/audit-2026-08-20.md:34
8. Three probes each sealed their own `κL`, and direct application needs an explicit `unfolding`. Basis: dev/pod/audit-2026-08-20.md:128
9. The architecture is a CANDIDATE and only a measurement settles it. Basis: dev/pod/screen.toml:10
10. `make check` is the gate before any commit. Basis: AGENTS.md:75
11. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69
12. One SRC collection after LJ-1. Basis: dev/pod/direction.md:37

## WHAT IS DELIVERED ALREADY

**THE WHOLE AMBIENT ROUTE IS ASSEMBLED AND GREEN IN A PROBE.**
`[LJ-1.420]`'s `chain-upper` (`agents/tasks/LJ-1-420/Probe420.agda:97-99`) IS
`L.StageCardinal`'s own `stage-card-upper`, reached by instantiating that
module with `[LJ-1.413]`'s pairing, under exactly one named hypothesis
(`agents/tasks/LJ-1-420/Probe420.agda:75-96`). Read
`agents/tasks/LJ-1-420/lj-1.420-report.md` and quote its VERDICT line before
you rely on that sentence.

The independent audit reports the same chain compiling from the other end and
names one mechanical repair, an explicit `unfolding` where three probes each
sealed their own `κL` (`dev/pod/audit-2026-08-20.md:128-145`). `[LJ-1.420]`
postdates that audit's scope. **Check whether the repair is already inside
`[LJ-1.420]`'s file, and say so at `file:line` either way.**

## WHAT IS MISSING

**THE ROUTE'S ENDPOINT IS IN `agents/` AND ITS RESIDUE HAS NO NAME IN THE
TREE.** A probe is not a library. Today the sentence "the ambient route needs
exactly one more statement" rests on reading two probe files. After this task
it is a chapter: one named type, one term that consumes it, and the consumer's
own conclusion on the other side.

That is what `[LJ-2.5]` reads. With `[LJ-1.443]`, the tree will hold BOTH
routes' endpoints and BOTH residues as types, in one chapter, and the
architecture ruling becomes a comparison of two named statements instead of a
survey of fifty probes.

## THE REASONING

**D-10, BEFORE ANY AGDA.**

1. Open `agents/tasks/LJ-1-420/lj-1.420-report.md`. Quote its VERDICT line at
   `file:line` and quote the hypothesis type it says it took. If the verdict is
   not `GO`, stop and report.
2. Open `agents/tasks/LJ-1-414/lj-1.414-report.md`. Quote its VERDICT line.
   **It is a NO-GO.** That is why `AmbToCoded` enters this chapter as a
   PARAMETER and never as a term. Write that sentence in your report.
3. Compare `[LJ-1.420]`'s hypothesis type against `[LJ-1.414]`'s delivered type
   projection for projection, in a table, as `[LJ-1.437]`'s report does at
   `agents/tasks/LJ-1-437/lj-1.437-report.md:62-70`. If any projection
   differs, say where and STOP; do not repair a mismatch by weakening either
   side.

**THE SHAPE.**

1. Add the imports `[LJ-1.420]`'s probe uses to `src/L/StageBound.lagda.md`.
2. State `AmbToCoded` once, at the type above.
3. Move `[LJ-1.420]`'s file into the chapter. The probe's module parameters
   `α₀` and `oα₀` stay module parameters or become arguments; say which you
   chose and why in one line.
4. If the `unfolding` repair the audit names is needed, write it as ONE clause
   and report its cost. The audit reports it as heap-safe when tried
   (`dev/pod/audit-2026-08-20.md:128-145`); if it is not heap-safe here, that
   is a WALL event: report it and stop.
5. Update `dev/ledger.toml`.

**DO NOT INHABIT `AmbToCoded` AND DO NOT POSTULATE IT.** It is a parameter and
nothing else. **Do not substitute a different type for it** because a
different type is easier to inhabit: `[LJ-1.398]` did that with a statement a
predecessor had already refuted, and the audit measured it
(`dev/pod/audit-2026-08-20.md:34`).

**DO NOT CLAIM THE TROPHY.** The trophy case is `src/Landmarks.lagda.md` and
this task does not touch it. `chain-upper` under a hypothesis is not a proof
of the stage-cardinal bound; it is a proof that ONE statement stands between
this tree and that bound on this route. Write that sentence and no stronger
one.

**PROSE IS FROZEN.** Write the chapter's code and the comments inside it. No
mathematical prose and no narrative section (`AGENTS.md:69`). A conflict with
the style checks is a STOP: name both rules at `file:line`.

**THE RATIO BAR IS LIVE** at 0.0123 seconds per in-fence line, over the
non-blank lines inside the ` ```agda ` fences of your write scope. The
instantiation of `L.StageCardinal` is the expensive part and law P-m
(`dev/LESSONS.md:2512`) says instantiation is the expensive content class.
**Do not pad the chapter to beat the bar.** An escalation is a review, not a
failure. **Report the two numbers in a section `## THE RATIO`.**

**W2 (DD4).** `AmbToCoded` and `chain-upper` stay generic in `ℓ` and in every
parameter `[LJ-1.420]` already carries. Name no band, no numeral except `ω`,
and no site.

**C-42.** In a section `## WHAT THIS DOES NOT MEASURE`, say plainly that this
task measures nothing about the TRUNCATED route, whose residue is `SqCollect`
in this same chapter after `[LJ-1.443]`, and that the two residues are not
known to be the same statement. Nobody has measured that, and this task does
not.

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 110 in-fence lines. BASIS: `[LJ-1.420]`'s probe
at 58 non-blank non-comment lines, plus a chapter header, plus the imports the
probe takes from three chapters. A delivered comparable of SHAPE.
**Replace this estimate with the MEASURED line count of `[LJ-1.420]`'s file as
soon as you have opened it, and say in the report that you did.** Comparables
are of SHAPE and never of size, and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the instantiation of `L.StageCardinal` inside a MASTER, and it is
unmeasured because it has only ever run inside a probe:

    SC.Upper.stage-card-upper

as `[LJ-1.420]` reaches it at `agents/tasks/LJ-1-420/Probe420.agda:99`, under
the module application at `agents/tasks/LJ-1-420/Probe420.agda:75-96`.

**Write the chapter up to and including that module application, with the
obligation `chain-upper` OMITTED, typecheck it alone, and report the median
wall time and peak RSS over three forced rechecks at the pane's caliber.**
Then add the obligation and measure again. A heap event is a WALL event:
report it and stop, and name the `unfolding` clause as the suspect if one is
present.

Run `make check` once before you write anything and once after, and report
both wall times.

ESTIMATE for W3: `[LJ-1.420]`'s own measured median, which you must quote at
`file:line` from its report. If your measurement differs from it by more than
a factor of two, that is a finding about what a master costs against a probe,
and it goes in the report.

## WHAT GO AND NO-GO EACH EARN

**A GO PUTS THE AMBIENT ROUTE'S ENDPOINT IN THE TREE WITH ITS RESIDUE NAMED.**
It says the stage-cardinal upper bound holds at every infinite band ordinal
from `AmbToCoded` alone, in `src/`, and `make check` is green.

**A NO-GO IS WORTH AS MUCH.** It says either a premise is not in the tree, or
the two hypothesis types do not match projection for projection, or the
instantiation costs something inside a master that it did not cost inside a
probe, or the `unfolding` repair walls the heap. Each is a fact this campaign
needs before it lands anything else, and each names a file and a line.

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
  changed_files_any = ["src/L/StageBound.lagda.md"]
  changed_files_none = ["agents/tasks/LJ-1-444/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-444/review-of-*.md"]

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
- CANDIDATE archive/dev/JOURNAL.md  (score 175.549)
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 174.820)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 161.655)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 160.668)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 158.158)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 56.186)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 48.048)
- CANDIDATE dev/literature/digest.md  (score 37.348)
- CANDIDATE dev/literature/terms-2026-08.md  (score 36.990)
- CANDIDATE dev/literature/geology.md  (score 35.040)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
