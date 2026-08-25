# LJ-1.445: land the truncated square law, from the report the tree carries

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Land ONE term in a NEW master `src/L/SquareLawClosed.lagda.md`:

    sq-trunc-closed :
        (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
      → ∥ sq δ ∥₁

at a GENERIC band, under the module parameters `{ℓ} (lem) (α₀) (oα₀)` and
NOTHING else. Register the master in `src/Everything.lagda.md`.

**READ ONE REPORT BEFORE ANYTHING ELSE:**
`agents/tasks/LJ-1-437/lj-1.437-report.md`. If it does not exist, or its
verdict is not `GO`, write nothing and stop. It is in this tree today: the
verdict is at `:17` and the delivered term is at
`agents/tasks/LJ-1-437/Probe437.agda:345-348`. Quote the verdict line and the
delivered type in your report before you write a line of Agda.

**THIS OBLIGATION HAS RUN ONCE AND IT STOPPED FOR A REASON THAT IS NOT
MATHEMATICS.** `[LJ-1.440]` held it. Its worktree was cut before `[LJ-1.437]`
was committed, so it could not open the report it was ordered to read, and it
stopped correctly. Its NO-GO is about a missing file and not about `sq`. **Do
not read that stop as a mathematical result and do not cite it as one.**

## OBLIGATION NAMES
obligations = ["src/L/SquareLawClosed.lagda.md::sq-trunc-closed"]

## SCOPE (write)
- src/L/SquareLawClosed.lagda.md
- dev/ledger.toml
- agents/tasks/LJ-1-445/lj-1.445-report.md
- agents/tasks/LJ-1-445/review-of-sq-trunc-closed.md
- agents/tasks/LJ-1-445/runs/
- `src/Everything.lagda.md` (R18: wire the new master here, because acceptance conjunct 3 refuses a catalog that does not import it)

## PREMISES

1. `[LJ-1.437]` is GO on `sq-trunc-closed` with an empty hypothesis telescope. Basis: agents/tasks/LJ-1-437/lj-1.437-report.md:17
2. The delivered type is at the probe that typechecked, and it is the type this task lands. Basis: agents/tasks/LJ-1-437/Probe437.agda:345
3. The proof reads `L.Cardinal` and `L.Absorption`, so the new master is imported after both. Basis: src/Everything.lagda.md:376
4. The consumer of the band bound is imported later, so the new master sits before it. Basis: src/Everything.lagda.md:387
5. `sq`, `Init` and `via-col-square` come from the square-law chapter. Basis: src/L/Ordinal/SquareLaw.lagda.md:959
6. The five-projection seal over the ambient least cardinal is the measured cure for the atom, and `[LJ-1.437]` names why. Basis: agents/tasks/LJ-1-437/Probe437.agda:90
7. `[LJ-1.440]` parked with `no-match` and wrote nothing into `src/`. Basis: dev/pod/transitions/2026-08.jsonl:832
8. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
9. The architecture is a CANDIDATE and only a measurement settles it. Basis: dev/pod/screen.toml:10
10. `make check` is the gate before any commit. Basis: AGENTS.md:75
11. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69
12. One SRC collection after LJ-1. Basis: dev/pod/direction.md:37

## WHAT IS DELIVERED ALREADY

**THE PROOF IS WRITTEN, IT TYPECHECKS, AND IT IS IN THIS TREE.**
`agents/tasks/LJ-1-437/Probe437.agda` is 349 lines. It carries the sealed
helpers (`:67-70`), the five-projection seal over the ambient least cardinal
(`:90-107`), conjunct 4 of `Init` at that cardinal, `init-at-kappa` as a
definition, and the band induction with four cases (`:345-348`). The report
records exit 0 and a median of 1.91 s over three forced rechecks.

**NOTHING OF THIS CAMPAIGN IS IN `src/` YET.** Fifty-one dispatches have
written probes under `agents/`. A probe is not a library: no master imports
one, and no trophy can be wired to one.

## WHAT IS MISSING

The chapter. `src/L/SquareLawClosed.lagda.md` does not exist. `ls` returns
`No such file or directory`.

## THE REASONING

**D-10, BEFORE ANY AGDA.** Open `agents/tasks/LJ-1-437/lj-1.437-report.md`
and quote the verdict at `:17`. Open `Probe437.agda` and quote the type at
`:345-348`. Say in one line whether the type you are about to land is that
type, character for character. If it is not, name the difference and stop.

**THE SHAPE.**

1. Create `src/L/SquareLawClosed.lagda.md` as a literate master. The chapter
   style is `dev/STYLE-agda.md` and the literate rules are `dev/STYLE-i18n.md`.
2. Move the content of `Probe437.agda` into it, unchanged in mathematics. Keep
   the two `opaque` blocks EXACTLY as the probe carries them (`:67-70` and
   `:90-107`). The seal is a measured cure and not decoration: `fst (κL a oa)`
   left transparent re-runs a `leastOf` reduction at every conversion check.
3. Import the chapter's suppliers from `src/`, not from a probe. **Import no
   file under `agents/`.** A master that reads a probe is a defect.
4. Register the master in `src/Everything.lagda.md` at a line after
   `import L.Absorption` (`:376`) and before `import L.StageCardinal` (`:387`).
5. Update `dev/ledger.toml`.

**WHAT MAY CHANGE, AND WHAT MAY NOT.** The mathematics may not change. The
module header, the import list and the comments may. If the master can take a
supplier straight from `src/` where the probe rebuilt it, take it, and say in a
section `## WHAT THE MOVE COST` which rebuilt block you deleted and what
replaced it. **If a rebuilt block cannot be deleted without opening a seal, keep
it and say why.**

**DO NOT WEAKEN THE STATEMENT.** Do not add a module hypothesis. Do not
truncate more than the probe truncates. Do not postulate. If the master cannot
be made to typecheck at the delivered type, that is a NO-GO and the obstruction
file is the deliverable.

**DO NOT CLAIM THE TROPHY.** The trophy case is `src/Landmarks.lagda.md` and
this task does not touch it. This term is one supply half of the counting leg.

**PROSE IS FROZEN.** Write the chapter's code and the comments inside it. Write
no mathematical prose and no narrative section (`AGENTS.md:69`). If a style
check demands a prose block the freeze forbids, that conflict is a STOP: name
the two rules at `file:line` and report.

**THE RATIO BAR IS LIVE.** The bar is 0.0123 seconds per in-fence line and the
divisor is the non-blank line count inside the ` ```agda ` fences of your write
scope. `[LJ-1.437]` measured 1.91 s over 349 lines, which is 0.0055 s per line.
The bar should not fire. **Report the two numbers in a section `## THE RATIO`.**

**W2 (DD4).** The term is written once at a generic band. Name no numeral and
no site.

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 300 in-fence lines. BASIS: `Probe437.agda` is 349
lines, of which about 20 are the probe header and the `OPTIONS` pragma that a
master does not carry. This is a delivered comparable of SHAPE and of size at
the same content, and it is the one case where the two agree, because the
content moves unchanged.

## W3, THE WIDEST UNMEASURED TERM

It is whether the SEAL survives the move into a master that imports
`L.Cardinal` directly.

    seal-holds : (a : S) (oa : IsOrd (fst a)) → S
    seal-holds = κL

**Write the five-projection `opaque` block into the new master FIRST, with the
band induction and `sq-trunc-closed` omitted, and typecheck the file alone.**
Report the wall time and the peak RSS. The risk is named and measured: an
unfolded least-cardinal atom is what `[LJ-1.398]` met as an 8 GB heap event,
and the master sits closer to `L.Cardinal` than the probe did.

ESTIMATE for W3: under 3 seconds and under 500 MB peak RSS. BASIS: the probe's
own W3 measured the same seal (`agents/tasks/LJ-1-437/lj-1.437-report.md:120`).
If it costs more here, that difference IS the finding and it is worth more than
the obligation.

Report the median wall time and peak RSS over three forced rechecks at the
pane's caliber, and run `make check` before and after the chapter lands.

## WHAT GO AND NO-GO EACH EARN

**A GO PUTS THIS CAMPAIGN'S FIRST TERM IN `src/`.** After it, a later brief can
cite a chapter instead of a probe, and `[LJ-1.449]` can state the campaign's
residue against a landed supply half.

**A NO-GO IS WORTH AS MUCH.** It says the proof does not survive contact with
the chapter tree: an import cycle, a seal that opens, or a gate that refuses the
master. Name which, at `file:line`.

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
  changed_files_any = ["agents/tasks/LJ-1-445/review-of-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["src/L/SquareLawClosed.lagda.md"]
  changed_files_none = ["agents/tasks/LJ-1-445/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-445/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 190.945)
- CANDIDATE archive/dev/JOURNAL.md  (score 182.795)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 172.614)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 159.425)
- CANDIDATE archive/dev/PLAN-archived.md  (score 159.185)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 60.048)
- CANDIDATE dev/literature/terms-2026-08.md  (score 46.549)
- CANDIDATE dev/literature/devlin-II5.md  (score 45.296)
- CANDIDATE dev/literature/digest.md  (score 35.863)
- CANDIDATE dev/literature/geology.md  (score 31.102)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
