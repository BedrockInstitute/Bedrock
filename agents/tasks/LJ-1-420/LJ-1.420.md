# LJ-1.420: assemble the main chain into ONE term and put it in the tree

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-420/Probe420.agda`, at a GENERIC band
`α₀` with its ordinal certificate as module parameters.

    chain-upper : (δ : V ℓ) → IsOrd δ → ⟨ δ ∈ˢ sucV α₀ ⟩
                → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → ⟪ Lset δ ⟫ ↪ ⟪ δ ⟫

**IT IS `L.StageCardinal`'s OWN OUTPUT, REACHED BY INSTANTIATING THE MODULE.**
Do not restate the induction. Instantiate `L.StageCardinal lem α₀ oα₀` with the
pairing that `[LJ-1.413]` built, then read `stage-card-upper`
(`src/L/StageCardinal.lagda.md:564-565`) out of it.

**ONE HYPOTHESIS AND EXACTLY ONE.** `amb-to-coded`, at `[LJ-1.414]`'s delivered
type (`agents/tasks/LJ-1-414/Probe414.agda:134-139`). Take it as a module
parameter, name it, and do not attempt it.

**EVERY OTHER PIECE IS DELIVERED AND GREEN. IMPORT OR RESTATE, DO NOT REBUILD.**

- `sq-data` and `plugs-in`, `agents/tasks/LJ-1-413/Probe413.agda:309-312` and
  `:326`. `sq-data` takes three module hypotheses.
- `init-at-kappa`, `agents/tasks/LJ-1-406/Probe406.agda:180`.
- `coded-descent`, at `[LJ-1.412]`'s type, restated at
  `agents/tasks/LJ-1-413/Probe413.agda:226-232`.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-420/Probe420.agda::chain-upper"]

## SCOPE (write)
- agents/tasks/LJ-1-420/Probe420.agda
- agents/tasks/LJ-1-420/lj-1.420-report.md
- agents/tasks/LJ-1-420/review-of-chain-upper.md

## PREMISES
- The consumer takes the pairing as a module parameter, so the pairing must exist before the module opens. Basis: src/L/StageCardinal.lagda.md:17
- The consumer's output is a bare injection from the stage's member type into the ordinal's. Basis: src/L/StageCardinal.lagda.md:564
- The consumer spends the pairing once, inside the limit step. Basis: src/L/StageCardinal.lagda.md:283
- `[LJ-1.413]` delivered the pairing at every band ordinal as DATA, from three module hypotheses. Basis: agents/tasks/LJ-1-413/Probe413.agda:309
- `[LJ-1.413]` checked its own fit to the consumer's parameter type mechanically. Basis: agents/tasks/LJ-1-413/Probe413.agda:326
- `[LJ-1.406]` delivered `Init` at the sealed ambient least cardinal from a truncated induction hypothesis. Basis: agents/tasks/LJ-1-406/Probe406.agda:180
- `[LJ-1.414]` left `amb-to-coded` as a hole and named it the campaign's remaining bill. Basis: agents/tasks/LJ-1-414/Probe414.agda:139
- The three probes each sealed their own `κL`, so direct application of one seal's output to another reports unequal terms. Basis: agents/tasks/LJ-1-406/Probe406.agda:82
- The architecture is a CANDIDATE and only a measurement settles it. Basis: dev/pod/screen.toml:10

## WHAT IS DELIVERED ALREADY

**THE CHAIN EXISTS IN PIECES AND HAS NEVER EXISTED AS ONE TERM.** `[LJ-1.401]`,
`[LJ-1.406]`, `[LJ-1.411]`, `[LJ-1.412]` and `[LJ-1.413]` each delivered one
link, each green in its own file, each with the next link stated as a module
hypothesis. Nothing in the tree joins them.

**AN INDEPENDENT CRITIC JOINED THEM ONCE, OUTSIDE THE TREE.** The record is
`dev/pod/audit-2026-08-20.md`, finding F10. The critic reports that the three
`κL` seals need one explicit `unfolding` clause, that the repair was heap-safe
when tried, and that the joined chain then compiles and yields
`Upper.stage-card-upper`. **That run is on no disk and no branch.** This task
makes it an artifact.

## WHAT IS MISSING

**THE CAMPAIGN HAS NO ASSEMBLED RESULT, SO IT CANNOT SAY WHAT ITS RESIDUE IS
WORTH.** `[LJ-2.5]` is asked to rule on an architecture. A ruling wants one
term with one named hypothesis, not five files each pointing at the next.

**AND THE SEAL PROBLEM IS UNMEASURED IN THIS TREE.** `[LJ-1.398]` measured an
8 GB heap event on the unfolding style (`dev/pod/audit-2026-08-20.md`, F10).
Whether the repair costs that here is a number nobody in the five slots has.

## THE REASONING

**START FROM THE SEALS, BECAUSE THAT IS WHERE THE ASSEMBLY FAILS.**
`agents/tasks/LJ-1-406/Probe406.agda:82` opens an `opaque` block over `κL`,
`κoL`, `κ-injL` and `κ-min-atL`. `[LJ-1.407]` and `[LJ-1.413]` each declare a
seal of their own. Two seals of the same definition are two atoms to the
elaborator, and a hypothesis stated at one does not apply at the other.

**THE CURE THE CRITIC NAMES IS ONE `unfolding` CLAUSE.** Write it, run it
ALONE first, and report the number. **If it costs a heap event, that is a WALL
event: report it and stop. Do not rerun it at a wider caliber.**

**W2 (DD4).** Generic in `δ`. The band `α₀` and its certificate are module
parameters, exactly as the consumer states them. Name no cardinal and no
numeral except `ω`, which the consumer's own type names.

**D-10, BEFORE ANY AGDA.** `chain-upper` is the consumer's own delivered
statement, so its truth at this generality is the consumer's claim and not a
new one. Check instead that the hypothesis you take is `[LJ-1.414]`'s
DELIVERED type and not the type any brief asked for. **Cite
`agents/tasks/LJ-1-414/Probe414.agda` at the line, never a brief.**

**W3, THE WIDEST UNMEASURED TERM.**

    unfolding-cost

**THE PROBE.** Write the `unfolding` clause and the smallest term that forces
it, in `Probe420.agda`, and typecheck THAT FILE ALONE before you add the rest
of the chain. Report wall seconds and peak RSS at the caliber the program set
on your pane, one Agda process, three forced rechecks, and the median.

ESTIMATE for the Agda: about 45 code lines. BASIS: it is four module
instantiations, one `unfolding` clause and one projection, and the comparable
of SHAPE is `[LJ-1.413]`'s own hypothesis block at
`agents/tasks/LJ-1-413/Probe413.agda:219-232`, which is 14 lines for three
hypotheses. **Comparables of SHAPE and never of size, and nothing may be
funded against them.**

**CLOSE WITH THE RESIDUE, NAMED AND COUNTED.** Write a report section
`## THE REMAINING BILL` that states, with `file:line`: every hypothesis
`chain-upper` still carries, and for each one whether it is `amb-to-coded` or
something the assembly forced you to add. **A second hypothesis is a finding
and not a defect.** Say it plainly if the chain needs more than one.

## WHAT GO AND NO-GO EACH EARN

**A GO PUTS THE CAMPAIGN'S RESULT IN THE TREE.** It says: `L ⊨ GCH`'s counting
leg reduces, at every band ordinal, to exactly the hypotheses your report
names. That is what `[LJ-2.5]` reads.

**A NO-GO IS WORTH AS MUCH.** If the seals cannot be joined, or the joining
costs a heap wall, then the campaign's five green files do not compose, and
every price built on them is wrong. Say which pair fails and at which type.

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
  changed_files_any = ["agents/tasks/LJ-1-420/Probe420.agda"]
  changed_files_none = ["agents/tasks/LJ-1-420/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-420/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 191.327)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 145.902)
- CANDIDATE archive/dev/JOURNAL.md  (score 141.570)
- CANDIDATE dev/ARCHIVE.md  (score 118.750)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 102.591)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 44.514)
- CANDIDATE dev/literature/devlin-II5.md  (score 41.503)
- CANDIDATE dev/literature/terms-2026-08.md  (score 32.762)
- CANDIDATE dev/literature/geology.md  (score 31.832)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 28.795)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
