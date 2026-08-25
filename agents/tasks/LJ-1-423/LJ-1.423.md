# LJ-1.423: the counting leg from ONE arrow, and the campaign's closing bill

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-423/Probe423.agda`, at a GENERIC band
`α₀` with its ordinal certificate as module parameters.

    upper-from-arrow : (δ : V ℓ) → IsOrd δ → ⟨ δ ∈ˢ sucV α₀ ⟩
                     → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → ⟪ Lset δ ⟫ ↪ ⟪ δ ⟫

**THE TELESCOPE MUST NOT HOLD `amb-to-coded`, `coded-descent` OR
`IsCardinalL`.** That is the difference between this task and `[LJ-1.420]`, and
it is the whole point.

**THE HYPOTHESES ARE `[LJ-1.421]`'s AND `[LJ-1.422]`'s DELIVERED TERMS, TAKEN
AS MODULE PARAMETERS AT THE TYPES THEIR REPORTS RECORD.** Read the reports, not
the briefs:

- `descent-from-data`, `agents/tasks/LJ-1-421/lj-1.421-report.md`.
- `kappa-arrow-data`, `agents/tasks/LJ-1-422/lj-1.422-report.md`.

**IF EITHER REPORT IS NO-GO, OR NAMES ITS STATEMENT FALSE, DO NOT WRITE THAT
TYPE INTO THIS TELESCOPE AS A HYPOTHESIS.** Stop, say which report refused it,
and return. Owner's ruling, 2026-08-20, measured by `dev/pod/audit-2026-08-20.md`
findings F1 and F3: two earlier tasks copied a supplier's BRIEF type after that
supplier's REPORT had refuted the statement, and both GOs were hollow.

**IF EITHER TASK HAS NOT RUN**, take its type from its own brief, say in the
report that you did so, and mark the return provisional. That is admissible; a
refuted type is not.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-423/Probe423.agda::upper-from-arrow"]

## SCOPE (write)
- agents/tasks/LJ-1-423/Probe423.agda
- agents/tasks/LJ-1-423/lj-1.423-report.md
- agents/tasks/LJ-1-423/review-of-upper-from-arrow.md

## PREMISES
- The consumer takes the pairing as a module parameter and spends it once, in the limit step. Basis: src/L/StageCardinal.lagda.md:283
- The consumer's output is the counting leg's target at every band ordinal. Basis: src/L/StageCardinal.lagda.md:564
- `[LJ-1.413]` delivered the pairing at every band ordinal as DATA and checked its fit to that parameter. Basis: agents/tasks/LJ-1-413/Probe413.agda:326
- Case three of that induction closes with no code at all, through the AMBIENT minimality of the least cardinal. Basis: agents/tasks/LJ-1-406/Probe406.agda:92
- Case four is where the coded detour enters. Basis: agents/tasks/LJ-1-413/Probe413.agda:282
- The arrow that detour starts from is delivered truncated by the tree. Basis: src/L/Cardinal.lagda.md:133
- `[LJ-1.414]` left the ambient-to-coded step a hole and did not refute it. Basis: agents/tasks/LJ-1-414/Probe414.agda:139
- The trophy case is `src/Landmarks.lagda.md`, and a theorem not wired into it is not landed. Basis: src/Landmarks.lagda.md:1
- The architecture is a CANDIDATE and only a measurement settles it. Basis: dev/pod/screen.toml:10

## WHAT IS DELIVERED ALREADY

**THE INDUCTION, THE TWO CASES AND THE CONSUMER FIT.** `[LJ-1.413]` holds all
three (`agents/tasks/LJ-1-413/Probe413.agda:309` and `:326`). This task changes
ONE branch of it and nothing else.

**AND `[LJ-1.420]` HOLDS THE ASSEMBLY.** If it returned GO, reuse its
instantiation of `L.StageCardinal` verbatim and change only the pairing you
feed it.

## WHAT IS MISSING

**A COUNTING LEG WHOSE ONE HYPOTHESIS IS AN ARROW AND NOT AN IMPLICATION.**
Every price this campaign has quoted rests on `amb-to-coded`, a general
implication about coding arbitrary ambient functions. If `[LJ-1.421]` and
`[LJ-1.422]` both return GO, the bill is instead ONE arrow at ONE named
ordinal, and that is a different object to price.

## THE REASONING

**BUILD THE PAIRING FIRST, THEN INSTANTIATE.** `descent-from-data` gives the
induction step at a generic ordinal. Feed it to `∈-induction` over the band,
exactly as `agents/tasks/LJ-1-413/Probe413.agda:312` does, to get the
consumer's parameter shape. Then instantiate `L.StageCardinal lem α₀ oα₀` with
it and read `stage-card-upper` out.

**W2 (DD4).** Generic in `δ`. The band and its certificate are module
parameters, as the consumer states them. Name no cardinal and no numeral except
`ω`.

**D-10, BEFORE ANY AGDA.** `upper-from-arrow` restates the consumer's own
delivered statement, so its truth is the consumer's claim. What you must check
is the TELESCOPE: read each supplier's report and confirm the type you copied
occurs there at the delivered term and not only in its brief. **Quote the
`file:line` for each.**

**W3, THE WIDEST UNMEASURED TERM.**

    instantiation-cost

**THE PROBE.** `L.StageCardinal` is a large module and this is the second time
the campaign instantiates it. Typecheck the instantiation ALONE, with a
`postulate`-free stub pairing if the real one is not yet green, and report wall
seconds and peak RSS at the caliber the program set on your pane, one Agda
process, three forced rechecks, and the median. **Compare it with `[LJ-1.420]`'s
number and say whether the two agree.** If it costs a heap event, that is a WALL
event: report it and stop.

ESTIMATE for the Agda: about 35 code lines. BASIS: it is `[LJ-1.420]`'s
assembly with one hypothesis swapped and the induction re-run, and the
comparable of SHAPE is `agents/tasks/LJ-1-413/Probe413.agda:309-312`, which is
4 lines for the induction plus the 14-line hypothesis block above it.
**Comparables of SHAPE and never of size, and nothing may be funded against
them.**

**CLOSE WITH THE CAMPAIGN'S BILL, IN ONE SECTION.** Write
`## WHAT LJ-1 STILL OWES` and state, each with `file:line`: every hypothesis
`upper-from-arrow` carries, whether each is delivered green somewhere in
`agents/tasks/`, and what remains before the counting leg could be written into
`src/`. **Do not write anything into `src/` in this task.**

## WHAT GO AND NO-GO EACH EARN

**A GO IS THE CAMPAIGN'S RESULT.** It says `L ⊨ GCH`'s counting leg holds at
every band ordinal from hypotheses the tree either has or has reduced to one
named arrow. Name in the report the exact line of `L.StageCardinal` that a
later task would change, and what a `src/` landing would cost.

**A NO-GO IS WORTH AS MUCH.** If the swapped pairing does not fit the
consumer's parameter, or if a supplier's report refuses its own type, then the
route through `[LJ-1.421]` and `[LJ-1.422]` is closed and `[LJ-1.414]`'s bill
stands. Say which supplier and at which type, and the campaign's residue is
then measured rather than assumed.

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
  changed_files_any = ["agents/tasks/LJ-1-423/Probe423.agda"]
  changed_files_none = ["agents/tasks/LJ-1-423/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-423/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 198.191)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 194.623)
- CANDIDATE archive/dev/JOURNAL.md  (score 186.792)
- CANDIDATE archive/dev/DD-archived.md  (score 158.375)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 154.510)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 59.235)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 47.729)
- CANDIDATE dev/literature/digest.md  (score 45.976)
- CANDIDATE dev/literature/geology.md  (score 39.881)
- CANDIDATE dev/literature/terms-2026-08.md  (score 38.286)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
