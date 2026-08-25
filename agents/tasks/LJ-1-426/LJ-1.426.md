# LJ-1.426: can the tree code the AMBIENT least-cardinal arrow, at one named ordinal

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-426/Probe426.agda`, at a GENERIC L-element
`a : S` with its ordinal certificate `oa` as module parameters, with
`L.Cardinal`'s own site bound and its ambient least cardinal in scope
(`open SiteBound a`, `src/L/Cardinal.lagda.md:163`; `open LeastCardInjL a oa`,
`src/L/Cardinal.lagda.md:61`):

    kappa-coded : ∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) a κ ∥₁

**BUILD IT FROM LIVE CHAPTERS, OR RETURN NO-GO NAMING THE ONE MISSING LINK.**
The conclusion is truncated, so nothing here untruncates anything.

**W8 BINDS THIS TASK. READ THE LITERATURE BEFORE ANY AGDA.** A literature NO-GO
is a full return and not a failure.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-426/Probe426.agda::kappa-coded"]

## SCOPE (write)
- agents/tasks/LJ-1-426/Probe426.agda
- agents/tasks/LJ-1-426/lj-1.426-report.md
- agents/tasks/LJ-1-426/review-of-kappa-coded.md

## PREMISES
- The ambient least cardinal and its truncated arrow are delivered at a generic L-element. Basis: src/L/Cardinal.lagda.md:133
- That arrow is an ambient function under a truncation, and the chapter states why it stays truncated. Basis: src/L/Cardinal.lagda.md:132
- `InjCode` is four satisfaction facts about a SET, and it names no ambient function. Basis: src/L/Cardinal.lagda.md:224
- The ordinal inclusion is coded and delivered, generic in the ordinal. Basis: src/L/InjChain.lagda.md:604
- The composition of two coded graphs is delivered, by separation. Basis: src/L/InjChain.lagda.md:314
- Separation takes a formula of one place, and never a function. Basis: src/L/Absorption.lagda.md:400
- `[LJ-1.414]` delivered the second half: four membership readings give `InjCode`. Basis: agents/tasks/LJ-1-414/Probe414.agda:115
- Its first half, a graph of an ambient injection, has no producer and is a hole. Basis: agents/tasks/LJ-1-414/Probe414.agda:139
- That report returned NO-GO on the general implication and did NOT refute it. Basis: agents/tasks/LJ-1-414/lj-1.414-report.md:39
- Audit finding F6 downgrades the words of grade「cannot」in that report. Basis: dev/pod/audit-2026-08-20.md:83
- The architecture is a CANDIDATE and only a measurement settles it. Basis: dev/pod/screen.toml:10

## WHAT IS DELIVERED ALREADY

**HALF B, IN FULL.** `code-from-graph` (`agents/tasks/LJ-1-414/Probe414.agda:115-125`)
takes four membership readings of a set `G` and returns `InjCode G x d`. It is
green.

**AND TWO CODED GRAPHS THE TREE BUILDS FROM NOTHING.** `OrdIncl`
(`src/L/InjChain.lagda.md:604`) codes the inclusion of one ordinal into another.
`Comp` (`src/L/InjChain.lagda.md:314`) codes the composite of two coded graphs.

## WHAT IS MISSING

**HALF A, AT ONE NAMED ORDINAL.** `HalfA` (`agents/tasks/LJ-1-414/Probe414.agda:65-66`)
is a graph of an ambient injection, and `[LJ-1.414]` left it a hole at a
GENERIC pair `x d`. This task asks it at ONE pair, `a` and its own least
cardinal `κ`, which is a narrower object by one quantifier and by everything
`κ`'s definition carries.

## THE REASONING

**ANSWER FOUR CANDIDATE SUPPLIERS, EACH IN ONE PARAGRAPH WITH `file:line`.**
This is the task. Do not skip one because it looks obviously wrong: the value
of this return is the enumeration, and an unanswered candidate is what audit
finding F8 measured.

1. **`OrdIncl` (`src/L/InjChain.lagda.md:604`).** `κ` sits in `sucV (fst a)`
   (`src/L/Cardinal.lagda.md:129`), so the inclusion available runs from `κ`
   into `a`. Say which direction it gives and whether that is the one needed.
2. **`Comp` (`src/L/InjChain.lagda.md:314`).** It composes two CODED graphs. Say
   whether it can manufacture a first factor, or only chain ones it is given.
3. **Separation (`src/L/Absorption.lagda.md:400`).** `sep` takes a
   `Formula S 1`. `κ-inj` (`src/L/Cardinal.lagda.md:133`) is a truncated ambient
   FUNCTION. **State at `file:line` whether a function can be a formula
   parameter here, because that is the suspected blocker and it has never been
   written down as a measurement.**
4. **`[LJ-1.414]`'s HALF A (`agents/tasks/LJ-1-414/Probe414.agda:65-66`).** Say
   what `κ` carries that a generic `d` does not: its minimality
   (`src/L/Cardinal.lagda.md:140`), its membership in `sucV (fst a)`
   (`:129`), and the fact that its arrow comes from a `leastOf` selection
   (`:117`). **Does any of the three give a graph? Answer each separately.**

**D-10, BEFORE ANY AGDA.** The conclusion is truncated existence, so its truth
is not in doubt from the ambient side: an injection exists. What is in doubt is
whether the tree can produce a CONSTRUCTIBLE set that codes one. Write that
distinction out before you write Agda.

**W2 (DD4).** Generic in `a`. The ordinal certificate is a module parameter.
Name no band and no numeral except `ω`, which `stageBound`'s own type names.

**W3, THE WIDEST UNMEASURED TERM.**

    half-a-at-kappa

**THE PROBE.** Instantiate `code-from-graph`
(`agents/tasks/LJ-1-414/Probe414.agda:115-125`) at `x := a` and `d := κ`, with
its four hypotheses left as bare module hypotheses, and report which of the four
has a producer in the live tree and which does not, each at `file:line`. **DO
NOT ATTEMPT HALF A ITSELF.** Audit finding F6 records that the one attempt to
join the halves reached 8.5 GB RSS and was killed
(`dev/pod/audit-2026-08-20.md:88`). Report wall seconds and peak RSS at the
caliber the program set on your pane, one Agda process, three forced rechecks,
and the median. If it costs a heap event, that is a WALL event: report it and
stop.

ESTIMATE for the Agda: about 25 code lines. BASIS: the whole probe is one module
application plus four hypothesis declarations, and the comparable of SHAPE is
`agents/tasks/LJ-1-414/Probe414.agda:115-125`, which is the same telescope
written once. **Comparables of SHAPE and never of size, and nothing may be
funded against them.**

## WHAT GO AND NO-GO EACH EARN

**A GO DISCHARGES THE CAMPAIGN'S RESIDUE FROM THE TREE.** With `[LJ-1.424]` it
gives the ambient arrow at `κ` as DATA, with no hypothesis left anywhere. Say in
the report which chapter supplied the graph and what a `src/` landing would cost.

**A NO-GO IS WORTH AS MUCH, AND IT IS THE MORE LIKELY RETURN.** It names HALF A
at ONE named ordinal as the campaign's single remaining link. That is a smaller
and more precise object than `[LJ-1.414]`'s general implication and than
「a well-order on the injections」, and naming it exactly is what
`[LJ-2.5]` needs. **Do not write a universal negative.** Audit findings F5 and
F6 record two reports that turned「this attempt failed」into「impossible」
(`dev/pod/audit-2026-08-20.md:76` and `:83`).

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
  changed_files_any = ["agents/tasks/LJ-1-426/Probe426.agda"]
  changed_files_none = ["agents/tasks/LJ-1-426/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-426/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 218.178)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 196.398)
- CANDIDATE archive/dev/JOURNAL.md  (score 175.359)
- CANDIDATE dev/ARCHIVE.md  (score 157.622)
- CANDIDATE archive/dev/DD-archived.md  (score 129.155)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 72.203)
- CANDIDATE dev/literature/devlin-II5.md  (score 70.745)
- CANDIDATE dev/literature/digest.md  (score 45.314)
- CANDIDATE dev/literature/terms-2026-08.md  (score 44.345)
- CANDIDATE dev/literature/geology.md  (score 36.606)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
