# LJ-1.454: the injection this tree DEFINES, and whether it carries a code

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-454/Probe454.agda`:

    rank-graph :
        (a : S) (w : SWO ⟪ fst a ⟫)
      → Σ[ G ∈ S ]
          ((z : S) → ⟨ z ∈ˢ G ⟩
            ≡ ∥ Σ[ m ∈ ⟪ fst a ⟫ ]
                  (fst z ≡ pr (⟪ fst a ⟫↪ m) (swo-rank w m)) ∥₁)

the GRAPH of the rank map, as an element of `S`. `swo-rank` is `[LJ-1.416]`'s
delivered top-level term. Land nothing in `src/`.

**THIS IS HALF A, AND IT IS THE STEP THAT HAS FAILED THREE TIMES. THE
DIFFERENCE IS THE FUNCTION.** `[LJ-1.414]`, `[LJ-1.426]` and `[LJ-1.441]` each
asked for the graph of an injection produced by `leastOf`, an ambient selection
whose output carries no defining formula by construction
(`src/L/Cardinal.lagda.md:117`). **`swo-rank` is not that.** It is defined by
well-founded recursion on the order (`agents/tasks/LJ-1-416/Probe416.agda:105`),
so it has a definition, and a definition is what separation needs.

**READ THREE REPORTS BEFORE ANY AGDA, AND STOP IF ANY VERDICT IS NOT `GO`:**
`agents/tasks/LJ-1-416/lj-1.416-report.md` (`:14`),
`agents/tasks/LJ-1-417/lj-1.417-report.md` (`:18`) and
`agents/tasks/LJ-1-418/lj-1.418-report.md` (`:18`). All three are committed.
Quote each verdict line and each delivered type before you write a line of Agda.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-454/Probe454.agda::rank-graph"]

## SCOPE (write)
- agents/tasks/LJ-1-454/Probe454.agda
- agents/tasks/LJ-1-454/lj-1.454-report.md
- agents/tasks/LJ-1-454/review-of-rank-graph.md
- agents/tasks/LJ-1-454/runs/

## PREMISES

1. `[LJ-1.416]` is GO and delivers `swo-rank` at the TOP LEVEL, built by well-founded recursion and not hypothesized. Basis: agents/tasks/LJ-1-416/lj-1.416-report.md:14
2. Its delivered type is `swo-rank : {A : Type ℓ} (w : SWO A) → A → S`, with `swo-rank-ord` and `swo-rank-mono` beside it. Basis: agents/tasks/LJ-1-416/Probe416.agda:105
3. `[LJ-1.417]` is GO on an UNTRUNCATED injection into an ordinal, built from that rank. Basis: agents/tasks/LJ-1-417/lj-1.417-report.md:18
4. Its delivered type carries no truncation, and the report says so in one line: the rank is enough. Basis: agents/tasks/LJ-1-417/Probe417.agda:80
5. `[LJ-1.418]` is GO: an untruncated injection from EVERY stage into some ordinal, with no pairing, no `Init`, no band and no infiniteness in the telescope. Basis: agents/tasks/LJ-1-418/lj-1.418-report.md:18
6. The tree carves a graph by ONE separation, and the device supplies a stage bound and `hasSeparationL` and nothing more. Basis: src/L/InjChain.lagda.md:468
7. `[LJ-1.429]` used that route and got a code. Basis: agents/tasks/LJ-1-429/lj-1.429-report.md:84
8. The order at an L-element is describable in the object language, and the description module takes exactly `(A : V ℓ) (pA : ⟨ isL A ⟩) (w : SWO ⟪ A ⟫)`. Basis: src/L/Choice/Internal.lagda.md:1014
9. `InjCode`'s four conjuncts are what every coded consumer reads. Basis: src/L/Cardinal.lagda.md:223
10. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
11. A refutation measures the site it names and never how far that site extends. Basis: dev/LESSONS.md:3752
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THIS TREE ALREADY OWNS AN UNTRUNCATED INJECTION FROM EVERY STAGE INTO AN
ORDINAL, AND NOTHING HAS CONSUMED IT SINCE `[LJ-1.418]` CLOSED.**

- `[LJ-1.416]` builds the rank (`Probe416.agda:105-108`).
- `[LJ-1.417]` turns it into `swo-into-ord : Σ[ β ∈ S ] (IsOrd β × (A ↪ ⟪ β ⟫))`
  (`Probe417.agda:80-81`), untruncated.
- `[LJ-1.418]` instantiates it at the tower as `stage-into-bound`
  (`Probe418.agda:64-66`).

**AND THE ORDER THOSE THREE RUN ON IS DESCRIBED IN THE OBJECT LANGUAGE, IN A
LANDED CHAPTER, INSIDE A PROVED TROPHY'S IMPORT CLOSURE.**
`src/L/Choice/Internal.lagda.md` exists so that "the model's own separation can
carve the order out as a set and the choosing can be written down inside"
(`:5-10`), and its `Adequacy` module takes the SAME telescope `[LJ-1.417]`
consumes. **No file in this tree has ever held both.**

## WHAT IS MISSING

The graph. `swo-into-ord` gives a function; every coded consumer wants a set.

## THE REASONING

**WHY THIS IS NOT THE STATEMENT THAT FAILED THREE TIMES.** Write this in the
report before any Agda, with both types at `file:line`. `amb-to-coded` asks for
the graph of an ARBITRARY injection. This asks for the graph of ONE named
function that the tree defines. A general negative about the first says nothing
about the second, and C-42 rules that in both directions
(`dev/LESSONS.md:3752`).

**WHAT `[LJ-1.419]` REFUTED, AND WHY IT IS NOT THIS.** `[LJ-1.419]` is NO-GO
(`lj-1.419-report.md:15`): the rank route does NOT replace the pairing parameter
in the stage-cardinal consumer, and `bound-into-ord` as that brief stated it is
FALSE at that generality. **This task makes no claim about the pairing and does
not touch that consumer.** It asks only whether the rank map has a graph. Say so
in one line and cite `:15`.

**THE SHAPE.**

1. Rebuild `swo-rank` at `[LJ-1.416]`'s delivered type, or import
   `L.WellOrder.Base` and restate it. Do not import a probe.
2. Do W3 first, and stop there if W3 fails.
3. Build the obligation by ONE separation over a bound, in the shape
   `src/L/InjChain.lagda.md:468-490` uses: name the bound BEFORE the graph, then
   separate, then read the two directions back.

**DO NOT POSTULATE, DO NOT ADD A HYPOTHESIS TO CLOSE A CASE, AND DO NOT WEAKEN
THE GRAPH TO A TRUNCATED EXISTENCE.** A telescope that grows to close a case is
the shape audit findings F1 and F3 measured (`dev/pod/audit-2026-08-20.md:34`).

**REQUIRED REPORT SECTION `## WHAT THE FORMULA COSTS`.** Name, as a
`Formula S n` and at `file:line`, the formula the separation consumes. If
`L.Choice.Internal` already delivers it, cite it. **If it does not, name what is
missing and STOP: that missing formula is worth more than the obligation**, and
it is the first honest statement of what a definable injection costs in this
tree.

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 160 lines in the probe, of which the obligation is
about 40. BASIS: `src/L/InjChain.lagda.md:468-544` is 77 lines for the carve
plus its two readings at the inclusion, and `agents/tasks/LJ-1-429/Probe429.agda`
is 98 lines for a code at a bound. Comparables are of SHAPE, and nothing may be
funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is whether the rank is DESCRIBABLE, and it is the cheapest place this task
can die.

    rank-formula : Formula S 2

**State it and typecheck it ALONE, with the obligation omitted, as the formula
whose satisfaction at `(z ∷ a ∷ [])` says `z` is the pair of a member of `a`
and that member's rank.** Then say, in one line, whether
`src/L/Choice/Internal.lagda.md` delivers it, derives it, or does neither.

**IF IT DELIVERS ONLY THE ORDER AND NOT THE RANK, SAY SO AND STOP.** The rank
is a well-founded recursion ON that order, and a description of the order is not
a description of the recursion. **That distinction IS the finding**, and the
next brief's whole target is the formula it names.

ESTIMATE for W3: about 25 lines and under 10 seconds. BASIS: `Adequacy` opens
at `src/L/Choice/Internal.lagda.md:1014` and the chapter's other formulas run
15 to 30 lines each (`:304`, `:731`, `:910`). If it costs more, say so.

Report the median wall time and the peak RSS over three forced rechecks at the
pane's caliber, for W3 alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO CHANGES THE CAMPAIGN'S DIRECTION.** It says this tree can code an
injection it DEFINES, and every coded consumer that has been starved since
`[LJ-1.424]` gets an input that does not come from `leastOf`. The three
`amb-to-coded` NO-GOs then read as a statement about arbitrary functions and
not about this tree's reach.

**A NO-GO IS WORTH AS MUCH AND IT IS THE LIKELIER RETURN.** It names the
formula that is missing between a described ORDER and a described RECURSION. No
report in this campaign has ever named that gap, and `[LJ-2.5]` needs it.

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
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-454/review-of-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-454/Probe454.agda"]
  changed_files_none = ["agents/tasks/LJ-1-454/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-454/review-of-*.md"]

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
- CANDIDATE archive/dev/JOURNAL.md  (score 157.983)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 156.477)
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 151.594)
- CANDIDATE dev/ARCHIVE.md  (score 123.859)
- CANDIDATE archive/dev/DD-archived.md  (score 122.128)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 64.930)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 56.133)
- CANDIDATE dev/literature/digest.md  (score 38.921)
- CANDIDATE dev/literature/terms-2026-08.md  (score 34.877)
- CANDIDATE dev/literature/fine-structure.md  (score 34.527)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
