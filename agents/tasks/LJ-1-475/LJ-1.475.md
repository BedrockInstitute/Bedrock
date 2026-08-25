# LJ-1.475: the rank formula, over an order that is now a set

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-475/Probe475.agda`:

    rank-formula : (Q : S) → Formula S 2

a first-order description of the well-founded rank of the order carried AS THE
SET `Q`, whose satisfaction at `(z ∷ a ∷ [])` says `z` is the pair of a member
of `a` and that member's rank in `Q`. Land nothing in `src/`.

**`[LJ-1.454]` NAMED THIS TARGET AND SAID WHY IT COULD NOT BE REACHED THEN.**
That critic-upheld STOP measured that `L.Choice.Internal` delivers the ORDER and
does NOT deliver the RANK, and its corrected target was: **inhabit the formula
first, then carve** (`agents/tasks/LJ-1-454/lj-1.454-report.md:73`). At the time
the order was not a set, so a first-order rank description had nothing to
quantify over.

**`[LJ-1.471]` CARVED IT.** `order-as-set` is GO
(`agents/tasks/LJ-1-471/Probe471.agda:90-94`, committed `198379c`): separation
accepts `orderFo`, the `appAtC` restatement reaches it, and both directions read
back. **The order is a set now, so the rank can be described by quantifying over
approximating functions on it.**

**READ BOTH REPORTS FIRST.** `[LJ-1.471]` also records that the brief's type as
written did not form and says what did; **take the delivered shape from the
probe, never from my brief.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-475/Probe475.agda::rank-formula"]

## SCOPE (write)
- agents/tasks/LJ-1-475/Probe475.agda
- agents/tasks/LJ-1-475/lj-1.475-report.md
- agents/tasks/LJ-1-475/review-of-rank-formula.md
- agents/tasks/LJ-1-475/runs/

## PREMISES

1. `[LJ-1.454]` is a critic-upheld STOP: Internal delivers the order and not the rank. Basis: agents/tasks/LJ-1-454/lj-1.454-report.md:73
2. Its corrected target is to inhabit the formula first and carve second. Basis: agents/tasks/LJ-1-454/lj-1.454-report.md:178
3. `[LJ-1.471]` is GO on the order as a set. Basis: agents/tasks/LJ-1-471/lj-1.471-report.md:109
4. Its delivered term is at the probe that typechecked, and its type is not the one my brief wrote. Basis: agents/tasks/LJ-1-471/Probe471.agda:90
5. `[LJ-1.468]` is GO on the one-slot order formula the carve consumed. Basis: agents/tasks/LJ-1-468/Probe468.agda:78
6. `[LJ-1.416]` builds the rank in the META language by well-founded recursion. Basis: agents/tasks/LJ-1-416/Probe416.agda:105
7. `[LJ-1.417]` turns it into an untruncated injection into an ordinal. Basis: agents/tasks/LJ-1-417/Probe417.agda:80
8. The tree builds formulas of this class with adequacy in both directions. Basis: src/L/Coding/Base.lagda.md:285
9. Separation consumes a `Formula S 1` over a named set. Basis: src/L/Axioms/Full.lagda.md:144
10. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
11. A refutation measures the site it names and never how far it extends. Basis: dev/LESSONS.md:3752
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

The rank exists in the META language and is green three times over
(`[LJ-1.416]`, `[LJ-1.417]`, `[LJ-1.418]`), and nothing has consumed those since
418 closed. The order now exists as a SET inside the model (`[LJ-1.471]`).
**What has never existed is a description of the rank in the object language.**

## WHAT IS MISSING

The formula. `[LJ-1.454]` named it and stopped rather than invent its body.

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE WHOLE RISK.** A rank is a well-founded
recursion. Its first-order description is the standard approximating-function
form: `z` is the pair `(m , r)` when there EXISTS a function `f` with domain the
`Q`-predecessors of `m`, which is a rank assignment on that domain, and `r` is
the supremum of the successors of its values. **Write that shape out as a type
before any Agda, and name, at `file:line`, the delivered formula machinery for
each clause it needs**: a function as a set, a domain, an application, a
supremum. `src/L/Coding/Base.lagda.md` and `src/L/Coding/Model.lagda.md` are
where those live.

**IF ANY ONE CLAUSE HAS NO DELIVERED FORMULA, NAME IT AND STOP.** That absence
is the finding and it is the next brief's whole target. **Do not invent a body
for a clause the tree does not have.**

**THE SHAPE.** Take `Q` as a parameter; do not rebuild the carve. Do not build
the graph and do not build `rank-graph`. One obligation: the formula.

**DO NOT PROVE ADEQUACY.** `[LJ-1.454]` asked for a formula, not for its two
readings, and adequacy is a separate price. **Say in the report what adequacy
would cost, with its basis.**

**DO NOT POSTULATE AND DO NOT WEAKEN THE RANK TO A BOUND.** `[LJ-1.417]` already
has a bound; a bound is not a rank.

**REQUIRED REPORT SECTION `## WHAT THE CARVE WOULD NOW COST`.** With the formula
in hand, state as a type what carving `rank-graph` would take and name the bound
it needs. **Do not carve it.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 160 lines in the probe, of which the obligation is
about 50. BASIS: `src/L/Coding/Base.lagda.md:248-295` is 47 lines for four
formulas at a flat shape, and a recursion is not flat; `[LJ-1.468]`'s
restatement reached its GO in about 90 lines. **The band is wide and the report
must narrow it with a measurement.** Comparables are of SHAPE.

## W3, THE WIDEST UNMEASURED TERM

It is the function-as-a-set clause, because everything else in the description
is membership and equality.

    fn-clause : Formula S 3

**State the clause that says `f` is a function with domain the `Q`-predecessors
of `m`, and typecheck it ALONE with the obligation omitted.** The tree has
`domAt` and `appAt` (`src/L/Coding/Model.lagda.md`), and `InjCode`'s own
conjuncts use them (`src/L/Cardinal.lagda.md:225-227`). **If those do not
compose into this clause, the rank has no first-order description in this tree
and the task stops at its cheapest point.**

ESTIMATE for W3: about 20 lines and under 20 seconds.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO REOPENS THE ROUTE `[LJ-1.454]` NAMED**: with a rank formula and a carved
order, `rank-graph` becomes one separation, and the untruncated injection
`[LJ-1.417]` already delivers would carry a code.

**A NO-GO NAMES THE MISSING CLAUSE**, which is the first statement in this
campaign about what a recursion costs to describe in the object language.

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
# THE ACCEPTANCE ITSELF CAN FAIL, AND NOTHING IN THIS TEMPLATE USED TO MATCH IT.
# MEASURED 2026-08-21 on LJ-1.469: the term was GREEN and its ratio was 0.0055,
# well under the bar, but acceptance conjunct 4 FAILED and the run exited 1.
# Every branch keyed on exit 0 or 42 missed, so the task parked `no-match` with a
# delivered obligation. An acceptance failure is a real event and it routes to a
# critic rather than to silence.
id = "accept-failed"
priority = 14
action = "escalate"
head_slot = "coder_adversarial"

  [branch.when]
  exit_code = 1
  changed_files_none = ["agents/tasks/LJ-1-475/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-475/review-of-*.md"]
  # THE CRITIC'S OWN RETURN MUST NOT RE-MATCH. It writes
  # `review-of-LJ-1-475-<k>.md` beside the coder's leftover `review-of-*.md`.
  # Without this exclusion the escalation re-escalates itself and `attempt_max`
  # parks the task PERMANENTLY. MEASURED 2026-08-21 on LJ-1.448, 449, 450, 451.
  changed_files_none = ["agents/tasks/LJ-1-475/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-475/Probe475.agda"]
  changed_files_none = ["agents/tasks/LJ-1-475/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-475/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 218.591)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 203.028)
- CANDIDATE archive/dev/JOURNAL.md  (score 163.680)
- CANDIDATE dev/ARCHIVE.md  (score 142.303)
- CANDIDATE archive/dev/DD-archived.md  (score 140.452)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 57.645)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 53.054)
- CANDIDATE dev/literature/terms-2026-08.md  (score 49.180)
- CANDIDATE dev/literature/digest.md  (score 42.507)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 34.326)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
