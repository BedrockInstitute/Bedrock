# LJ-1.478: carve the rank, the move two reports have now set up

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-478/Probe478.agda`:

    rank-graph :
        (Q a bnd : S)
      → Σ[ G ∈ S ] ((z : S) → (z ∈ˢ G)
          ≡ ((z ∈ˢ bnd) ⊓ ((z ∷ []) ⊨ rankFo Q a)))

where `rankFo Q a` is `[LJ-1.475]`'s `rank-formula Q` with the free `a` pinned as
`con a`. Land nothing in `src/`.

**`[LJ-1.475]` WROTE THIS TASK'S TYPES ITSELF AND TOLD YOU NOT TO CARVE.** It is
GO on `rank-formula : (Q : S) → Formula S 2`
(`agents/tasks/LJ-1-475/Probe475.agda:95-103`, committed `fdfb625`), its W3
composed `svAt`, `inDomAt` and `appAt` into the function-as-a-set clause, and its
section `## WHAT THE CARVE WOULD NOW COST` states `rankFo` and `rank-graph`
verbatim and names the pinning as the same `RelCond` move it used for `Q`.

**IT ALSO SAYS THE BOUND IS NOT DELIVERED AT THIS `Q`.** So `bnd` is a PARAMETER
here, exactly as `[LJ-1.471]` took one, and finding it is not this obligation.

**READ `[LJ-1.475]`'s REPORT FIRST** (verdict at `:105`). Take both types from it
and from its probe, never from this brief.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-478/Probe478.agda::rank-graph"]

## SCOPE (write)
- agents/tasks/LJ-1-478/Probe478.agda
- agents/tasks/LJ-1-478/lj-1.478-report.md
- agents/tasks/LJ-1-478/review-of-rank-graph.md
- agents/tasks/LJ-1-478/runs/

## PREMISES

1. `[LJ-1.475]` is GO on the rank formula. Basis: agents/tasks/LJ-1-475/lj-1.475-report.md:105
2. Its delivered term is at the probe that typechecked. Basis: agents/tasks/LJ-1-475/Probe475.agda:95
3. Its report states `rankFo` and `rank-graph` verbatim and names the pinning move. Basis: agents/tasks/LJ-1-475/lj-1.475-report.md:150
4. It records that the bound is not delivered at this `Q`. Basis: agents/tasks/LJ-1-475/lj-1.475-report.md:167
5. `[LJ-1.471]` is GO on the same carve shape at the order formula, with the bound a parameter. Basis: agents/tasks/LJ-1-471/Probe471.agda:90
6. Separation consumes a `Formula S 1` over a named set. Basis: src/L/Axioms/Full.lagda.md:144
7. `[LJ-1.454]` named this two-step route: inhabit the formula first, carve second. Basis: agents/tasks/LJ-1-454/lj-1.454-report.md:178
8. `[LJ-1.416]` builds the rank in the meta language. Basis: agents/tasks/LJ-1-416/Probe416.agda:105
9. `[LJ-1.417]` turns it into an UNTRUNCATED injection into an ordinal. Basis: agents/tasks/LJ-1-417/Probe417.agda:80
10. `[LJ-1.418]` instantiates that at EVERY stage, with no band and no infiniteness. Basis: agents/tasks/LJ-1-418/lj-1.418-report.md:18
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THE WHOLE ROUTE `[LJ-1.454]` NAMED IS NOW ONE STEP FROM CLOSING.**
`[LJ-1.468]` gave the order a one-slot formula, `[LJ-1.471]` carved the order
into a set, and `[LJ-1.475]` described the rank over it. Each of those was the
named obstruction of the one before it.

**AND THE PRIZE IS AT THE LIMITS.** `[LJ-1.418]` delivers an untruncated
injection from EVERY stage into an ordinal, limits included, with no band and no
infiniteness in the telescope. The shift code `[LJ-1.460]` built reaches only
successors, and `[LJ-1.464]` recorded that the shift route provably cannot reach
a limit. **A carved rank graph is the first candidate that can.**

## WHAT IS MISSING

The separation applied, and the pinning that lets it be applied.

## THE REASONING

**D-10, BEFORE ANY AGDA.** `[LJ-1.475]` pinned `Q` with `con`. **Pin `a` the same
way and say, in one line, that `rankFo Q a` is `Formula S 1`.** If the second
pinning does not reduce the arity the way the first did, that is the finding and
it stops the task cheaply.

**THE SHAPE.** Rebuild `[LJ-1.475]`'s formula at its delivered type. Pin `a`.
Apply `hasSeparationL` once at `bnd`. Read both directions back, as
`[LJ-1.471]`'s `order-as-set` did (`Probe471.agda:90-109`). Do not import a
probe. **Do not build the bound and do not build the code.**

**DO NOT CLAIM A CODE.** A carved graph is a SET. `InjCode` is four conjuncts
(`src/L/Cardinal.lagda.md:223-228`) and this task delivers none of them. **Do
not claim `Residue`, and do not claim anything about limits**: those are what a
GO here would make ASKABLE, and asking is a later brief.

**DO NOT POSTULATE AND DO NOT INVENT A BOUND.**

**REQUIRED REPORT SECTION `## WHERE THE BOUND COMES FROM`.** Name every delivered
term in `src/` that could supply `bnd` for pairs of a member and its rank, at
`file:line`, and say for each whether it fits. `[LJ-1.471]` was asked the same
question at the order; **say whether its answer transfers to the rank, and do not
assume it does**: C-42 rules that a measured cure does not transfer by analogy.

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 140 lines in the probe, of which the obligation is
about 30. BASIS: `[LJ-1.471]` carved at this exact shape and its obligation plus
both readings ran `Probe471.agda:90-109`, twenty lines, over a file that also
rebuilt the formula. Comparables are of SHAPE and nothing may be funded against
them.

## W3, THE WIDEST UNMEASURED TERM

It is the second pinning, because the first one is the only evidence that this
move works and one pinning is not two.

    rankFo : (Q a : S) → Formula S 1

**Write it FIRST, with the obligation omitted, and typecheck it ALONE.**
`[LJ-1.475]`'s formula has `a` free at a slot the `∃̇` nest binds around; **if
pinning it needs anything more than `con`, name what and report it.**

ESTIMATE for W3: about 6 lines and under 15 seconds. BASIS: `[LJ-1.475]` did the
same move for `Q` inside its own obligation.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO PUTS THE RANK IN THE MODEL AS A SET**, completing the three-step route
`[LJ-1.454]` named, and it makes one question askable that no other delivered
term reaches: whether the untruncated injection `[LJ-1.418]` gives at a LIMIT
stage carries a code.

**A NO-GO NAMES EITHER THE SECOND PINNING OR THE MISSING BOUND**, and either is a
measurement this campaign has never had.

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
  changed_files_none = ["agents/tasks/LJ-1-478/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-478/review-of-*.md"]
  # THE CRITIC'S OWN RETURN MUST NOT RE-MATCH. It writes
  # `review-of-LJ-1-478-<k>.md` beside the coder's leftover `review-of-*.md`.
  # Without this exclusion the escalation re-escalates itself and `attempt_max`
  # parks the task PERMANENTLY. MEASURED 2026-08-21 on LJ-1.448, 449, 450, 451.
  changed_files_none = ["agents/tasks/LJ-1-478/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-478/Probe478.agda"]
  changed_files_none = ["agents/tasks/LJ-1-478/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-478/review-of-*.md"]

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
