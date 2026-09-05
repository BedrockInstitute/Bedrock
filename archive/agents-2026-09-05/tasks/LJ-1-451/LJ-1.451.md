# LJ-1.451: the cheaper of the two condensation hypotheses

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-451/Probe451.agda`, at the type the
consumer states:

    levelIn : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ C.πX ⟩ → ⟨ Lset δ ∈ˢ C.πX ⟩

`C` is `Collapse M` and `M` is the definable hull `H.T.Hull` at a limit stage,
exactly as `src/L/BoundedSubset.lagda.md:898-916` builds them. Land nothing in
`src/`.

**RESTATE THE SITE, DO NOT IMPORT THE MODULE PARAMETER.** `levelIn` is a
parameter of `module Condense` (`src/L/BoundedSubset.lagda.md:917`), so it
cannot be projected out. Rebuild the telescope above it in your probe:
`HullStage`'s three limit hypotheses, `X`, `X⊆L` and `∅∈λ`
(`src/L/BoundedSubset.lagda.md:898-905`), then `M`, then `C = Collapse M`.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-451/Probe451.agda::levelIn"]

## SCOPE (write)
- agents/tasks/LJ-1-451/Probe451.agda
- agents/tasks/LJ-1-451/lj-1.451-report.md
- agents/tasks/LJ-1-451/review-of-levelIn.md
- agents/tasks/LJ-1-451/runs/

## PREMISES

1. `levelIn` is one of the two unpaid hypotheses of the condensation step. Basis: src/L/BoundedSubset.lagda.md:917
2. The other is `cover`, and this task does not touch it. Basis: src/L/BoundedSubset.lagda.md:918
3. **NEITHER HAS A PRODUCER.** `grep -c "levelIn\|cover" src/L/Condensation.lagda.md` returns 0 over 7,435 lines. Basis: src/L/Condensation.lagda.md:1
4. `levelIn` has exactly one consumer inside the step, the forward inclusion. Basis: src/L/BoundedSubset.lagda.md:1011
5. The hull is a term algebra closed under definable existence at the stage. Basis: src/L/Hull.lagda.md:120
6. The hull's members lie in the stage. Basis: src/L/Hull.lagda.md:330
7. The collapse's image has an introduction rule from membership in the hull. Basis: src/V/Collapse.lagda.md:86
8. The collapse is injective on the hull and its image is transitive. Basis: src/V/Collapse.lagda.md:214
9. `Lset` is the stage operation the conclusion names, and it is a function on the L-structure's own carrier. Basis: src/L/Constructible.lagda.md:222
10. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
11. `make check` is the gate before any commit. Basis: AGENTS.md:75
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THE BOUNDED-SUBSET LEMMA IS COMPLETE ABOVE THESE TWO HYPOTHESES AND BLOCKED
ON THEM.** `Devlin55.BoundedSubsetAt` (`src/L/BoundedSubset.lagda.md:1384`)
reaches `theorem : ⟨ x ∈ˢ Lset κ ⟩` (`:1621`), and the path runs through
`module Cn = HS.Condense levelIn cover` (`:1560`). Its other unpaid slot, the
square-law family, is what `[LJ-1]` has spent fifty dispatches on. **These two
have had none.**

**THE PIECES `levelIn` NEEDS ARE ALL DELIVERED.** The hull is closed under
definable existence (`src/L/Hull.lagda.md:120-123`), its members lie in the
stage (`:330-334`), and the collapse image has `πX-intro`
(`src/V/Collapse.lagda.md:86-87`) and the Mostowski package
(`:214`).

## WHAT IS MISSING

The term. Nobody has asked whether the hull is closed under `Lset` at its own
ordinals, which is what `levelIn` says once the collapse is transported across.

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE WHOLE RISK.** `levelIn` says: if `δ` is
an ordinal in the COLLAPSE IMAGE, then `Lset δ` is in the collapse image. Work
it back across the collapse before you write a term:

1. `δ ∈ C.πX` gives, by `C.πX-member`, some `y ∈ M` with `C.π y ≡ δ`.
2. So the statement is about `M`, the hull: is `Lset y` a member of the hull
   whenever `y` is, and does the collapse send it to `Lset δ`?
3. The first half is a DEFINABILITY question: is `Lset` a definable operation
   in the hull's own language? The hull is a term algebra over
   `Formula Code 1` (`src/L/Hull.lagda.md:120`), so the answer is a formula or
   it is a NO-GO.
4. The second half is an ABSOLUTENESS question: the collapse must commute with
   `Lset`, and `π` is defined by `∈`-recursion (`src/V/Collapse.lagda.md:53`).

**WRITE THOSE FOUR STEPS IN THE REPORT, AS TYPES, BEFORE THE TERM.** If step 3
has no formula, this task is a NO-GO and the formula is the thing the next
brief must order. **Say which step failed. A NO-GO that names its step is worth
more than a GO that hides one.**

**THE SHAPE.**

1. Rebuild the telescope down to `C = Collapse M`, copying
   `src/L/BoundedSubset.lagda.md:898-916` and nothing below it.
2. Do W3 first.
3. Build the obligation, or stop at the step that fails.

**DO NOT PAY `cover`.** It is the condensation lemma itself and it is not this
task. **Do not add it as a hypothesis either**: if `levelIn` needs `cover`, that
is the finding and the report says so as a type.

**DO NOT POSTULATE AND DO NOT WEAKEN THE CONCLUSION.** A truncated conclusion is
a different statement: the consumer at `src/L/BoundedSubset.lagda.md:1020`
spends `levelIn` as data, inside `Lβ⊆πX`.

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 140 lines in the probe, of which the obligation is
about 30. BASIS: `agents/tasks/LJ-1-434/Probe434.agda` is 128 lines and it
rebuilds a comparable telescope out of the same chapter to state one term about
it. Comparables are of SHAPE, and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is step 3, definability of `Lset` in the hull's language.

    lset-code : (c : Code) → Σ[ d ∈ Code ] (fst (val d) ≡ Lset (fst (val c)))

**Write it FIRST, with the obligation omitted, and typecheck it ALONE.** If the
hull's `Code` cannot name the stage operation, `levelIn` has no route through
the hull and the obligation is a NO-GO whatever the collapse does. **This is the
cheapest place the task can die and it must be measured before anything else.**

If `Code` carries no such constructor, do not force one: report the type above
as unbuilt, name the constructor that is missing at
`src/L/Hull.lagda.md:120-123`, and stop. That is a full return.

ESTIMATE for W3: about 20 lines and under 5 seconds. BASIS: it is one
membership in the term algebra's own index. If it costs more, say so.

Report the median wall time and the peak RSS over three forced rechecks at the
pane's caliber, for W3 alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS ONE OF THE TWO HYPOTHESES THAT BLOCK THE BOUNDED-SUBSET LEMMA**,
and it leaves `cover` alone in that position, which makes the next brief's
target unambiguous.

**A NO-GO NAMES THE MISSING FORMULA.** That is the first honest statement of
what the condensation front costs, and this campaign has never had one.

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
# MEASURED 2026-08-21: this row fired on `[LJ-1.448]` and routed it to a critic
# (dev/pod/transitions/2026-08.jsonl:915), where `[LJ-1.440]` parked no-match
# seven times without one. A stated NO-GO is the critic's input, never a close.
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-451/review-of-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-451/Probe451.agda"]
  changed_files_none = ["agents/tasks/LJ-1-451/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-451/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 168.862)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 148.096)
- CANDIDATE dev/ARCHIVE.md  (score 135.914)
- CANDIDATE archive/dev/JOURNAL.md  (score 131.083)
- CANDIDATE archive/dev/DD-archived.md  (score 117.371)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 49.664)
- CANDIDATE dev/literature/devlin-II5.md  (score 48.063)
- CANDIDATE dev/literature/digest.md  (score 41.406)
- CANDIDATE dev/literature/terms-2026-08.md  (score 34.945)
- CANDIDATE dev/literature/geology.md  (score 33.347)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
