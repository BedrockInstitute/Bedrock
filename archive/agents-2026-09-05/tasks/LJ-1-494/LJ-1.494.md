# LJ-1.494: the level graph at the stage world, which is what cover actually owes

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-494/Probe494.agda`:

    GraphSatAtStage :
        (δ : S) → IsOrd (fst δ) → ⟨ fst δ ∈ˢ Lset α ⟩
      → ⟨ ((Lset-at δ) ∷ δ ∷ []) AbsL.⊨ᵐ LsetGraphAt zero (suc zero) ⟩

the **defines** direction of the level graph's adequacy **at the stage world
`AbsL.𝒮M`**, not at `𝒮ʟ`. Land nothing in `src/`.

**`[LJ-1.492]` IS A CRITIC-UPHELD NO-GO AND ITS CRITIC NAMED THIS OBJECT.** The
return stopped at a conversion it called `StageSatOfCover`
(`agents/tasks/LJ-1-492/lj-1.492-report.md:135-137`). **Its critic says that
object alone is not enough**: what the consumer owes is adequacy of the level
graph at the stage world in BOTH directions
(`agents/tasks/LJ-1-492/review-of-LJ-1-492-1.md:163-166`). This task builds the
first direction and prices the second without attempting it.

**THE DEFINES DIRECTION IS DELIVERED, BUT AT THE WRONG WORLD.** `Lset-defines`
(`src/L/Hierarchy.lagda.md:646-648`) is exactly this statement at `𝒮ʟ`, whose
carrier is all of `L`. `AbsL.𝒮M` is `𝒮ᵥ` relativised to ONE STAGE
(`src/L/Hull.lagda.md:153`). Those are different worlds and the transfer is the
whole task.

**USE `hull-closed`, NOT `closed`.** `hull-closed`
(`src/L/Hull.lagda.md:415-417`) restates the closure with its hypothesis already
at `AbsL.⊨ᵐ`, and its own proof runs the `⊨c`-to-`𝒮M` conversion with `⊨-map`
(`src/L/Hull.lagda.md:419`). `[LJ-1.492]` opened `closed` and paid for the
decoder detour. **This is the cheapest spelling and its critic says so**
(`agents/tasks/LJ-1-492/review-of-LJ-1-492-1.md:168-177`).

**READ `src/L/Choice/Order.lagda.md` BEFORE YOU PRICE ANYTHING.** It consumes
`LsetGraphAt` inside its own satisfaction world (`:267`, with uses at `:372` and
`:462`). **It is a precedent that this is fundable, and it is NOT a cure.** A
measured cure does not transfer by analogy: re-measure at this site. Say in your
report what its price was and whether its shape is available here.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-494/Probe494.agda::GraphSatAtStage"]

## SCOPE (write)
- agents/tasks/LJ-1-494/Probe494.agda
- agents/tasks/LJ-1-494/lj-1.494-report.md
- agents/tasks/LJ-1-494/review-of-GraphSatAtStage.md
- agents/tasks/LJ-1-494/runs/

## PREMISES

1. `[LJ-1.492]` is a critic-upheld NO-GO on `CoverWitnessesInHull`. Basis: agents/tasks/LJ-1-492/lj-1.492-report.md:133
2. Its critic says the conversion alone cannot close it, and names both directions. Basis: agents/tasks/LJ-1-492/review-of-LJ-1-492-1.md:163
3. Its critic names `hull-closed` as the cheapest spelling. Basis: agents/tasks/LJ-1-492/review-of-LJ-1-492-1.md:168
4. `hull-closed` states its hypothesis at `AbsL.⊨ᵐ` already. Basis: src/L/Hull.lagda.md:415
5. Its proof runs the conversion with `⊨-map`. Basis: src/L/Hull.lagda.md:419
6. `AbsL` is `𝒮ᵥ` relativised to one stage. Basis: src/L/Hull.lagda.md:153
7. The defines direction is delivered at `𝒮ʟ` as `Lset-defines`. Basis: src/L/Hierarchy.lagda.md:646
8. Its approximation is `hierL`, which returns an element of `L`. Basis: src/L/Hierarchy.lagda.md:621
9. `GraphAt` is an existential over a matrix with two universal quantifiers. Basis: src/L/Coding/Sequence.lagda.md:291
10. That matrix is `ApproxAt`, whose second conjunct is the two universals. Basis: src/L/Coding/Sequence.lagda.md:286
11. `L.Choice.Order` restates graph satisfaction inside a consumer's own world. Basis: src/L/Choice/Order.lagda.md:267
12. The formula at arity one already forms, so do not rebuild it. Basis: agents/tasks/LJ-1-492/Probe492.agda:124
13. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
14. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34

## WHAT IS DELIVERED ALREADY

**FOUR TASKS HAVE NOW CIRCLED ONE MISSING FACT AND `[LJ-1.492]` NAMED IT.**
`[LJ-1.481]`, `[LJ-1.489]` and `[LJ-1.487]` all stopped for want of elementarity
at the hull. `[LJ-1.492]` opened the hull's own closure, proved the formula forms
at arity one, applied the closure, and stopped at ONE conversion. **The hull side
is finished. The graph side is not.**

## WHAT IS MISSING

The graph's adequacy at the stage world.

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE WHOLE RISK.** `GraphAt w b` is
`∃̇ (ApproxAt zero (suc b) ∧̇ Step (suc w) (suc b) zero)`
(`src/L/Coding/Sequence.lagda.md:291-292`). Going DOWN from `L` to one stage, the
two universals of `ApproxAt` are the cheap half. **The existential is the
expensive half: its witness must LIVE IN THE STAGE.** At `𝒮ʟ` that witness is
`hierL δ` (`src/L/Hierarchy.lagda.md:656`).

**So answer this ONE question first, at `file:line`, and it decides the task: is
`hierL δ` a member of `Lset α` when `δ` is?** `L.Hierarchy`'s third delivered
statement is that the tower below an ordinal is a single element of `L`
(`src/L/Hierarchy.lagda.md:624-625`). **Being an element of `L` is not being an
element of THIS stage.** If nothing in the tree bounds `hierL δ` by `α`, say so
and STOP: that names the missing fact exactly, and it is a better return than a
term built on a hypothesis nobody has.

**DO NOT POSTULATE THE BOUND AND DO NOT ADD A REFLECTION HYPOTHESIS.** If the
stage does not contain its own approximations, that is the finding.

**DO NOT REBUILD `coverFo`, `code-of` OR `ambient-level`.** `[LJ-1.492]` and
`[LJ-1.484]` built all three and `[LJ-1.492]`'s own report forbids re-ordering
them (`agents/tasks/LJ-1-492/lj-1.492-report.md:337-342`).

**REQUIRED REPORT SECTION `## THE ONLY DIRECTION, PRICED NOT BUILT.`** State, as
a type, the reverse reading at `AbsL.𝒮M`, name which of `Lset-only`
(`src/L/Hierarchy.lagda.md:334`) or `graph-table` (`:382`) is its source at
`𝒮ʟ`, and say whether the same stage-membership question governs it. **Do not
attempt it.** AD12 gives this brief one obligation.

**REQUIRED REPORT SECTION `## WHAT L.CHOICE.ORDER PAID.`** Give its price at
`file:line` and say whether its shape is available at this telescope. **Found
nothing on it.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 160 lines in the probe, of which the obligation is
about 45. BASIS: `[LJ-1.492]` built a comparable telescope with the hull, the
formula and both `isOrdFo` readings in 128 non-blank non-comment lines.
Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the stage membership of the approximation, because every other piece of
this transfer is delivered and this one has never been asked for.

    hier-in-stage : (δ : S) → IsOrd (fst δ) → ⟨ fst δ ∈ˢ Lset α ⟩
                  → ⟨ hierL (fst δ) _ _ ∈ˢ Lset α ⟩

**Write it FIRST, with the obligation omitted, and typecheck it ALONE.** If it
will not form, the existential of `GraphAt` cannot be witnessed inside the stage,
the whole transfer is blocked at a single named point, and the task stops at its
cheapest point having found the sharpest thing available.

ESTIMATE for W3: about 25 lines and under 30 seconds. **Do not fund it against
`[LJ-1.492]`'s W3**: that measured a formula, this measures a membership.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS THE HALF OF `cover` THAT `[LJ-1.492]` COULD NOT REACH**, and it does
it with the delivered spelling rather than a new route.

**A NO-GO AT W3 SAYS THE STAGE DOES NOT CONTAIN ITS OWN APPROXIMATIONS**, which
would explain every condensation stop this campaign has recorded with one fact,
and would tell the mathematician to re-price `cover` and `levelIn` together
instead of one at a time.

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
id = "accept-failed"
priority = 14
action = "escalate"
head_slot = "coder_adversarial"

  [branch.when]
  exit_code = 1
  changed_files_none = ["agents/tasks/LJ-1-494/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-494/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-494/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-494/Probe494.agda"]
  changed_files_none = ["agents/tasks/LJ-1-494/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-494/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 200.439)
- CANDIDATE archive/dev/JOURNAL.md  (score 170.117)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 166.020)
- CANDIDATE dev/ARCHIVE.md  (score 157.565)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 149.047)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 69.066)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 46.949)
- CANDIDATE dev/literature/digest.md  (score 43.914)
- CANDIDATE dev/literature/geology.md  (score 42.476)
- CANDIDATE dev/literature/terms-2026-08.md  (score 34.529)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
