# LJ-1.498: does the level graph name any constant at all

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-498/Probe498.agda`:

    graphFo-at-SL : {n : ℕ} (w b : Fin n) → Formula SL n

**the level graph as a formula over the STAGE carrier `SL`, by `mapFo` along
some map.** Land nothing in `src/`.

**`[LJ-1.494]` IS A CRITIC-UPHELD NO-GO AND IT FOUND A SECOND WALL, PRIOR TO THE
ONE I BRIEFED.** Its verdict names stage membership of `hierL`, but its
next-brief section names something that comes first
(`agents/tasks/LJ-1-494/lj-1.494-report.md:364-368`):

> The Formula-carrier wall is a second blocker. `LsetGraphAt` is `Formula CS.S`.
> `AbsL.⊨ᵐ` takes `Formula SL`. A next brief that wants satisfaction at `𝒮M`
> must name a formula whose constants live in `SL`, or name a delivered map
> `CS.S → SL`, which does not exist.

**A TOTAL MAP `CS.S → SL` CANNOT EXIST AND YOU MUST NOT LOOK FOR ONE.** `SL` is
the carrier restricted to one stage (`src/L/Hull.lagda.md:153-156`), and not
every element of `L` lies in a given stage. **The question is not the map. It is
whether the formula needs one.**

**`mapFo` MOVES ONLY THE CONSTANTS.** So if `LsetGraphAt` names NO constant, any
map transports it and the wall is vacuous. The tree's own pattern is `inL`
(`src/L/Hull.lagda.md:171-172`), a carrier map used through `mapFo inL`
(`:176`). **Read that pattern; do not reuse `inL`, whose domain is the hull.**

**THIS IS A CENSUS BEFORE IT IS A TERM.** `GraphAt w b` is
`∃̇ (ApproxAt zero (suc b) ∧̇ Step (suc w) (suc b) zero)`
(`src/L/Coding/Sequence.lagda.md:291-292`) and every index in sight is a slot.
**Say whether any constant survives the unfolding.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-498/Probe498.agda::graphFo-at-SL"]

## SCOPE (write)
- agents/tasks/LJ-1-498/Probe498.agda
- agents/tasks/LJ-1-498/lj-1.498-report.md
- agents/tasks/LJ-1-498/review-of-graphFo-at-SL.md
- agents/tasks/LJ-1-498/runs/

## PREMISES

1. `[LJ-1.494]` is a critic-upheld NO-GO at `GraphSatAtStage`. Basis: agents/tasks/LJ-1-494/lj-1.494-report.md:125
2. It names the Formula-carrier wall as a second blocker. Basis: agents/tasks/LJ-1-494/lj-1.494-report.md:364
3. It reports that no delivered map `CS.S → SL` exists. Basis: agents/tasks/LJ-1-494/lj-1.494-report.md:367
4. `SL` is the carrier restricted to one stage. Basis: src/L/Hull.lagda.md:153
5. `inL` is the tree's carrier map into `SL`, from the hull. Basis: src/L/Hull.lagda.md:171
6. It is used through `mapFo` to move a formula. Basis: src/L/Hull.lagda.md:176
7. `GraphAt` unfolds to an existential over `ApproxAt` and `Step`. Basis: src/L/Coding/Sequence.lagda.md:291
8. `ApproxAt` is `domAt` conjoined with two universals. Basis: src/L/Coding/Sequence.lagda.md:286
9. The tree does not bound `hierL δ` by the stage, so do not attempt it. Basis: agents/tasks/LJ-1-494/lj-1.494-report.md:127
10. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
11. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**FIVE TASKS HAVE STOPPED ON THIS LEG AND EACH NAMED A DIFFERENT MISSING FACT.**
`[LJ-1.481]` and `[LJ-1.489]` wanted elementarity. `[LJ-1.487]` used the wrong
witness. `[LJ-1.492]` opened the hull's closure and stopped at a conversion.
`[LJ-1.494]` found the conversion blocked twice over. **This task attacks the
cheaper of the two blockers, and it may find it is not a blocker at all.**

## WHAT IS MISSING

The census, and the transport.

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE WHOLE TASK.** Unfold `LsetGraphAt` to its
atoms and **list every constant it names, at `file:line`**. `Everything.lagda.md`
records that a sibling formula names the constant `ωʟ`, so the answer is not
obviously "none". **If the list is empty, `mapFo` along any map transports the
formula and the wall is vacuous: say so and build the term.** If the list is not
empty, **name each constant and say whether it lies in the stage**, and if one
does not, STOP: that is a sharper statement of the wall than `[LJ-1.494]` could
give.

**DO NOT BUILD A TOTAL MAP `CS.S → SL` AND DO NOT POSTULATE ONE.** It would be
false. If the formula needs constants moved, the map is partial and its domain is
the finite set of constants, not the carrier.

**DO NOT ATTEMPT `hier-in-stage`, `GraphSatAtStage` OR `CoverWitnessesInHull`.**
`[LJ-1.494]` measured the first and `[LJ-1.492]` the third. This task is prior to
both.

**DO NOT ORDER `coverFo`, `code-of` OR `ambient-level` AGAIN.** `[LJ-1.492]`
forbids it and `[LJ-1.494]` repeats the prohibition.

**REQUIRED REPORT SECTION `## THE CONSTANT CENSUS`.** One row per constant of
`LsetGraphAt` with its `file:line`, or the word NONE with the unfolding that
shows it. **This section is the deliverable even if the term is not built.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 120 lines in the probe, of which the obligation is
about 30. BASIS: `[LJ-1.494]` stated its types in 30 non-blank non-comment lines
and `[LJ-1.492]` built a formula at arity one in a comparable file. Comparables
are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the census itself, because a formula's constants are not visible from its
type and nobody has unfolded this one.

    -- the atoms of ApproxAt and Step, with every `con` occurrence named

**Do this FIRST, before any transport, and record it in the report as you go.**
If a constant appears that does not lie in the stage, the transport cannot be
built and the task stops at its cheapest point with the wall named exactly.

ESTIMATE for W3: about 25 lines of reading and under 30 seconds of Agda. **Do not
fund it against `[LJ-1.494]`'s W3**: that measured a membership and this reads a
formula.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO REMOVES ONE OF THE TWO BLOCKERS ON THE CONDENSATION LEG**, and if the
census is empty it removes it for every formula of this family at once.

**A NO-GO NAMES THE CONSTANT THAT CANNOT CROSS**, which turns a wall described in
two sentences into one line of Agda, and tells the mathematician whether the
`AbsL.𝒮M` route is available at all.

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
  changed_files_none = ["agents/tasks/LJ-1-498/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-498/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-498/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-498/Probe498.agda"]
  changed_files_none = ["agents/tasks/LJ-1-498/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-498/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 199.446)
- CANDIDATE archive/dev/JOURNAL.md  (score 164.276)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 161.334)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 137.876)
- CANDIDATE dev/ARCHIVE.md  (score 135.730)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 69.528)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 48.435)
- CANDIDATE dev/literature/digest.md  (score 41.048)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 40.959)
- CANDIDATE dev/literature/terms-2026-08.md  (score 39.045)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
