# LJ-1.516: transport the satisfaction, not only the formula

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-516/Probe516.agda`:

    graphSat-transports :
        (the satisfaction of graphFo-at-SL at AbsL.𝒮M)
      ↔ (the satisfaction of LsetGraphAt at 𝒮ʟ, at corresponding environments)

**by `Relabel.liftFo-correct` and the `⊨-map` law.** Land nothing in `src/`.

**`[LJ-1.514]` IS GO AND IT KILLED THE WALL, BUT ONLY FOR THE FORMULA.** Its
own words: "Satisfaction was NOT transported, only the formula.
`Relabel.liftFo-correct` (`src/FOL/Manipulation/Bounding.lagda.md:198`) says
`mapFo up (liftFo φ h) ≡ mapFo proj φ`. That is the equation an absoluteness
argument meets at, and this task did not spend it. **The next brief that wants
`⟨ γ AbsL.⊨ᵐ graphFo-at-SL w b ⟩` to say what `LsetGraphAt` says must order
`liftFo-correct` and the `⊨-map` law, and that is a separate obligation.**"

**THE INSTRUMENT IS `Relabel`, NOT `mapFo`, AND MY EARLIER BRIEF WAS WRONG
ABOUT THAT.** `[LJ-1.514]` measured that the tree uses `Relabel`
(`src/FOL/Manipulation/Bounding.lagda.md:146`), whose own prose names this
exact instance at `:135-137`, and that `liftFo` (`:162`) is the partial map
whose domain is the finite set of constants rather than the carrier. **Do not
look for a total `CS.S → SL` map. It would be false.**

**THE CENSUS IS DONE AND YOU MUST NOT REPEAT IT.** `LsetGraphAt` names
**664** constants, counted by the tree's own `countFo`
(`src/FOL/Manipulation/Parameters.lagda.md:74`) and recorded at
`agents/tasks/LJ-1-514/runs/w3-0.out:3-4`. The number does not matter here:
`liftFo` handles them given the certificate.

**A SIDE CONDITION `[LJ-1.514]` TOLD ME TO NAME RATHER THAN LET YOU
DISCOVER.** The stage is not free to choose. `graphFo-at-SL` lands at
`sucV σ`, the stage the formula's own constants force. **A consumer that needs
the formula at its own `α` must supply
`⟨ fst (mkBoundedFo (LsetGraphAt w b)) ∈ α ⟩` and use `graphFo-at-anyStage`.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-516/Probe516.agda::graphSat-transports"]

## SCOPE (write)
- agents/tasks/LJ-1-516/Probe516.agda
- agents/tasks/LJ-1-516/lj-1.516-report.md
- agents/tasks/LJ-1-516/review-of-graphSat-transports.md
- agents/tasks/LJ-1-516/runs/

## PREMISES

1. `[LJ-1.514]` is GO and names this as a separate obligation. Basis: agents/tasks/LJ-1-514/lj-1.514-report.md:264
2. `liftFo-correct` is the equation to spend. Basis: src/FOL/Manipulation/Bounding.lagda.md:198
3. `Relabel` is the instrument the tree uses. Basis: src/FOL/Manipulation/Bounding.lagda.md:146
4. Its own prose names this instance. Basis: src/FOL/Manipulation/Bounding.lagda.md:135
5. `liftFo` is the partial map over the constants. Basis: src/FOL/Manipulation/Bounding.lagda.md:162
6. The census is done and the count is 664. Basis: agents/tasks/LJ-1-514/lj-1.514-report.md:33
7. `countFo` is the tree's counter. Basis: src/FOL/Manipulation/Parameters.lagda.md:74
8. The stage side condition is named by the predecessor. Basis: agents/tasks/LJ-1-514/lj-1.514-report.md:257
9. `⊨-map` is delivered and used at this frame. Basis: src/L/Hull.lagda.md:176
10. `hier-in-stage` is still open and this task does not touch it. Basis: agents/tasks/LJ-1-494/lj-1.494-report.md:127
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THE CHEAPER OF THE TWO CONDENSATION BLOCKERS IS GONE.** `[LJ-1.514]` reports
that the Formula-carrier wall "is GONE, and it is gone for the family": the
answer applies to ANY `Formula CS.S n` and `LsetGraphAt` is not special.
**`hier-in-stage` remains, and it is the other one.**

## THE REASONING

**D-10, BEFORE ANY AGDA.** `liftFo-correct` equates two `mapFo` images. Say at
`file:line` what each side is and which of them a satisfaction statement can
consume. **If the equation relates formulas where a satisfaction law needs
models, name the gap and STOP**: that would say the two instruments do not
compose, which is worth more than a term built across a seam.

**DO NOT REBUILD `graphFo-at-SL`.** `[LJ-1.514]` built it. Rebuild only what
this obligation needs, and do not import a probe.

**DO NOT ATTEMPT `hier-in-stage`, `GraphSatAtStage` OR `cover`.**
`[LJ-1.494]` measured the first and `[LJ-1.492]` the third. This task is one
equation, not the leg.

**DO NOT ORDER `coverFo`, `code-of` OR `ambient-level` AGAIN.** `[LJ-1.492]`
forbids it and two later reports repeat the prohibition.

**REQUIRED REPORT SECTION `## WHAT THE CONDENSATION LEG OWES NOW`.** After this
task, name every remaining object between the tree and `cover`, as types, with
`file:line` for each that is delivered. **Do not price them.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 140 lines in the probe, of which the obligation is
about 40. BASIS: `[LJ-1.514]` built the `Relabel` instance and the census in 86
non-blank non-comment lines. Comparables are of SHAPE and nothing may be funded
against them.

## W3, THE WIDEST UNMEASURED TERM

It is the seam between `liftFo-correct` and `⊨-map`, because each is delivered
and nobody has put them end to end.

    -- liftFo-correct's equation, fed to the ⊨-map law at this frame

**Write it FIRST, with the obligation omitted, and typecheck it ALONE.** If the
two do not compose, the task stops at its cheapest point and the report carries
the seam as a type.

ESTIMATE for W3: about 25 lines and under 40 seconds. **Do not fund it against
`[LJ-1.514]`'s census run**: that counted constants and this composes two laws.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO MAKES THE TRANSPORTED FORMULA SAY WHAT THE ORIGINAL SAYS**, without
which `[LJ-1.514]`'s result is a formula nobody can use.

**A NO-GO NAMES THE SEAM BETWEEN TWO DELIVERED LAWS**, which would be a fact
about the tree's own manipulation chapters rather than about condensation, and
it would bear on every future transport, not just this one.

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
  # DELTA KEY ADDED 2026-08-22. Without it this row matches an acceptance
  # failure that delivered NOTHING, escalates, and matches again: MEASURED on
  # LJ-1.497, four times to attempt_max in six minutes, every one exit 1 with
  # delta 0. The row exists for the LJ-1.469 case, where the obligation WAS
  # delivered (delta -1) and acceptance failed. Keep it to that case.
  obligations_delta_max = -1
  changed_files_none = ["agents/tasks/LJ-1-516/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-516/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-516/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-516/Probe516.agda"]
  changed_files_none = ["agents/tasks/LJ-1-516/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-516/review-of-*.md"]

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
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 196.624)
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 181.999)
- CANDIDATE archive/dev/JOURNAL.md  (score 167.443)
- CANDIDATE dev/ARCHIVE.md  (score 153.765)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 149.211)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 61.885)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 58.270)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 52.584)
- CANDIDATE dev/literature/terms-2026-08.md  (score 51.129)
- CANDIDATE dev/literature/digest.md  (score 45.289)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
