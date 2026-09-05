# LJ-1.523: price the last mile, from the bounded subset theorem to GCH

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-523/Probe523.agda`:

    GCHBridge : ModelL.isZFModel → Type (ℓ-suc ℓ)

**the type of the implication from the bounded subset theorem to
`GCHStatement`, stated with NO HOLES, and every input it names reported at
`file:line`.** Land nothing in `src/`, and **do not inhabit it**.

**THIS SEGMENT HAS NEVER BEEN TOUCHED AND THE OWNER ORDERED IT PRICED.**
Measured before this brief was written, and the command is
`grep -rn "GCHStatement\|SuccCardL" src --include='*.lagda.md'`:
**`GCHStatement` and `SuccCardL` occur in `src/` ONLY inside
`src/L/GCH.lagda.md`. Nothing reads them.** And `grep -rn "BoundedSubset" src`
shows the bounded subset work is consumed only by `src/L/StageBound.lagda.md`
(`:15`, `:74`) and listed in `src/Everything.lagda.md:395`. **The two ends are
not wired, and no dispatch has ever priced the wire.**

**THE TARGET, AT ITS OWN LINES.** `GCHStatement` (`src/L/GCH.lagda.md:59-70`)
says: for every ordinal L-cardinal `κ` not in `ω`, there is `δ` with
`SuccCardL δ κ` (`:46-53`), `InjL (𝒫 κ) δ` and `InjL δ (𝒫 κ)`.

**AND `InjL` REDUCES TO THE COUNTING LEG'S OWN OBJECT.**
`InjL a b = ∥ Σ[ F ∈ S ] InjCode F a b ∥₁` (`src/L/GCH.lagda.md:37-38`), and
`InjCode` comes from `L.Cardinal` (`:16`). **`InjCode` is what `[LJ-1.490]`,
`[LJ-1.497]`, `[LJ-1.515]`, `[LJ-1.518]` and `[LJ-1.521]` have been building
toward.** Say in your report whether the `InjCode` the counting leg is building
is the same `InjCode` this statement names, at `file:line`. **If it is not, that
is the most important sentence you will write.**

**THE SOURCE END.** `src/L/BoundedSubset.lagda.md:1621-1622` has
`theorem : ⟨ x ∈ˢ Lset κ ⟩`, inside a module whose telescope takes `levelIn`
and `cover` as HYPOTHESES (`:1555-1556`). **State the bridge from the theorem
as it stands, hypotheses and all. Do not discharge them and do not hide them.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-523/Probe523.agda::GCHBridge"]

## SCOPE (write)
- agents/tasks/LJ-1-523/Probe523.agda
- agents/tasks/LJ-1-523/lj-1.523-report.md
- agents/tasks/LJ-1-523/review-of-GCHBridge.md
- agents/tasks/LJ-1-523/runs/

## PREMISES

1. `GCHStatement` is the target and it has no proof term. Basis: src/L/GCH.lagda.md:59
2. `SuccCardL` is its successor cardinal clause. Basis: src/L/GCH.lagda.md:46
3. `InjL` reduces to `InjCode`. Basis: src/L/GCH.lagda.md:37
4. `InjCode` and `IsCardinalL` come from `L.Cardinal`. Basis: src/L/GCH.lagda.md:16
5. The bounded subset theorem exists. Basis: src/L/BoundedSubset.lagda.md:1621
6. It sits under the `levelIn` and `cover` hypotheses. Basis: src/L/BoundedSubset.lagda.md:1555
7. Those hypotheses are consumed inside the module. Basis: src/L/BoundedSubset.lagda.md:967
8. Only `StageBound` consumes the chapter. Basis: src/L/StageBound.lagda.md:15
9. `L ⊨ ZFC` is landed and is the neighbouring trophy. Basis: src/Landmarks.lagda.md:59
10. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
11. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**BOTH ENDS EXIST AND NEITHER REACHES THE OTHER.** The statement is written and
unread; the theorem is proved and consumed elsewhere. **Every dispatch of this
campaign has worked on the legs. This is the first to look at the join.**

## THE REASONING

**D-10, BEFORE ANY AGDA.** `GCHStatement` quantifies over ordinal L-cardinals
`κ` outside `ω`; the bounded subset theorem concludes `x ∈ˢ Lset κ` for one `x`
at one `κ`. **Say at `file:line` what the theorem's `x` and `κ` are bound by,
and whether its `κ` can be the statement's `κ`.** If the two `κ` cannot be the
same object, the bridge is not the implication this brief names and you must
say what it is instead.

**STATE IT, DO NOT PROVE IT.** The deliverable is the TYPE with no holes and
the input list. **A brief that ordered the proof would be pricing by building,
which is what this campaign has spent eleven dispatches learning not to do.**

**NAME EVERY INPUT AND SAY WHERE IT IS.** For each, one of: delivered in
`src/` at `file:line`; delivered in a probe at `file:line`; stated nowhere.
**"Stated nowhere" is the answer that matters most and you must not soften it.**

**DO NOT DISCHARGE `levelIn` OR `cover`.** They are the condensation leg's
work and it is running. Carry them into the bridge type as hypotheses.

**DO NOT BUILD OR REPAIR `InjCode`.** `[LJ-1.521]` holds the counting leg.

**DO NOT POSTULATE.**

**REQUIRED REPORT SECTION `## THE INPUT LIST`.** One row per input: its type,
its status by the three-way split above, and a `file:line` for the first two.
**This section is the deliverable even if the type does not form.**

**REQUIRED REPORT SECTION `## IS THE COUNTING LEG'S `InjCode` THIS ONE`.** One
sentence and a `file:line`. **The whole campaign's shape depends on the
answer.**

**REQUIRED REPORT SECTION `## WHAT IS STATED NOWHERE`.** The subset of the
input list with that status, and for each, one sentence on what kind of object
it is: a cardinal arithmetic fact, a coding fact, or something else. **Do not
price them in lines or seconds. That is the mathematician's.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 120 lines in the probe, of which the obligation is
about 40. BASIS: the type must open both chapters' telescopes, and `[LJ-1.517]`
re-declared seven types across two chapters in 86 non-blank non-comment lines.
Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is whether the two `κ` are the same object, because if they are not there is
no bridge of this shape and every later row of the input list is moot.

    kappa-agrees : (the theorem's κ, at the statement's binding)

**Write it FIRST, as a type, and typecheck it ALONE.** If the theorem's `κ`
carries hypotheses the statement's `κ` does not, list them: that difference is
the price and it is what the owner asked for.

ESTIMATE for W3: about 25 lines and under 40 seconds. **Do not fund it against
any predecessor**: no dispatch has opened both chapters at once.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO GIVES THE CAMPAIGN ITS FIRST MEASURED PICTURE OF THE JOIN**, and tells
the mathematician whether the three legs are converging on a reachable target
or on one that needs a fourth.

**A NO-GO AT THE TWO `κ` SAYS THE BOUNDED SUBSET THEOREM IS NOT WHAT GCH
CONSUMES**, which would re-price the whole campaign and is worth far more than
a type that forms.

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
  changed_files_none = ["agents/tasks/LJ-1-523/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-523/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-523/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-523/Probe523.agda"]
  changed_files_none = ["agents/tasks/LJ-1-523/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-523/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 247.846)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 231.939)
- CANDIDATE archive/dev/JOURNAL.md  (score 220.128)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 168.548)
- CANDIDATE archive/dev/DD-archived.md  (score 165.500)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 57.233)
- CANDIDATE dev/literature/geology.md  (score 56.344)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 49.643)
- CANDIDATE dev/literature/digest.md  (score 43.850)
- CANDIDATE dev/literature/devlin-errata.md  (score 40.802)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
