# LJ-1.486: the bound the rank carve has never had

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-486/Probe486.agda`:

    rank-bound :
        (a : S) (oa : IsOrd (fst a))
      → Σ[ bnd ∈ S ]
          ((m : S) → ⟨ fst m ∈ˢ fst a ⟩
            → ⟨ pr (fst m) (swo-rank w m) ∈ fst bnd ⟩)

a set that contains every pair of a member and its rank, so the rank carve has a
bound to separate inside. Take the rank at `[LJ-1.416]`'s delivered type. Land
nothing in `src/`.

**TWO REPORTS HAVE NOW STOPPED FOR WANT OF THIS ONE SET.** `[LJ-1.478]` carved
`rank-graph` with `bnd` a parameter and did not inhabit it. `[LJ-1.482]` is a
critic-upheld NO-GO on the fourth `InjCode` conjunct
(`agents/tasks/LJ-1-482/lj-1.482-report.md:97`): its W3 `from-out` typechecks but
does not reach the range clause, and a close that treated pair-in-bound as
`y ∈ b` is `[UnequalTerms]`. **Its own report names the device**: `PairBound a C`
at `src/L/InjChain.lagda.md:276-297`, with `C` the `β` of `stage-into-bound` and
`a` the stage.

**READ `[LJ-1.482]` FIRST AND QUOTE ITS `## WHAT A CODE HERE WOULD REACH`.** If
its verdict is not a stated NO-GO, write nothing and stop.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-486/Probe486.agda::rank-bound"]

## SCOPE (write)
- agents/tasks/LJ-1-486/Probe486.agda
- agents/tasks/LJ-1-486/lj-1.486-report.md
- agents/tasks/LJ-1-486/review-of-rank-bound.md
- agents/tasks/LJ-1-486/runs/

## PREMISES

1. `[LJ-1.482]` is a critic-upheld NO-GO on the fourth conjunct and names the device for the bound. Basis: agents/tasks/LJ-1-482/lj-1.482-report.md:97
2. `PairBound` is delivered. Basis: src/L/InjChain.lagda.md:276
3. `[LJ-1.478]` is GO on the carve with `bnd` a parameter, and did not inhabit it. Basis: agents/tasks/LJ-1-478/lj-1.478-report.md:148
4. `[LJ-1.416]` builds the rank at the top level. Basis: agents/tasks/LJ-1-416/Probe416.agda:105
5. `[LJ-1.417]` bounds the rank into an ordinal, untruncated. Basis: agents/tasks/LJ-1-417/Probe417.agda:80
6. `[LJ-1.418]` instantiates that at EVERY stage. Basis: agents/tasks/LJ-1-418/Probe418.agda:64
7. `InclGraph` supplies its own bound from a stage bound, and that is the delivered pattern. Basis: src/L/InjChain.lagda.md:575
8. `ShiftGraph` does the same for the shift. Basis: src/L/Absorption.lagda.md:604
9. A measured cure does not transfer by analogy. Basis: dev/LESSONS.md:3752
10. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
11. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

Every carve in this tree that produced a code named its bound BEFORE it built the
set: `InclGraph` from a stage bound (`src/L/InjChain.lagda.md:575-598`),
`ShiftGraph` the same (`src/L/Absorption.lagda.md:604-605`). **The rank carve is
the only one that took the bound as a parameter**, and both tasks that used it
stopped at the same place.

## WHAT IS MISSING

The set. `[LJ-1.417]` bounds the RANKS into an ordinal; nothing bounds the PAIRS.

## THE REASONING

**D-10, BEFORE ANY AGDA.** `[LJ-1.417]`'s `swo-into-ord` gives an ordinal `β`
containing every rank (`Probe417.agda:80-88`). A pair `pr m r` with `m ∈ a` and
`r ∈ β` lives in a bound built from `a` and `β`. **Say, at `file:line`, whether
`PairBound a C` is exactly that, and what it needs that this telescope does not
give.** If `PairBound` wants something the rank does not supply, name it and
STOP.

**THE SHAPE.** Rebuild the rank at `[LJ-1.416]`'s delivered type. Take
`[LJ-1.417]`'s bounding ordinal at its delivered type, or as a module hypothesis,
and say which. Apply `PairBound`. Do not import a probe. **Do not carve and do
not build any `InjCode` conjunct.**

**DO NOT POSTULATE AND DO NOT WIDEN THE BOUND TO A CLASS.** A bound separation
can use must be a set this tree can name.

**REQUIRED REPORT SECTION `## WHAT THE FOURTH CONJUNCT NOW COSTS`.** With the
bound in hand, restate `[LJ-1.482]`'s range clause and say whether it closes.
**Do not close it**: that is the next brief, and it must be written against a
measured bound rather than a hoped one.

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 130 lines in the probe, of which the obligation is
about 25. BASIS: `src/L/InjChain.lagda.md:575-598` is 24 lines for the same move
at the inclusion, and `[LJ-1.478]`'s probe reached its GO in about 130.
Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is whether `PairBound`'s telescope is the rank's.

    fits : the `PairBound a C` application, type only

**Write the application with the body omitted and typecheck the TYPE alone.**
`PairBound` was built for `InclGraph`, whose pairs are `(x , x)` at one set.
**The rank's pairs are `(m , rank m)` across two**, and C-42 rules that a device
measured at one site does not transfer to another by analogy. If the arities
differ, that is the finding.

ESTIMATE for W3: about 8 lines and under 15 seconds.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO UNBLOCKS TWO STOPPED TASKS AT ONCE**, and the fourth conjunct becomes a
question about a named set instead of about a parameter.

**A NO-GO SAYS THE DELIVERED BOUND DEVICE DOES NOT REACH THE RANK**, which would
mean the rank route needs its own bound construction, and that is a larger and
nameable piece of work.

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
  changed_files_none = ["agents/tasks/LJ-1-486/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-486/review-of-*.md"]
  # THE CRITIC'S OWN RETURN MUST NOT RE-MATCH. It writes
  # `review-of-LJ-1-486-<k>.md` beside the coder's leftover `review-of-*.md`.
  # Without this exclusion the escalation re-escalates itself and `attempt_max`
  # parks the task PERMANENTLY. MEASURED 2026-08-21 on LJ-1.448, 449, 450, 451.
  changed_files_none = ["agents/tasks/LJ-1-486/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-486/Probe486.agda"]
  changed_files_none = ["agents/tasks/LJ-1-486/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-486/review-of-*.md"]

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
