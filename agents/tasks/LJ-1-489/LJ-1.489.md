# LJ-1.489: does the collapse commute with the definable powerset

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-489/Probe489.agda`:

    piCommuteD :
        (y : S) → ⟨ y ∈ˢ M ⟩ → C.π (𝒟ₒ y) ≡ 𝒟ₒ (C.π y)

where `M` is the definable hull and `C = Collapse M`, exactly as
`src/L/BoundedSubset.lagda.md:903-916` builds them. Land nothing in `src/`.

**`[LJ-1.477]` NAMED THIS AS ONE OF TWO NEEDS AND NOBODY HAS ATTEMPTED IT.** That
critic-upheld NO-GO measured that the two computation laws spend and do not join,
and then said what a proof of the commutation at that site actually needs:
"**it needs `π` to commute with `𝒟ₒ`**, and it needs `Lset-out` witnesses to lie
in `M`" (`agents/tasks/LJ-1-477/lj-1.477-report.md:312`, committed `b12a15e`).

**THE SECOND NEED IS `[LJ-1.487]`'s WORK, IN FLIGHT. THIS IS THE FIRST, AND IT IS
INDEPENDENT OF IT.** `𝒟ₒ` is the definable powerset step of the tower
(`src/L/Constructible.lagda.md:212`), sealed `opaque` with `Lset-compute` as its
official unfolding (`:201-207`).

**READ `[LJ-1.477]` FIRST AND QUOTE ITS `## 4. What the next brief needs`.** If
its verdict is not a stated NO-GO, write nothing and stop.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-489/Probe489.agda::piCommuteD"]

## SCOPE (write)
- agents/tasks/LJ-1-489/Probe489.agda
- agents/tasks/LJ-1-489/lj-1.489-report.md
- agents/tasks/LJ-1-489/review-of-piCommuteD.md
- agents/tasks/LJ-1-489/runs/

## PREMISES

1. `[LJ-1.477]` is a critic-upheld NO-GO and it names this as one of two needs. Basis: agents/tasks/LJ-1-477/lj-1.477-report.md:312
2. It measured that the two computation laws spend and do not join. Basis: agents/tasks/LJ-1-477/Probe477.agda:90
3. It also measured that the exported law spends WITHOUT opening the seal. Basis: agents/tasks/LJ-1-477/lj-1.477-report.md:305
4. `𝒟ₒ` is the tower's definable powerset step, sealed. Basis: src/L/Constructible.lagda.md:212
5. The tower's step is a union of `𝒟ₒ` over the members. Basis: src/L/Constructible.lagda.md:58
6. `π` is sealed and defined by `∈`-induction. Basis: src/V/Collapse.lagda.md:52
7. Its computation law is exported and the chapter spends it three times. Basis: src/V/Collapse.lagda.md:58
8. `π-member` reads a collapse value back to a carrier member. Basis: src/V/Collapse.lagda.md:63
9. The hull is NOT transitive, measured. Basis: agents/tasks/LJ-1-160/lj-1.160-report.md:248
10. `levelIn` step 4 is the consumer of this, and it is unbuilt. Basis: agents/tasks/LJ-1-462/Probe462.agda:139
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

`[LJ-1.477]` did the work of finding out what step 4 needs, and it named two
things. **One of them has been in flight since `[LJ-1.487]`; the other has never
been looked at.** Its own measurements also clear two false leads: the seal does
not need opening, and hull closure under `Lset` does not change the join.

## WHAT IS MISSING

The commutation at the powerset step, which is one layer below the one
`[LJ-1.477]` attempted.

## THE REASONING

**D-10, BEFORE ANY AGDA, AND THE STATEMENT MAY BE FALSE.** `𝒟ₒ y` is the set of
subsets of `y` definable over `y`. `C.π` sends a set to the image of its
members. **These commute only if the collapse preserves definability over `y`,
which is an absoluteness claim about the hull and not a computation.** Write out
what each side unfolds to, at `file:line`, and say in one line whether they can
agree without elementarity. **If they cannot, say so and STOP: that is the
finding, and it closes `levelIn` step 4 by a second route.**

**THE SHAPE.** Rebuild the telescope down to `C = Collapse M`, copying
`src/L/BoundedSubset.lagda.md:903-916` as `[LJ-1.477]` did. Do W3 first. Do not
import a probe.

**DO NOT OPEN EITHER SEAL.** `[LJ-1.477]` measured that the exported laws spend
without unfolding, at 1.97 s and 473 MB. **If you find yourself needing an
`unfolding`, stop and report that instead**: it is the heap-cost shape
`[LJ-1.398]` met at 8 GB.

**DO NOT TAKE `HullClosedLset` OR `CoverWitnessesInHull` AS A HYPOTHESIS.** The
first `[LJ-1.477]` measured as irrelevant to the join; the second is
`[LJ-1.487]`'s obligation and assuming it makes this return worthless.

**DO NOT POSTULATE.**

**REQUIRED REPORT SECTION `## WHAT STEP FOUR NOW NEEDS`.** State, as types, both
of `[LJ-1.477]`'s two needs with this one marked BUILT or UNBUILT, and say
whether step 4 is now reachable, blocked on one need, or blocked on both. **Do
not claim `levelIn` and do not claim step 4.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 150 lines in the probe, of which the obligation is
about 40. BASIS: `[LJ-1.477]` rebuilt this same telescope and reached its join
measurement in 35 non-blank non-comment lines of new content over a comparable
file. Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is one direction, not the equation.

    one-way : (y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ C.π (𝒟ₒ y) ⊆ˢ 𝒟ₒ (C.π y) ⟩

**Write the easier inclusion FIRST, with the obligation omitted, and typecheck it
ALONE.** A definable subset of `y` collapses to a set of collapsed members; **the
question is whether it is still DEFINABLE over `C.π y`, and that is where
elementarity would be needed.** If even this direction fails, the equation is out
of reach and the task stops at its cheapest point. **Say which direction you
tried and why.**

ESTIMATE for W3: about 15 lines and under 25 seconds. **Do not fund it against
`[LJ-1.477]`'s 1.97 s**: that measured a law application, not an inclusion.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO LEAVES `levelIn` STEP 4 BLOCKED ON ONE NEED INSTEAD OF TWO**, and that one
is already in flight.

**A NO-GO CLOSES STEP 4 BY A SECOND, INDEPENDENT ROUTE**, which would mean
`[LJ-1.462]`'s four-step decomposition is wrong at step 4 and `levelIn` must be
re-decomposed. That is a larger and more useful result than the term.

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
  changed_files_none = ["agents/tasks/LJ-1-489/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-489/review-of-*.md"]
  # THE CRITIC'S OWN RETURN MUST NOT RE-MATCH. It writes
  # `review-of-LJ-1-489-<k>.md` beside the coder's leftover `review-of-*.md`.
  # Without this exclusion the escalation re-escalates itself and `attempt_max`
  # parks the task PERMANENTLY. MEASURED 2026-08-21 on LJ-1.448, 449, 450, 451.
  changed_files_none = ["agents/tasks/LJ-1-489/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-489/Probe489.agda"]
  changed_files_none = ["agents/tasks/LJ-1-489/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-489/review-of-*.md"]

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
