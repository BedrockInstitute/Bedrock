# LJ-1.482: is the carved rank a code, and does it reach a limit

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-482/Probe482.agda`:

    rank-coded :
        (Q a bnd b : S)
      → (readings hold as `[LJ-1.478]` delivers them)
      → InjCode (rank-graph Q a bnd) a b

the four `InjCode` conjuncts on top of the carved rank graph. State the
telescope from `[LJ-1.478]`'s delivered readings and not from this sketch. Land
nothing in `src/`.

**`[LJ-1.478]` CARVED THE GRAPH AND REFUSED TO CLAIM THE CODE.** It is GO
(`agents/tasks/LJ-1-478/lj-1.478-report.md:148`, committed `a7059a5`):
`rank-graph` inhabits the unique `SetOf` of the carve
(`Probe478.agda:105-109`) and both directions read back (`:111-124`). Its own
report records "I did not claim `InjCode`". **This task asks exactly that and
nothing more.**

**THE PATTERN IS DELIVERED AND GREEN.** `[LJ-1.460]` built the four conjuncts on
top of a carved graph for the shift, and its body took them straight from the
carve's exports (`agents/tasks/LJ-1-460/Probe460.agda:73-88`). **Follow that
shape, and re-measure it here**: C-42 rules that a measured cure does not
transfer by analogy.

**READ `[LJ-1.478]` AND `[LJ-1.460]` FIRST.** If either verdict is not `GO`,
write nothing and stop.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-482/Probe482.agda::rank-coded"]

## SCOPE (write)
- agents/tasks/LJ-1-482/Probe482.agda
- agents/tasks/LJ-1-482/lj-1.482-report.md
- agents/tasks/LJ-1-482/review-of-rank-coded.md
- agents/tasks/LJ-1-482/runs/

## PREMISES

1. `[LJ-1.478]` is GO on the carved rank graph with both readings. Basis: agents/tasks/LJ-1-478/lj-1.478-report.md:148
2. Its delivered terms are at the probe that typechecked. Basis: agents/tasks/LJ-1-478/Probe478.agda:105
3. `[LJ-1.460]` is GO on the four conjuncts over a carved graph, for the shift. Basis: agents/tasks/LJ-1-460/lj-1.460-report.md:108
4. Its body takes all four from the carve's exports and adds no hypothesis. Basis: agents/tasks/LJ-1-460/Probe460.agda:81
5. `InjCode` is four conjuncts and only the fourth mentions the codomain. Basis: src/L/Cardinal.lagda.md:223
6. `[LJ-1.417]` delivers an UNTRUNCATED injection into an ordinal from the rank. Basis: agents/tasks/LJ-1-417/Probe417.agda:80
7. `[LJ-1.418]` instantiates that at EVERY stage, with no band and no infiniteness. Basis: agents/tasks/LJ-1-418/lj-1.418-report.md:18
8. `[LJ-1.464]` records that the shift route provably cannot reach a limit. Basis: agents/tasks/LJ-1-464/lj-1.464-report.md:89
9. A measured cure does not transfer by analogy. Basis: dev/LESSONS.md:3752
10. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
11. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**A THREE-STEP ROUTE CLOSED IN THREE CONSECUTIVE DISPATCHES.** `[LJ-1.468]` gave
the order a one-slot formula, `[LJ-1.471]` carved the order, `[LJ-1.475]`
described the rank over it, and `[LJ-1.478]` carved the rank. Each was the named
obstruction of the one before.

**AND THE RANK IS THE ONLY DEVICE IN THIS TREE THAT REACHES A LIMIT.**
`[LJ-1.418]`'s injection is at every stage; the shift code reaches successors
only, and `[LJ-1.464]` measured that it provably cannot do better.

## WHAT IS MISSING

The four conjuncts.

## THE REASONING

**D-10, BEFORE ANY AGDA.** `[LJ-1.460]` got its four conjuncts from
`ShiftGraph`'s exports because that carve was built to serve `InjCode`.
**`[LJ-1.478]`'s carve was built to serve a rank description and nothing else.**
List the four conjuncts and, for each, name the delivered reading that supplies
it, at `file:line`. **If one has no supplier, name it and STOP.** That is the
finding and it is worth more than the obligation.

**THE SHAPE.** Rebuild `[LJ-1.478]`'s carve at its delivered type, or take the
readings as module hypotheses at their delivered types and say which you did.
Build the conjuncts. Do not import a probe. **Do not build the bound**: it is a
parameter here as it was there.

**DO NOT CLAIM A LIMIT AND DO NOT CLAIM `Residue`.** This task is about one code
at one carve. **Whether it reaches a limit stage is a separate question**, and it
depends on the bound, which nobody has supplied at any stage.

**DO NOT POSTULATE AND DO NOT ADD A HYPOTHESIS TO CLOSE A CONJUNCT.**

**REQUIRED REPORT SECTION `## WHAT A CODE HERE WOULD REACH`.** State, as types,
what would still be needed to get a coded injection at a LIMIT stage: the bound,
and `[LJ-1.418]`'s instantiation. **Do not price it from this task's seconds.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 160 lines in the probe, of which the obligation is
about 45. BASIS: `agents/tasks/LJ-1-460/Probe460.agda` built the same four
conjuncts over a carved graph and its term is 16 lines under a rebuilt carve;
`[LJ-1.478]`'s probe reached its GO in about 130. Comparables are of SHAPE.

## W3, THE WIDEST UNMEASURED TERM

It is the fourth conjunct, the range clause, as it was for the shift.

    range-clause :
      (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (rank-graph Q a bnd) ⟩
                → ⟨ fst y ∈ fst b ⟩

**Write it FIRST from `[LJ-1.478]`'s `rank-graph-out` alone, with the obligation
omitted, and typecheck it ALONE.** The rank's values are ORDINALS and the
codomain `b` must contain them; **`[LJ-1.478]` did not supply a bound and this
clause is where that absence bites.** If the clause needs the bound to be an
ordinal containing every rank, say so: that is a condition on `bnd` and it is
the finding.

ESTIMATE for W3: about 14 lines and under 20 seconds.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO GIVES THIS TREE ITS SECOND CODE FOR A NON-IDENTITY INJECTION**, and the
first one built on a device that is defined at every stage rather than at
successors only.

**A NO-GO NAMES THE CONJUNCT THE RANK CARVE CANNOT SUPPLY**, which would say the
carve serves a description and not a code, and that the two need different
bounds.

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
  changed_files_none = ["agents/tasks/LJ-1-482/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-482/review-of-*.md"]
  # THE CRITIC'S OWN RETURN MUST NOT RE-MATCH. It writes
  # `review-of-LJ-1-482-<k>.md` beside the coder's leftover `review-of-*.md`.
  # Without this exclusion the escalation re-escalates itself and `attempt_max`
  # parks the task PERMANENTLY. MEASURED 2026-08-21 on LJ-1.448, 449, 450, 451.
  changed_files_none = ["agents/tasks/LJ-1-482/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-482/Probe482.agda"]
  changed_files_none = ["agents/tasks/LJ-1-482/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-482/review-of-*.md"]

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
