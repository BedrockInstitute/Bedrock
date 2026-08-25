# LJ-1.490: the fourth conjunct, now that the bound exists

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-490/Probe490.agda`:

    rank-coded :
        (a : S) (oa : IsOrd (fst a)) (b : S)
      → InjCode (rank-graph Q a (fst (rank-bound a oa))) a b

the four `InjCode` conjuncts over the rank carve, with the bound taken from
`[LJ-1.486]`'s delivered term instead of left a parameter. State the telescope
from the two delivered probes and not from this sketch. Land nothing in `src/`.

**`[LJ-1.482]` FAILED ON THE FOURTH CONJUNCT FOR WANT OF EXACTLY THIS BOUND, AND
`[LJ-1.486]` HAS NOW BUILT IT.** 482 is a critic-upheld NO-GO
(`agents/tasks/LJ-1-482/lj-1.482-report.md:97`): `from-out` typechecks and does
not reach the range clause, and a close treating pair-in-bound as `y ∈ b` is
`[UnequalTerms]`. **486 is GO** (`agents/tasks/LJ-1-486/lj-1.486-report.md:160`,
committed `c3c07e5`): `PairBound`'s arities match, and `rank-bound` inhabits a
set containing every pair of a member and its rank
(`agents/tasks/LJ-1-486/Probe486.agda:169-194`).

**READ BOTH REPORTS FIRST.** If `[LJ-1.486]`'s verdict is not `GO`, write nothing
and stop.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-490/Probe490.agda::rank-coded"]

## SCOPE (write)
- agents/tasks/LJ-1-490/Probe490.agda
- agents/tasks/LJ-1-490/lj-1.490-report.md
- agents/tasks/LJ-1-490/review-of-rank-coded.md
- agents/tasks/LJ-1-490/runs/

## PREMISES

1. `[LJ-1.486]` is GO on the bound and its arities match `PairBound`. Basis: agents/tasks/LJ-1-486/lj-1.486-report.md:160
2. Its delivered term is at the probe that typechecked. Basis: agents/tasks/LJ-1-486/Probe486.agda:169
3. `[LJ-1.482]` is a critic-upheld NO-GO on the fourth conjunct for want of that bound. Basis: agents/tasks/LJ-1-482/lj-1.482-report.md:97
4. `[LJ-1.478]` is GO on the carve with both readings. Basis: agents/tasks/LJ-1-478/Probe478.agda:105
5. `InjCode` is four conjuncts and only the fourth mentions the codomain. Basis: src/L/Cardinal.lagda.md:223
6. `[LJ-1.460]` built the same four over a carved graph for the shift, from the carve's own exports. Basis: agents/tasks/LJ-1-460/Probe460.agda:81
7. `[LJ-1.417]` bounds the rank into an ordinal, untruncated. Basis: agents/tasks/LJ-1-417/Probe417.agda:80
8. `[LJ-1.418]` instantiates that at EVERY stage, with no band and no infiniteness. Basis: agents/tasks/LJ-1-418/lj-1.418-report.md:18
9. `[LJ-1.464]` records that the shift route provably cannot reach a limit. Basis: agents/tasks/LJ-1-464/lj-1.464-report.md:89
10. A measured cure does not transfer by analogy. Basis: dev/LESSONS.md:3752
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**FIVE CONSECUTIVE DISPATCHES BUILT THIS ROUTE AND EACH CLOSED THE ONE BEFORE.**
`[LJ-1.468]` the one-slot order formula, `[LJ-1.471]` the order as a set,
`[LJ-1.475]` the rank formula, `[LJ-1.478]` the rank carve, `[LJ-1.486]` the
bound. **The only thing between the carve and a code is the four conjuncts, and
three of them were already reachable at `[LJ-1.482]`.**

## WHAT IS MISSING

The fourth conjunct, and the three beside it restated against a named bound.

## THE REASONING

**D-10, BEFORE ANY AGDA.** `[LJ-1.482]`'s W3 `from-out` typechecked but did not
inhabit the range clause, and the false close it tried is recorded at
`runs/w3-false-close.out`. **Read that measurement and say, in one line, what the
bound now supplies that it lacked.** If the bound does not close the clause, the
finding is that `PairBound`'s membership is not the codomain membership
`InjCode` wants, and that is worth more than the obligation.

**THE SHAPE.** Rebuild `[LJ-1.478]`'s carve and `[LJ-1.486]`'s bound at their
delivered types, or take them as module hypotheses and say which. Build the four
conjuncts. Do not import a probe.

**DO NOT CLAIM A LIMIT AND DO NOT CLAIM `Residue`.** A code at a carve is not a
code at a stage; `[LJ-1.418]`'s instantiation is a separate step and this task
does not take it.

**DO NOT POSTULATE AND DO NOT ADD A HYPOTHESIS TO CLOSE A CONJUNCT.**

**REQUIRED REPORT SECTION `## WHAT A LIMIT WOULD NOW COST`.** State, as types,
what remains between this term and a coded injection at a LIMIT stage:
`[LJ-1.418]`'s instantiation, and whatever the bound needs at a limit. **Do not
price it from this task's seconds** and do not attempt it.

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 180 lines in the probe, of which the obligation is
about 50. BASIS: `[LJ-1.482]` reached three conjuncts in a comparable file and
`[LJ-1.486]` is about 200; this file carries both. Comparables are of SHAPE and
nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the fourth conjunct alone, again, because it is the one that failed.

    range-clause :
      (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (rank-graph Q a bnd) ⟩
                → ⟨ fst y ∈ fst b ⟩

**Write it FIRST with `bnd` the delivered `rank-bound`, with the other three
conjuncts and the obligation omitted, and typecheck it ALONE.** `[LJ-1.486]`'s
bound contains pairs; the clause wants the SECOND component in `b`. **Say at
`file:line` how you get from one to the other, and if it needs `b` to be
`[LJ-1.417]`'s bounding ordinal, say so**: that would make `b` determined rather
than free, and the obligation's telescope must then change.

ESTIMATE for W3: about 16 lines and under 25 seconds. **Do not fund it against
`[LJ-1.482]`'s 1.55 s**: that measured a term that did not close.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO GIVES THIS TREE ITS SECOND CODE FOR A NON-IDENTITY INJECTION**, built on
a device defined at every stage rather than at successors only, and it makes the
limit question askable for the first time.

**A NO-GO SAYS THE BOUND IS NOT THE CODOMAIN**, which would mean `PairBound`
serves the carve and not the code, and the two need different sets.

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
  changed_files_none = ["agents/tasks/LJ-1-490/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-490/review-of-*.md"]
  # THE CRITIC'S OWN RETURN MUST NOT RE-MATCH. It writes
  # `review-of-LJ-1-490-<k>.md` beside the coder's leftover `review-of-*.md`.
  # Without this exclusion the escalation re-escalates itself and `attempt_max`
  # parks the task PERMANENTLY. MEASURED 2026-08-21 on LJ-1.448, 449, 450, 451.
  changed_files_none = ["agents/tasks/LJ-1-490/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-490/Probe490.agda"]
  changed_files_none = ["agents/tasks/LJ-1-490/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-490/review-of-*.md"]

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
