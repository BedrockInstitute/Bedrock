# LJ-1.497: the bridge the range clause wants, from rankFo to swo-rank

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-497/Probe497.agda`:

    rankFo-adequate :
        (Q a z : S)
      → ⟨ (z ∷ []) ⊨ rankFo Q a ⟩
      → (the reading that z is the pair of a member of `a` and its `swo-rank`)

**the adequacy of `rankFo` to `swo-rank`.** `[LJ-1.490]`'s own report names this
as the bridge to fund FIRST. Land nothing in `src/`.

**`[LJ-1.490]` IS A CRITIC-UPHELD NO-GO AND IT NAMED THIS TASK.** Its verdict:
`from-out` typechecks and the `range-clause` type forms, but the range clause has
no term, because a close that treats the pair-in-bound as the
second-component-in-codomain is `[UnequalTerms]`
(`agents/tasks/LJ-1-490/lj-1.490-report.md:80-86`). Its own next-brief section
says: **"The range clause wants the adequacy of `rankFo` to `swo-rank`, which
`[LJ-1.475]` left. Fund that bridge first."** Its critic says the same at
`agents/tasks/LJ-1-490/review-of-LJ-1-490-1.md:194`.

**MY PREVIOUS BRIEF CARRIED A PREMISE THAT THIS MEASUREMENT DOES NOT SUPPORT,
AND YOU MUST NOT INHERIT IT.** `[LJ-1.490]`'s report says the other three
conjuncts read the graph as a function, which also reads the second component of
a pair in the carve, so they want the SAME adequacy; and it says plainly that
"the brief's premise that three were already reachable at `[LJ-1.482]` is not
supported by this measurement". **Treat all four conjuncts as waiting on this
bridge.**

**`rankFo` AND `swo-rank` ARE BOTH DELIVERED IN 490's PROBE.** `rankFo` at
`agents/tasks/LJ-1-490/Probe490.agda:95-96`, `swo-rank` at `:147-148` (rebuilt at
`[LJ-1.416]`'s delivered type), `rank-graph` at `:105-109` and `rank-graph-out`
at `:111-114`. **Rebuild them. Do not import a probe.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-497/Probe497.agda::rankFo-adequate"]

## SCOPE (write)
- agents/tasks/LJ-1-497/Probe497.agda
- agents/tasks/LJ-1-497/lj-1.497-report.md
- agents/tasks/LJ-1-497/review-of-rankFo-adequate.md
- agents/tasks/LJ-1-497/runs/

## PREMISES

1. `[LJ-1.490]` is a critic-upheld NO-GO at the fourth conjunct. Basis: agents/tasks/LJ-1-490/lj-1.490-report.md:80
2. Its report names this adequacy as the bridge to fund first. Basis: agents/tasks/LJ-1-490/lj-1.490-report.md:281
3. Its critic names the same order of work. Basis: agents/tasks/LJ-1-490/review-of-LJ-1-490-1.md:194
4. It reports that the three other conjuncts want the same adequacy. Basis: agents/tasks/LJ-1-490/lj-1.490-report.md:275
5. `rankFo` is delivered in that probe. Basis: agents/tasks/LJ-1-490/Probe490.agda:95
6. `swo-rank` is delivered in that probe. Basis: agents/tasks/LJ-1-490/Probe490.agda:147
7. `rank-graph` separates the bound at that formula. Basis: agents/tasks/LJ-1-490/Probe490.agda:105
8. `rank-graph-out` is the delivered reading of that separation. Basis: agents/tasks/LJ-1-490/Probe490.agda:111
9. `[LJ-1.475]` is GO on the rank formula and left the adequacy. Basis: agents/tasks/LJ-1-475/lj-1.475-report.md:107
10. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
11. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**SIX DISPATCHES BUILT THIS ROUTE AND EACH CLOSED THE ONE BEFORE**: `[LJ-1.468]`
the one-slot formula, `[LJ-1.471]` the order as a set, `[LJ-1.475]` the rank
formula, `[LJ-1.478]` the carve, `[LJ-1.486]` the bound, `[LJ-1.490]` the fourth
conjunct. **The seventh is the bridge the sixth asked for**, and it is the only
thing standing between the delivered pieces and all four conjuncts.

## WHAT IS MISSING

The reading of the formula as the rank.

## THE REASONING

**D-10, BEFORE ANY AGDA.** `[LJ-1.475]` is GO on `rank-formula` and left the
adequacy unbuilt. Say at `file:line` what its formula asserts, slot by slot, and
what `swo-rank` computes. **If the formula asserts something `swo-rank` does not
compute, STOP AND SAY WHICH SLOT DIVERGES.** A bridge between two things that do
not correspond cannot be built, and naming the divergence is the deliverable.

**BUILD THE `out` DIRECTION FIRST.** Satisfaction to the rank reading is what the
range clause consumes. The `in` direction is not this obligation and you should
not attempt it.

**DO NOT POSTULATE AND DO NOT WEAKEN THE RANK TO A BOUND.** `[LJ-1.475]` refused
that and its refusal stands.

**DO NOT CLAIM `InjCode`, DO NOT CLAIM A LIMIT, DO NOT CLAIM `Residue`.**
`[LJ-1.490]` forbids all three and its own report says those questions wait on a
code.

**REQUIRED REPORT SECTION `## WHAT THE RANGE CLAUSE NEEDS NEXT`.** State, as a
type, what remains between this bridge and `range-clause`, and say whether `b`
is still free or is now determined as the bounding ordinal. **Do not attempt
`range-clause`.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 170 lines in the probe, of which the obligation is
about 45, the rest being the rebuilt rank and formula. BASIS: `[LJ-1.490]` built
the rank, the formula, the carve and the bound in one file. Comparables are of
SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the rank at a member, because `swo-rank` is a well-founded recursion and
the formula reads a pair.

    rank-at : (a z : S) → (the value swo-rank assigns, as an S)

**Write it FIRST, with the obligation omitted, and typecheck it ALONE.** If the
recursion will not reduce at a slot the formula can name, the bridge cannot be
stated and the task stops at its cheapest point.

ESTIMATE for W3: about 30 lines and under 45 seconds. **Do not fund it against
`[LJ-1.490]`'s W3**: that measured a range clause and this measures a recursion.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO UNBLOCKS ALL FOUR CONJUNCTS AT ONCE**, because `[LJ-1.490]` measured that
each of them reads the second component of a pair in the carve and wants this
same adequacy.

**A NO-GO SAYS THE RANK FORMULA AND THE RANK DO NOT CORRESPOND**, which would
retire `[LJ-1.475]`'s formula rather than extend it, and would be the first
measurement to say the coded-injection route needs a different rank.

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
  changed_files_none = ["agents/tasks/LJ-1-497/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-497/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-497/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-497/Probe497.agda"]
  changed_files_none = ["agents/tasks/LJ-1-497/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-497/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 188.401)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 173.304)
- CANDIDATE archive/dev/JOURNAL.md  (score 146.211)
- CANDIDATE dev/ARCHIVE.md  (score 142.766)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 136.646)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 53.473)
- CANDIDATE dev/literature/digest.md  (score 39.554)
- CANDIDATE dev/literature/terms-2026-08.md  (score 38.383)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 34.024)
- CANDIDATE dev/literature/geology.md  (score 28.564)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
