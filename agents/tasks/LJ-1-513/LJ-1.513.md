# LJ-1.513: re-base the order on membership, so the predecessor set forms at all

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-513/Probe513.agda`:

    preds : (a : S) → IsOrd (fst a) → S

**the set of predecessors of `a`, formed through `_∈ₛ_` rather than through
`SWO._<∙_`, and landing at the level a carrier needs.** Land nothing in `src/`.

**`[LJ-1.497]` IS A CRITIC-UPHELD NO-GO AND IT DID NOT FAIL, IT REFUTED.**
`rankFo-adequate` is FALSE and the refutation typechecks
(`agents/tasks/LJ-1-497/Probe497.agda:435-451`, exit 0). **`[LJ-1.490]`'s
instruction to "fund that bridge first" is retired**: what stands between the
tree and `range-clause` is not a bridge but a **replacement rank**, whose
bounding ordinal is taken over the PREDECESSORS only.

**AND `[LJ-1.497]` NAMED THIS TASK AND ITS ORDER.** Its own words: "The order
must be re-based on `_∈ₛ_` first. **That re-basing is the next brief, and it is
a coder task, not a bridge.**"

**THE BLOCKER IS A UNIVERSE LEVEL AND IT IS ALREADY MEASURED.**
`agents/tasks/LJ-1-497/runs/cure-level.out` reads:

    Probe497.agda:461.12-31: error: [UnequalSorts]
    Type (ℓ-suc ℓ) != Type ℓ
    when checking that the expression Σ-syntax A λ x → x <∙ a has type Type ℓ

**So `Σ[ x ∈ A ] (x <∙ a)` lands one universe too high.** That is why the
predecessor set cannot be formed today, and it is the whole obstruction.

**THE TREE ALREADY RELATES THE TWO ORDERS AT A STAGE, AND YOU SHOULD READ IT.**
`src/L/Cardinal.lagda.md:100` states `SWO._<∙_ w m n ≡ ⟨ ⟪ sucV (fst α) ⟫↪ m ∈ˢ
⟪ sucV (fst α) ⟫↪ n ⟩`. **It is a precedent that the re-basing is possible at a
price. It is not a cure and it does not transfer by analogy.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-513/Probe513.agda::preds"]

## SCOPE (write)
- agents/tasks/LJ-1-513/Probe513.agda
- agents/tasks/LJ-1-513/lj-1.513-report.md
- agents/tasks/LJ-1-513/review-of-preds.md
- agents/tasks/LJ-1-513/runs/

## PREMISES

1. `[LJ-1.497]` is a critic-upheld NO-GO and it REFUTED the adequacy. Basis: agents/tasks/LJ-1-497/Probe497.agda:435
2. Its report names the re-basing as the next brief and a coder task. Basis: agents/tasks/LJ-1-497/lj-1.497-report.md:3
3. The blocker is a universe level, measured. Basis: agents/tasks/LJ-1-497/lj-1.497-report.md:167
4. The diverging slot is the second component of the coded pair. Basis: agents/tasks/LJ-1-497/Probe497.agda:258
5. `range-clause` reads that same slot. Basis: agents/tasks/LJ-1-490/Probe490.agda:280
6. `b` is determined as the bounding ordinal, not free. Basis: agents/tasks/LJ-1-490/lj-1.490-report.md:271
7. `_∈ₛ_` is delivered. Basis: src/V/Model.lagda.md:48
8. The tree relates `_<∙_` to a membership at a stage. Basis: src/L/Cardinal.lagda.md:100
9. `[LJ-1.475]` said in prose that the formula does not read the order from `Q`. Basis: agents/tasks/LJ-1-475/lj-1.475-report.md:249
10. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
11. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**SEVEN DISPATCHES BUILT THE CODED ROUTE AND THE EIGHTH REFUTED ITS ADEQUACY.**
`[LJ-1.468]` the one-slot formula, `[LJ-1.471]` the order as a set,
`[LJ-1.475]` the rank formula, `[LJ-1.478]` the carve, `[LJ-1.486]` the bound,
`[LJ-1.490]` the fourth conjunct, `[LJ-1.497]` the refutation. **The formula is
sound; the rank behind it is the wrong rank.**

## WHAT IS MISSING

A predecessor set that forms.

## THE REASONING

**D-10, BEFORE ANY AGDA.** Say at `file:line` what universe `SWO`'s carrier and
its comparison each live in, and what universe `_∈ₛ_` gives. **Then say whether
re-basing actually lowers the level, or only moves the problem.** If it only
moves it, STOP AND SAY SO: that would mean the predecessor set cannot be formed
at any base and the replacement rank is unreachable, which retires the whole
coded route and is worth far more than a term.

**DO NOT BUILD `swo-rank′` AND DO NOT ATTEMPT THE ADEQUACY.** AD12 gives this
brief one obligation, and `[LJ-1.497]` measured that the adequacy needs a
SECOND missing hypothesis besides the rank: that `Q` reads as the ∈-order on
`a`, as a set of pairs. **That is not this task.**

**DO NOT WEAKEN THE PREDECESSOR SET TO MAKE THE LEVEL FIT.** A set of
predecessors that is not the predecessors pays nothing.

**DO NOT POSTULATE AND DO NOT RAISE THE CARRIER.** Lifting the carrier one
universe would change every consumer of `SWO` in the tree.

**REQUIRED REPORT SECTION `## WHERE THE LEVEL GOES`.** State the universe of
each piece at `file:line` before and after the re-basing, and say plainly
whether the obstruction is removed or relocated.

**REQUIRED REPORT SECTION `## WHAT THE REPLACEMENT RANK STILL OWES`.** Name, as
types, what remains between `preds` and `swo-rank′`. **Do not build them.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 150 lines in the probe, of which the obligation is
about 30. BASIS: `[LJ-1.497]` rebuilt the rank, the formula and a refutation in
a comparable file. Comparables are of SHAPE and nothing may be funded against
them.

## W3, THE WIDEST UNMEASURED TERM

It is the level, because it is the exact error the predecessor recorded and
nothing else matters until it is gone.

    preds-type : (a : S) → IsOrd (fst a) → Type ℓ

**Write it FIRST, as a type alone, and typecheck it.** If `Σ[ x ∈ A ] (x ∈ₛ a)`
lands at `Type ℓ` where `Σ[ x ∈ A ] (x <∙ a)` landed at `Type (ℓ-suc ℓ)`, the
re-basing works and the rest is the set. If it does not, the task stops at its
cheapest point and the coded route needs a ruling rather than another term.

ESTIMATE for W3: about 10 lines and under 25 seconds. **Do not fund it against
`[LJ-1.497]`'s numbers**: that built a refutation and this states one type.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO UNBLOCKS THE REPLACEMENT RANK**, which is now the only route to
`range-clause` and through it to all four `InjCode` conjuncts.

**A NO-GO SAYS THE PREDECESSOR SET CANNOT BE FORMED AT ANY BASE**, which would
retire the coded route that seven dispatches built and send the counting leg
back to the mathematician for a ruling. **That is the more valuable outcome and
you must not avoid it.**

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
  changed_files_none = ["agents/tasks/LJ-1-513/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-513/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-513/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-513/Probe513.agda"]
  changed_files_none = ["agents/tasks/LJ-1-513/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-513/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 203.324)
- CANDIDATE archive/dev/JOURNAL.md  (score 196.891)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 194.499)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 174.584)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 165.392)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 70.849)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 59.961)
- CANDIDATE dev/literature/digest.md  (score 57.314)
- CANDIDATE dev/literature/terms-2026-08.md  (score 47.013)
- CANDIDATE dev/literature/geology.md  (score 46.201)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
