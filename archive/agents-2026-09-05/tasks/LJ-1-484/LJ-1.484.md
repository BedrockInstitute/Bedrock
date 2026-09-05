# LJ-1.484: the hypothesis nobody has ever taken as an obligation

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-484/Probe484.agda`:

    cover : (y : S) → ⟨ y ∈ˢ M ⟩
          → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ C.πX ⟩ × ⟨ C.π y ∈ˢ Lset γ ⟩) ∥₁

where `M` is the definable hull and `C = Collapse M`, exactly as
`src/L/BoundedSubset.lagda.md:903-916` builds them. Land nothing in `src/`.

**`cover` IS ONE OF THE TWO UNPAID CONDENSATION HYPOTHESES AND IT HAS NEVER BEEN
A TASK'S OBLIGATION.** `grep -l "obligations = .*cover" agents/tasks/*/[A-Z]*.md`
returns nothing. Sixty-nine report lines mention it and no dispatch has attempted
it. Its sibling `levelIn` has had six.

**A NO-GO WITH A DECOMPOSITION IS THE EXPECTED RETURN AND THE BRIEF ASKS FOR IT
BY NAME.** `[LJ-1.462]` did exactly this for `levelIn`: it inhabited one step,
stated the other three as types, and stopped. That return was upheld by a critic
and it produced four later dispatches. **Do the same here.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-484/Probe484.agda::cover"]

## SCOPE (write)
- agents/tasks/LJ-1-484/Probe484.agda
- agents/tasks/LJ-1-484/lj-1.484-report.md
- agents/tasks/LJ-1-484/review-of-cover.md
- agents/tasks/LJ-1-484/runs/

## PREMISES

1. `cover` is a module parameter of the condensation step and has no producer. Basis: src/L/BoundedSubset.lagda.md:918
2. It is spent twice, at an ARBITRARY member of the hull each time. Basis: src/L/BoundedSubset.lagda.md:967
3. The second spend is inside the inclusion of the collapse image in a level. Basis: src/L/BoundedSubset.lagda.md:1002
4. Its sibling `levelIn` sits beside it and has a four-step decomposition. Basis: src/L/BoundedSubset.lagda.md:917
5. `[LJ-1.462]` is the decomposition shape this brief asks for, and a critic upheld it. Basis: agents/tasks/LJ-1-462/lj-1.462-report.md:75
6. The hull is a term algebra closed under definable existence. Basis: src/L/Hull.lagda.md:120
7. Its members lie in the stage. Basis: src/L/Hull.lagda.md:330
8. `π-member` reads a collapse value back to a carrier member. Basis: src/V/Collapse.lagda.md:63
9. The hull is NOT transitive, measured. Basis: agents/tasks/LJ-1-160/lj-1.160-report.md:248
10. Devlin 5.2 identifies the collapse image with a level by Φ and Σ₁ elementarity, and does not commute the collapse with the stage operation. Basis: dev/literature/devlin-II5.md:95
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

The whole condensation step above `cover` and `levelIn`
(`src/L/BoundedSubset.lagda.md:916-1034`), including the separation of the
collapse image's ordinals and the identification of the image with a level. All
of it is CONDITIONAL on these two hypotheses.

## WHAT IS MISSING

Everything below the statement, and even the statement's shape has never been
worked out.

## THE REASONING

**W8 BINDS THIS TASK. READ THE INJECTED LITERATURE BLOCK BEFORE ANY AGDA.**
`cover` says every member of the hull collapses into some level indexed inside
the image. **That is the Σ₁ elementarity half of Devlin 5.2**
(`dev/literature/devlin-II5.md:95-106`). If the literature shows the shape needs
a hypothesis this tree does not meet, **STOP: a literature NO-GO is a full
return.**

**D-10, BEFORE ANY AGDA.** Decompose `cover` into named steps and write each as
a type. A first cut, which you must correct rather than accept:

1. `y ∈ M` gives a `Code` whose value is `y`, by the hull's own membership.
2. The code's formula bounds the stage at which `y` is definable.
3. `C.π y` lies in the level indexed by the collapse of that stage.
4. That index lies in `C.πX`.

**Name every step you actually need, at `file:line` for each delivered supplier,
and say which are unbuilt.** The list is the deliverable if the obligation does
not close.

**ONE MEASURED FACT THAT WILL BITE AND THE BRIEF NAMES IT UP FRONT: THE HULL IS
NOT TRANSITIVE** (`agents/tasks/LJ-1-160/lj-1.160-report.md:248-250`). A member
of a member of `M` need not be in `M`, so any step that walks down from `y` must
say why it stays inside.

**THE SHAPE.** Rebuild the telescope down to `C = Collapse M`, copying
`src/L/BoundedSubset.lagda.md:903-916`. Do not import a probe. **Do not take
`levelIn` as a hypothesis**: it is the sibling and assuming it makes the return
worthless.

**DO NOT POSTULATE. DO NOT WEAKEN THE CONCLUSION.** It is already truncated; do
not truncate the index or drop the `IsOrd`.

**REQUIRED REPORT SECTION `## THE DECOMPOSITION`.** Every step as a type, each
marked BUILT or UNBUILT, with a supplier at `file:line` for each built one.
**That section is what the next brief is written from**, exactly as
`[LJ-1.462]`'s was.

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 150 lines in the probe, of which the obligation or
its decomposition is about 50. BASIS: `agents/tasks/LJ-1-462/Probe462.agda` is
149 lines for the sibling's decomposition, one built step and three stated types.
**The band is wide because nothing has measured this statement**, and the report
must narrow it. Comparables are of SHAPE.

## W3, THE WIDEST UNMEASURED TERM

It is step 1, because everything else is written against whatever it produces.

    code-of : (y : S) → ⟨ y ∈ˢ M ⟩ → ∥ Σ[ c ∈ Code ] (fst (val c) ≡ y) ∥₁

**Write it FIRST, with the obligation omitted, and typecheck it ALONE.** The hull
is `∥ Σ[ c ∈ Code ] (fst (val c) ≡ x) ∥₁` by construction
(`src/L/Hull.lagda.md:330-334` reads it that way), so this should be immediate.
**If it is not, the hull's membership is not a code and the whole decomposition
above is wrong at its first step.**

ESTIMATE for W3: about 6 lines and under 15 seconds.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO WOULD PAY THE LAST UNTOUCHED HYPOTHESIS OF THE BOUNDED-SUBSET LEMMA**, and
with `levelIn` in flight the condensation step would be conditional on nothing.

**A NO-GO WITH A DECOMPOSITION IS THE LIKELY AND USEFUL RETURN.** It is the first
statement in this campaign of what `cover` actually costs, and every later brief
on the condensation front is written from it.

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
  changed_files_none = ["agents/tasks/LJ-1-484/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-484/review-of-*.md"]
  # THE CRITIC'S OWN RETURN MUST NOT RE-MATCH. It writes
  # `review-of-LJ-1-484-<k>.md` beside the coder's leftover `review-of-*.md`.
  # Without this exclusion the escalation re-escalates itself and `attempt_max`
  # parks the task PERMANENTLY. MEASURED 2026-08-21 on LJ-1.448, 449, 450, 451.
  changed_files_none = ["agents/tasks/LJ-1-484/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-484/Probe484.agda"]
  changed_files_none = ["agents/tasks/LJ-1-484/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-484/review-of-*.md"]

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
