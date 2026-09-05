# LJ-1.462: levelIn again, with the formula the tree turned out to have

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-462/Probe462.agda`, at the type the consumer
states:

    levelIn : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ C.πX ⟩ → ⟨ Lset δ ∈ˢ C.πX ⟩

`C` is `Collapse M` and `M` is the definable hull at a limit stage, exactly as
`src/L/BoundedSubset.lagda.md:898-916` builds them. Rebuild that telescope; the
consumer states `levelIn` as a module parameter (`:917`) so it cannot be
projected out. Land nothing in `src/`.

**THIS OBLIGATION RAN ONCE AND ITS NO-GO WAS UPHELD ON A PREMISE THAT IS NOW
FALSE.** `[LJ-1.451]` stopped at D-10 step 3
(`agents/tasks/LJ-1-451/lj-1.451-report.md:66`, committed `9222c45`): the hull's
`Code` names no `Lset` and it judged the formula "not delivered". **`[LJ-1.458]`
then found it delivered.** `LsetGraphAt` is at `src/L/Coding/Sequence.lagda.md:349`
and its adequacy `Lset-only` at `src/L/Hierarchy.lagda.md:334-335`
(`agents/tasks/LJ-1-458/lj-1.458-report.md:71`, committed `4014d53`).

**READ BOTH REPORTS AND SAY WHICH PREMISE MOVED.** `[LJ-1.451]`'s NO-GO is a
measurement of the CONSTRUCTOR question and it still stands: `Code` has `base`
and `wit` only. What changed is the FORMULA question, and `wit` takes a formula.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-462/Probe462.agda::levelIn"]

## SCOPE (write)
- agents/tasks/LJ-1-462/Probe462.agda
- agents/tasks/LJ-1-462/lj-1.462-report.md
- agents/tasks/LJ-1-462/review-of-levelIn.md
- agents/tasks/LJ-1-462/runs/

## PREMISES

1. `levelIn` is one of the two unpaid condensation hypotheses. Basis: src/L/BoundedSubset.lagda.md:917
2. Its single consumer inside the step spends it as DATA. Basis: src/L/BoundedSubset.lagda.md:1011
3. `[LJ-1.451]` is a critic-upheld NO-GO at D-10 step 3. Basis: agents/tasks/LJ-1-451/lj-1.451-report.md:66
4. The hull's `Code` has two constructors and `wit` takes a formula with earlier codes as parameters. Basis: src/L/Hull.lagda.md:72
5. The hull is closed under definable existence at the stage. Basis: src/L/Hull.lagda.md:120
6. `[LJ-1.458]` is GO: the level formula IS delivered. Basis: agents/tasks/LJ-1-458/lj-1.458-report.md:71
7. It is `LsetGraphAt`. Basis: src/L/Coding/Sequence.lagda.md:349
8. Its adequacy is `Lset-only`, with an extra `IsOrd`. Basis: src/L/Hierarchy.lagda.md:334
9. The collapse image has an introduction rule from membership in the hull. Basis: src/V/Collapse.lagda.md:86
10. The collapse is injective on the hull and its image is transitive. Basis: src/V/Collapse.lagda.md:214
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THE FORMULA `[LJ-1.451]` CALLED MISSING IS IN THE TREE, AND A GREP PATTERN IS
WHY NOBODY SAW IT.** It is named `LsetGraphAt`, not `LsetAt`. `[LJ-1.458]` found
it and its adequacy in one dispatch. Everything else `levelIn` needs was already
delivered: the hull's closure (`src/L/Hull.lagda.md:120-123`), its members in
the stage (`:330-334`), and the collapse package (`src/V/Collapse.lagda.md:86`,
`:214`).

## WHAT IS MISSING

The term. `levelIn` still has no producer, and the bounded-subset lemma cannot
run without it.

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE SAME FOUR STEPS `[LJ-1.451]` WROTE.**
Work `levelIn` back across the collapse and write the four steps as types:

1. `δ ∈ C.πX` gives some `y ∈ M` with `C.π y ≡ δ`, by `C.πX-member`.
2. So the statement is about the hull: is `Lset y` in `M` whenever `y` is.
3. **That is the definability question, and it is now answerable**: `wit` takes a
   `Formula (⊥* {ℓ}) (suc k)` with earlier codes as parameters
   (`src/L/Hull.lagda.md:73-74`), and `LsetGraphAt` is a formula. **Say whether
   the two formula types meet, at `file:line`.** If they do not, name the
   repackaging and do NOT hide it in a `subst`.
4. Then the collapse must commute with `Lset`.

**STEP 3 IS THE ONE THAT MOVED AND STEP 4 IS THE ONE NOBODY HAS MEASURED.** If
step 3 closes and step 4 does not, say so: that is a different finding from
`[LJ-1.451]`'s and it is worth more.

**THE SHAPE.** Rebuild the telescope down to `C = Collapse M`, copying
`src/L/BoundedSubset.lagda.md:898-916` and nothing below it. Do W3 first. Do not
import a probe. **Do not pay `cover`**, and do not add it as a hypothesis: if
`levelIn` needs it, that is the finding.

**DO NOT POSTULATE AND DO NOT TRUNCATE THE CONCLUSION.** The consumer spends it
as data at `src/L/BoundedSubset.lagda.md:1020`.

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 160 lines in the probe, of which the obligation is
about 40. BASIS: `agents/tasks/LJ-1-434/Probe434.agda` is 128 lines and rebuilds
a comparable telescope out of the same chapter. Comparables are of SHAPE.

## W3, THE WIDEST UNMEASURED TERM

It is step 3, and it is now a MEETING of two formula types rather than an
absence.

    lset-code : (c : Code) → Σ[ d ∈ Code ] (fst (val d) ≡ Lset (fst (val c)))

**Write it FIRST, with the obligation omitted, and typecheck it ALONE**, feeding
`LsetGraphAt` to `wit`. `[LJ-1.458]` reports an extra `IsOrd` on the delivered
adequacy (`src/L/Hierarchy.lagda.md:334-335`); **the hull carries no ordinality,
so say where that hypothesis comes from at this site or report that it does
not.** That is the likeliest death point and it is cheap to reach.

ESTIMATE for W3: about 25 lines and under 15 seconds.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS ONE OF THE TWO HYPOTHESES THAT BLOCK THE BOUNDED-SUBSET LEMMA** and
leaves `cover` alone in that position.

**A NO-GO NAMES WHICH OF THE FOUR STEPS FAILS**, and after `[LJ-1.458]` it can no
longer be step 3's absence.

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
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-462/review-of-*.md"]
  # THE CRITIC'S OWN RETURN MUST NOT RE-MATCH. It writes
  # `review-of-LJ-1-462-<k>.md` beside the coder's leftover `review-of-*.md`.
  # Without this exclusion the escalation re-escalates itself and `attempt_max`
  # parks the task PERMANENTLY. MEASURED 2026-08-21 on LJ-1.448, 449, 450, 451.
  changed_files_none = ["agents/tasks/LJ-1-462/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-462/Probe462.agda"]
  changed_files_none = ["agents/tasks/LJ-1-462/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-462/review-of-*.md"]

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
