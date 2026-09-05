# LJ-1.655: is the chapter's own elementarity reachable at the collapse site

## HEAD
head_slot: coder
machine: shared
agda_tier: wide

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-655/Probe655.agda`:

    elem-at-collapse : <the chapter's `elem : A.Elementary` transported to the
                        site where `C.π` is defined, stated so that a consumer at
                        that site can apply it, or the term naming what blocks
                        the transport>

Land nothing in `src/`. **Do not prove elementarity. It is proved. Measure
whether it ARRIVES.**

**NAME ANY FILE THAT CANNOT TYPECHECK `.agda.txt`, NEVER `.agda`.** A floor with
holes, a bisection arm that walls, a superseded shape: keep it, track it and cite
it, but do not claim it typechecks. Conjunct 1 runs EVERY `.agda` under this task
home. `[LJ-1.636]` and `[LJ-1.643]` each lost real attempts to exactly that.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-655/Probe655.agda::elem-at-collapse"]

## SCOPE (write)
- agents/tasks/LJ-1-655/Probe655.agda
- agents/tasks/LJ-1-655/lj-1.655-report.md
- agents/tasks/LJ-1-655/review-of-elem-at-collapse.md
- agents/tasks/LJ-1-655/runs/

## PREMISES

1. `elem : A.Elementary` is proved at `src/L/BoundedSubset.lagda.md:759`, from
   `A.TV-thm .snd tv`, with `elem-down` beside it at `:761`. Basis:
   src/L/BoundedSubset.lagda.md:759
2. `Elementary` is a satisfaction transfer, `(δ ⊨ᵐ φ) ≡ (map inL δ AbsL.⊨ᵐ (mapFo
   inL φ))`, and `TV-thm` proves it equivalent to Tarski-Vaught in both
   directions. Basis: src/L/Hull.lagda.md:174
3. **TWO NO-GOs NAMED ELEMENTARITY AS THE MISSING INGREDIENT AND NEITHER USED
   IT.** `[LJ-1.489]`'s verdict is "cannot agree without elementarity";
   `[LJ-1.477]` mentions it three times and spends it nowhere. Basis:
   agents/tasks/LJ-1-489/lj-1.489-report.md:12
4. `elem` sits at `:759` while `HullStage` opens at `:903` and `Condense` at
   `:916`, so the instance is ABOVE the collapse site in the same file. Whether
   it is IN SCOPE there is what this measures, and my line reading is a claim you
   should refute if it is wrong. Basis: src/L/BoundedSubset.lagda.md:903

## WHAT IS DELIVERED ALREADY

Premise 1's instance, green. No task has ever applied it at the collapse.

## THE REASONING

`[LJ-1.652]` and `[LJ-1.653]` both take elementarity as a hypothesis, which is
safe but leaves the campaign not knowing whether that hypothesis is free. This
costs one dispatch and answers it for both. **If it does not arrive, the two
NO-GOs stand for a structural reason and I want that reason named, not guessed.**

## W3, THE WIDEST UNMEASURED TERM

Whether `A.SM`, the carrier `Elementary` quantifies over, is the carrier the
collapse site uses. Estimate 50 to 120 lines, basis: this is a scope and carrier
measurement, not a construction, and `[LJ-1.643]`'s comparable census of one
predicate came to 126 lines (agents/tasks/LJ-1-643/lj-1.643-report.md:1).

## WHAT GO AND NO-GO EACH EARN

**GO** makes elementarity free at two consumers.
**NO-GO** names the carrier or scope gap between a proved elementarity and the
site that needs it, which is a fact about the chapter's layout that no report has.
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
  changed_files_any = ["agents/tasks/LJ-1-655/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-655/review-of-LJ-*-*.md"]

[[branch]]
id = "accept-failed"
priority = 14
action = "escalate"
head_slot = "coder_adversarial"

  [branch.when]
  exit_code = 1
  obligations_delta_max = -1
  changed_files_none = ["agents/tasks/LJ-1-655/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-655/Probe655.agda"]
  changed_files_none = ["agents/tasks/LJ-1-655/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-655/review-of-*.md"]

[[branch]]
# PARK, NOT ESCALATE. A heap wall is a resource fact and no critic can
# adjudicate it (MEASURED on LJ-1.534).
id = "heap-wall-park"
priority = 30
action = "park_and_split"

  [branch.when]
  heap_wall = true

[[branch]]
# CLOSES BACKLOG ITEM 30, MEASURED ON LJ-1.630 2026-08-25. A REAL failed
# landing carries a named Agda error and NEITHER companion file: the coder
# edits the target directly and leaves ad-hoc runs/*.out. Both rows above
# demand a companion (Probe or review-of), so that return matched NOTHING
# and the task parked with its evidence invisible. This row is the catch-all
# and it sits BELOW heap-wall-park, so a wall still parks.
id = "no-go-bare"
priority = 40
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
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
  Full entry: dev/LESSONS.md:2307
- **P-l. A statement may be ABOUT a concrete stage without dragging that stage's PRESENTATION into its type**
  **The law.** Being about a concrete position is not what costs. Naming a transparent construction in a statement's TYPE is. If the tower's stage values are `opaque` upstream, a theorem may quantify over, hypothesize about and conclude at `Sset ω` freely, because the stage is an ATOM to the elaborator and nothing unfolds. If instead the type mentions a transparent presentation, such as `⟪ sucV (...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2367
- **D-26. A well-founded key on a tower needs generation data, or it needs syntax**
  **Rule:** When a route must well-order a cumulative tower's stage, ask first what the stage's members CARRY. A stage built as the values of finitely many total operations carries its own generation data, so a well-founded key exists with NO syntax at all: the operation index, then the arguments, ordered recursively. A stage built as a definable power carries nothing: its members are sets, not c...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:1735
- **C-42. A refutation measures the site it names, and it never measures how far that site extends**
  **Rule:** A refutation is a measurement of ONE site. It says the statement there is false. **It says nothing about how many other sites carry the same false shape.** So when a refutation lands, the next action is not the cure. **It is the sweep: search the tree for the shape, and report the COUNT before you price the cure.** A cure funded against the named site is priced against a number nobody...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:3762

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev, archive/scripts, dev/ARCHIVE.md:
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 181.877)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 172.960)
- CANDIDATE archive/dev/JOURNAL.md  (score 148.302)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 140.124)
- CANDIDATE dev/ARCHIVE.md  (score 139.877)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 57.146)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 46.552)
- CANDIDATE dev/literature/digest.md  (score 37.029)
- CANDIDATE dev/literature/terms-2026-08.md  (score 30.774)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 29.985)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
