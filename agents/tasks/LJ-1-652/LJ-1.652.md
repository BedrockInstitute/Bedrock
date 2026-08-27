# LJ-1.652: pi commutes with the definable powerset, from elementarity

## HEAD
head_slot: coder
machine: shared
agda_tier: wide

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-652/Probe652.agda`:

    picommute-D-from-elem :
        <`Elementary` at the site as a HYPOTHESIS>
      → <`[LJ-1.651]`'s `lset-formula`, and its `𝒟ₒ` counterpart, as HYPOTHESES>
      → (y : S) → ⟨ y ∈ˢ M ⟩ → C.π (𝒟ₒ y) ≡ 𝒟ₒ (C.π y)

Land nothing in `src/`. **Build neither hypothesis.**

**NAME ANY FILE THAT CANNOT TYPECHECK `.agda.txt`, NEVER `.agda`.** A floor with
holes, a bisection arm that walls, a superseded shape: keep it, track it and cite
it, but do not claim it typechecks. Conjunct 1 runs EVERY `.agda` under this task
home. `[LJ-1.636]` and `[LJ-1.643]` each lost real attempts to exactly that.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-652/Probe652.agda::picommute-D-from-elem"]

## SCOPE (write)
- agents/tasks/LJ-1-652/Probe652.agda
- agents/tasks/LJ-1-652/lj-1.652-report.md
- agents/tasks/LJ-1-652/review-of-picommute-D.md
- agents/tasks/LJ-1-652/runs/

## PREMISES

1. `[LJ-1.489]` closed NO-GO on exactly this statement and its verdict names the
   missing ingredient in its own words: "The two sides cannot agree without
   elementarity". Basis: agents/tasks/LJ-1-489/lj-1.489-report.md:12
2. **THE TREE HAS ELEMENTARITY AND `[LJ-1.489]` DID NOT USE IT.** `Elementary` is
   `src/L/Hull.lagda.md:174-175` and it is exactly a satisfaction transfer:
   `(δ ⊨ᵐ φ) ≡ (map inL δ AbsL.⊨ᵐ (mapFo inL φ))`. Basis: src/L/Hull.lagda.md:174
3. **IT IS ALSO INHABITED, IN THIS VERY CHAPTER.** `elem : A.Elementary` at
   `src/L/BoundedSubset.lagda.md:759`, built from `A.TV-thm .snd tv`, with
   `elem-down` beside it. Basis: src/L/BoundedSubset.lagda.md:759
4. `[LJ-1.648]` measured that `DefFwd` and `DefBwd` are ONE statement and that
   statement is `[LJ-1.489]`'s, so closing this closes two of clause (iii)'s three
   gaps. Basis: agents/tasks/LJ-1-648/lj-1.648-report.md:251

## WHAT IS DELIVERED ALREADY

Premises 2 and 3, both green in `src/`. `piCommuteD` has supply 0.

## THE REASONING

A NO-GO that names its missing ingredient, an ingredient that is proved twenty
lines from the site, and no dispatch between them. That is the cheapest kind of
task this campaign has and it has been sitting for 160 dispatches.

## W3, THE WIDEST UNMEASURED TERM

Whether `𝒟ₒ`'s defining condition is a `Formula A.SM n`, which is what
`Elementary` transfers. Estimate 80 to 170 lines, basis: `[LJ-1.489]`'s own probe
reached the join and stated the stop.

## WHAT GO AND NO-GO EACH EARN

**GO** closes two of clause (iii)'s three gaps. **NO-GO** earns why elementarity
does NOT reach `𝒟ₒ`, which is the sharpest thing anyone could say about the
collapse and which `[LJ-1.489]` could only say in prose.
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
  changed_files_any = ["agents/tasks/LJ-1-652/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-652/review-of-LJ-*-*.md"]

[[branch]]
id = "accept-failed"
priority = 14
action = "escalate"
head_slot = "coder_adversarial"

  [branch.when]
  exit_code = 1
  obligations_delta_max = -1
  changed_files_none = ["agents/tasks/LJ-1-652/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-652/Probe652.agda"]
  changed_files_none = ["agents/tasks/LJ-1-652/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-652/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 200.836)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 183.162)
- CANDIDATE archive/dev/JOURNAL.md  (score 163.013)
- CANDIDATE dev/ARCHIVE.md  (score 155.298)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 143.757)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 57.601)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 49.631)
- CANDIDATE dev/literature/digest.md  (score 41.515)
- CANDIDATE dev/literature/geology.md  (score 30.780)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 28.732)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
