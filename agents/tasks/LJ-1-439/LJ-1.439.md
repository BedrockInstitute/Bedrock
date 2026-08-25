# LJ-1.439: a limit ordinal above any ordinal, with successor closure

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-439/Probe439.agda`, at a GENERIC ordinal:

    limit-above :
        (u : S) → IsOrd u
      → Σ[ lam ∈ S ] ( IsOrd lam
                     × ⟨ u ∈ˢ lam ⟩
                     × ((d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩) )

`S` is `hPropStructure 𝒮ᵥ`'s `S`, the same one
`src/L/Ordinal/StageArith.lagda.md:27` and `src/L/BoundedSubset.lagda.md:56`
open. The witness is `+ω u` (`src/L/Ordinal/StageArith.lagda.md:41-42`) and
nothing else. Do not build a second ω-block.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-439/Probe439.agda::limit-above"]

## SCOPE (write)
- agents/tasks/LJ-1-439/Probe439.agda
- agents/tasks/LJ-1-439/lj-1.439-report.md
- agents/tasks/LJ-1-439/review-of-limit-above.md

## PREMISES
- The bounded-subset lemma takes a limit stage as FIVE separate hypotheses. Basis: src/L/BoundedSubset.lagda.md:1393
- One of the five is successor closure of that stage. Basis: src/L/BoundedSubset.lagda.md:1394
- The hull module reads successor closure directly, so it is not decoration. Basis: src/L/BoundedSubset.lagda.md:904
- The ω-block above an ordinal is defined and SEALED. Basis: src/L/Ordinal/StageArith.lagda.md:41
- The seal exports an introduction and no elimination. Basis: src/L/Ordinal/StageArith.lagda.md:48
- The block is an ordinal when its base is. Basis: src/L/Ordinal/StageArith.lagda.md:76
- The base is a member of its own block. Basis: src/L/Ordinal/StageArith.lagda.md:62
- Every finite iterate is a member of the block. Basis: src/L/Ordinal/StageArith.lagda.md:68
- Each finite iterate is an ordinal. Basis: src/L/Ordinal/StageArith.lagda.md:72
- Trichotomy on two ordinals is delivered. Basis: src/L/Ordinal/Linear.lagda.md:136
- The successor of an ordinal is an ordinal. Basis: src/L/Ordinal.lagda.md:96
- The architecture is a CANDIDATE and only a measurement settles it. Basis: dev/pod/screen.toml:10

## WHAT IS DELIVERED ALREADY

**THE BLOCK EXISTS AND IT IS AN ORDINAL.** `+ω`
(`src/L/Ordinal/StageArith.lagda.md:41-42`) is the union of the finite
successor iterates of its base. `+ω-ord` (`:76-78`) proves it is an ordinal,
`+ω-mem` (`:62-63`) puts the base inside it, `+ω-sup` (`:65-66`) puts every
member of the base inside it, and `+ω-iter` (`:68-69`) puts every finite
iterate inside it.

**TWO OF THE THREE CONJUNCTS ARE ONE LINE EACH.** `IsOrd lam` is `+ω-ord u ou`.
`⟨ u ∈ˢ lam ⟩` is `+ω-mem u`.

## WHAT IS MISSING

**THE THIRD CONJUNCT, AND THE BLOCK EXPORTS NO ELIMINATION.** The `opaque`
block at `src/L/Ordinal/StageArith.lagda.md:44-78` carries
`unfolding +ω` and exports SIX names: `+ω-in`, `+ω-mem`, `+ω-sup`,
`+ω-iter`, `sucIter-ord` and `+ω-ord`. **Four of them put a set INTO the
block, two are ordinality facts, and NOT ONE takes a member out of it.** So a proof written outside that file cannot
turn `⟨ d ∈ˢ +ω u ⟩` into `Σ[ n ∈ ℕ ] ⟨ d ∈ˢ sucIter (suc n) u ⟩`, because
`+ω u` is a stuck atom there and `union-ax` cannot see its union.

That is the whole question of this task, and nobody has asked it. Five
hypotheses of the bounded-subset lemma wait on the answer.

## THE REASONING

**D-10, BEFORE ANY AGDA.** Write in the report, at `file:line`, EVERY name the
`opaque` block at `src/L/Ordinal/StageArith.lagda.md:44-78` exports, and say
for each whether it is an introduction, an elimination, or neither. **If the block
exports no elimination, say so at that point**, then go on and try the route
below anyway. A conclusion reached before the attempt is an opinion; the
attempt is the measurement.

**THE SHAPE, AND THERE ARE TWO ROUTES. TRY THE SECOND ONLY IF THE FIRST FAILS.**

*Route 1, through the exported five.* Take `d : S` with `⟨ d ∈ˢ +ω u ⟩`. Both
`sucV d` and `+ω u` are ordinals, so trichotomy (`src/L/Ordinal/Linear.lagda.md:136`)
gives `⟨ sucV d ∈ˢ +ω u ⟩`, or `sucV d ≡ +ω u`, or `⟨ +ω u ∈ˢ sucV d ⟩`. The
first case is the goal. In the other two, `+ω u` is a subset of `sucV d`, so
`+ω-iter n u` puts every finite iterate inside `sucV d`. Ask whether that,
with `⟨ d ∈ˢ +ω u ⟩`, is a contradiction. **Say in the report exactly where
this route stops if it stops**, because that is the measurement.

*Route 2, one exported line.* If route 1 stops, do NOT edit `src/`. State in
`agents/tasks/LJ-1-439/review-of-limit-above.md` the ONE declaration that the
`unfolding +ω` block would have to export to close route 1, as a TYPE, for
example an elimination of the block into an indexed iterate. Name the file and
the line where it would go. That review file is this task's deliverable when
the obligation does not close, and the NO-GO branch sends it to a critic.

**W2 (DD4).** Generic in `u`. Name no stage, no numeral, no cardinal and no
band. The consumer's instantiation is a later task's business and not this
one's.

**W3, THE WIDEST UNMEASURED TERM.**

    plus-omega-suc :
        (u : S) → IsOrd u
      → (d : S) → ⟨ d ∈ˢ +ω u ⟩ → ⟨ sucV d ∈ˢ +ω u ⟩

**THE PROBE.** State and typecheck `plus-omega-suc` ALONE, with `limit-above`
OMITTED. It IS the third conjunct, and the other two are one line each, so this
term carries the whole risk of the task. Report wall seconds and peak RSS at
the caliber the program set on your pane, one Agda process, three forced
rechecks, and the median. Quote the elaborator at `file:line` if it refuses. A
heap event is a WALL event: report it and stop.

**DO NOT WRITE IN `src/`.** This task adds one probe and one report. If the
cure is an export, the review file names it and a later brief orders it.

**C-42.** In a section `## WHAT THIS DOES NOT MEASURE`, say plainly that this
task delivers a limit ordinal above a given ordinal and measures NOTHING about
the other hypotheses of the bounded-subset lemma. Name at `file:line` the two
that stay owed after a GO: the membership of the subject in the stage
(`src/L/BoundedSubset.lagda.md:1395`) and the absorption arrow
(`src/L/BoundedSubset.lagda.md:1392`).

ESTIMATE for the Agda: about 45 code lines. BASIS: a delivered comparable of
SHAPE, `src/L/Ordinal/StageArith.lagda.md:61-78`, which is the four block
lemmas and the two ordinality lemmas in 18 lines, plus one trichotomy split of
the size of `agents/tasks/LJ-1-421/Probe421.agda:182-198`. **Comparables of
SHAPE and never of size, and nothing may be funded against them.**

## WHAT GO AND NO-GO EACH EARN

**A GO RETIRES THREE OF THE FIVE LIMIT-STAGE HYPOTHESES** of the bounded-subset
lemma, at a generic ordinal, and hands the next brief a single Sigma to open.
Say in the report, in one sentence with a `file:line`, the exact type you
inhabited.

**A NO-GO IS WORTH AS MUCH AND IT IS CHEAPER TO ACT ON.** It says the ω-block
is sealed with no way out, names the one declaration that would open it, and
turns a mathematical question into a one-line export that a later brief orders.
Write that declaration as a TYPE, not as a description.

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
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-439/Probe439.agda"]
  changed_files_none = ["agents/tasks/LJ-1-439/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-439/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 171.662)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 145.552)
- CANDIDATE archive/dev/JOURNAL.md  (score 117.422)
- CANDIDATE dev/ARCHIVE.md  (score 114.507)
- CANDIDATE archive/dev/TASKS-archived.md  (score 93.884)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 43.039)
- CANDIDATE dev/literature/devlin-II5.md  (score 42.942)
- CANDIDATE dev/literature/digest.md  (score 36.358)
- CANDIDATE dev/literature/fine-structure.md  (score 32.974)
- CANDIDATE dev/literature/devlin-errata.md  (score 31.546)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
