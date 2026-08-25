# LJ-1.434: does a TRUNCATED square law reach the bounded-subset lemma's conclusion

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-434/Probe434.agda`:

    bounded-from-trunc :
        ∥ ((δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
             → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
                 ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v)) ∥₁
      → ⟨ x ∈ˢ Lset κ ⟩

Every OTHER parameter of `Devlin55.BoundedSubsetAt`
(`src/L/BoundedSubset.lagda.md:1385-1395`) and of its inner `module Co`
(`src/L/BoundedSubset.lagda.md:1554-1558`) is a module parameter of your probe,
copied unchanged. **Only `sq` moves, and it moves under one `∥ ∥₁`.**

**THE BODY IS ONE `PT.rec` AND THE CHAPTER'S OWN `theorem`.** The conclusion is
an hProp, so the chapter itself already spends `snd (x ∈ˢ Lset κ)` as the
`isProp` witness at `src/L/BoundedSubset.lagda.md:1606`. Use that same witness.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-434/Probe434.agda::bounded-from-trunc"]

## SCOPE (write)
- agents/tasks/LJ-1-434/Probe434.agda
- agents/tasks/LJ-1-434/lj-1.434-report.md
- agents/tasks/LJ-1-434/review-of-bounded-from-trunc.md

## PREMISES
- The bounded-subset lemma's conclusion is a membership, and a membership is an hProp. Basis: src/L/BoundedSubset.lagda.md:1621
- The chapter itself already spends that hProp witness, one line above the conclusion. Basis: src/L/BoundedSubset.lagda.md:1606
- The lemma takes the square law as DATA, over every member of the successor of its own ordinal. Basis: src/L/BoundedSubset.lagda.md:1388
- It spends that parameter directly at ONE ordinal, its own `α`. Basis: src/L/BoundedSubset.lagda.md:1410
- It spends it a second time through the stage-cardinal upper bound, again at that one ordinal. Basis: src/L/BoundedSubset.lagda.md:1513
- The whole family enters through one module application. Basis: src/L/BoundedSubset.lagda.md:1397
- The enclosing module takes no parameters, so the probe can open it directly. Basis: src/L/BoundedSubset.lagda.md:1362
- The inner module that carries the conclusion takes two more hypotheses. Basis: src/L/BoundedSubset.lagda.md:1554
- `[LJ-1.407]` delivers the square law TRUNCATED at every band ordinal, with no residue. Basis: agents/tasks/LJ-1-407/lj-1.407-report.md:18
- Its delivered shape is the consumer's own parameter with one truncation added and nothing else changed. Basis: agents/tasks/LJ-1-407/Probe407.agda:273
- `[LJ-1.408]` REFUTED one way of moving the pairing under a truncation, inside the class predicate. Basis: agents/tasks/LJ-1-408/Probe408.agda:95
- That refutation is about a pairing read TWICE under two different truncations, which is not what one outer `PT.rec` does. Basis: agents/tasks/LJ-1-408/lj-1.408-report.md:26
- The architecture is a CANDIDATE and only a measurement settles it. Basis: dev/pod/screen.toml:10

## WHAT IS DELIVERED ALREADY

**THE TRUNCATED SQUARE LAW.** `[LJ-1.407]` returned GO with no residue and its
`plugs-in` (`agents/tasks/LJ-1-407/Probe407.agda:279-280`) has the consumer's own
shape with one `∥ ∥₁` added.

**THE UNTRUNCATED CONSUMER.** `Devlin55.BoundedSubsetAt` is green in the tree
today and its conclusion is `theorem : ⟨ x ∈ˢ Lset κ ⟩`
(`src/L/BoundedSubset.lagda.md:1621`).

## WHAT IS MISSING

**NOBODY HAS ASKED WHETHER THE CONSUMER'S CONCLUSION IS A PROPOSITION.** The
whole campaign since `[LJ-1.391]` has tried to turn `∥ sq δ ∥₁` into `sq δ`.
`[LJ-1.391]` measured that the missing principle is a `2-Constant` endomap
(`agents/tasks/LJ-1-391/lj-1.391-report.md:38`) and returned NO-GO.

**THE OTHER DIRECTION WAS NEVER TRIED: leave the square law truncated and ask
what the CONSUMER can still deliver.** `⟨ x ∈ˢ Lset κ ⟩` is an hProp. A single
`PT.rec` at the top of the module is then legal, and every use of the pairing
inside the module happens under ONE opened witness, so the two readings
`[LJ-1.408]` refuted never arise.

**WHAT THIS DOES NOT CLAIM.** The hypothesis here is a TRUNCATED FAMILY,
`∥ (δ : S) → ... → sq δ ∥₁`, and `[LJ-1.407]` delivers a FAMILY OF TRUNCATIONS,
`(δ : S) → ... → ∥ sq δ ∥₁`. **Those are different types and this task does not
join them.** Naming the distance between them, as a type, is half this task's
value.

## THE REASONING

**D-10, BEFORE ANY AGDA.** Write in the report, at `file:line`, why
`⟨ x ∈ˢ Lset κ ⟩` is an hProp and where the chapter itself uses that fact. If
you cannot cite the chapter's own use of it, do not write Agda.

**STEP ONE, W3, THE INSTANTIATION.** Form the module telescope and the two
module applications with `sq` as a PLAIN data parameter, with the obligation
omitted, and typecheck it alone. This step measures whether the probe can carry
this chapter at all at the caliber the program set on your pane.

**STEP TWO, THE OBLIGATION.** Move `sq` under `∥ ∥₁`, and close with
`PT.rec (snd (x ∈ˢ Lset κ)) (λ sqf → ...) h`, where the body is the instantiation
of step one at `sqf`.

**A REQUIRED REPORT SECTION, `## WHERE THE CHAPTER SPENDS sq`.** Run
`grep -n "sq " src/L/BoundedSubset.lagda.md src/L/StageCardinal.lagda.md`, and
report the COUNT and every site at `file:line`. **For each site say at WHICH
ordinal the parameter is read.** Say plainly whether any site reads it at more
than one ordinal, and if one does, name it. That count is the input to the next
brief and it is not optional.

**W2 (DD4).** Change nothing in the telescope except `sq`. Do not specialise
`κ`, `α`, `x` or `lam`. Do not add a hypothesis. A probe that fixes an ordinal
measures a different statement.

**DO NOT EDIT `src/`.** The chapter stays as it is. This task measures it.

ESTIMATE for the Agda: about 45 code lines. BASIS:
`src/L/BoundedSubset.lagda.md:1385-1402` is the same telescope with two module
applications in 18 lines; this probe restates that telescope, adds the two
hypotheses of `module Co` and one `PT.rec`. **Comparables of SHAPE and never of
size, and nothing may be funded against them.**

## WHAT GO AND NO-GO EACH EARN

**A GO MOVES THE WHOLE CAMPAIGN'S RESIDUE TO ONE NAMED TYPE.** It says the
bounded-subset lemma needs no pairing as data at all, only a truncated family,
and the only thing left between `[LJ-1.407]`'s delivery and the trophy is the
distance between a family of truncations and a truncated family. Write that
distance in the report as ONE type, at `file:line`. **Do not claim that distance
is small and do not claim it is closed.**

**A NO-GO IS WORTH AS MUCH.** It names the first term inside the module that
needs the pairing as data OUTSIDE a proposition, at `file:line`, and that term is
then the true consumer the campaign has been serving without knowing it. Either
answer is a measurement `[LJ-2.5]` can spend.

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
  changed_files_any = ["agents/tasks/LJ-1-434/Probe434.agda"]
  changed_files_none = ["agents/tasks/LJ-1-434/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-434/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 147.247)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 114.844)
- CANDIDATE archive/dev/JOURNAL.md  (score 104.140)
- CANDIDATE dev/ARCHIVE.md  (score 103.864)
- CANDIDATE archive/dev/DD-archived.md  (score 85.896)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 65.756)
- CANDIDATE dev/literature/devlin-II5.md  (score 56.870)
- CANDIDATE dev/literature/digest.md  (score 38.552)
- CANDIDATE dev/literature/terms-2026-08.md  (score 35.242)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 29.110)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
