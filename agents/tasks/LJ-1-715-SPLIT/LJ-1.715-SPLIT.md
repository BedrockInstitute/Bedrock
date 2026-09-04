# LJ-1.715-SPLIT: transcribe the worktree landing, then floor Everything

## HEAD
head_slot: coder
machine: shared
agda_tier: heavy

## THE OBLIGATION

Add the same two names to `src/L/Ordinal.lagda.md` that sit in the 715 worktree, and mirror `bound2-in-limit` in `agents/tasks/LJ-1-715-SPLIT/Probe715Split.agda`.

Transcribe. Do not re-invent. The bodies are:

    IsLimit : S → Type (ℓ-suc ℓ)
    bound2-in-limit :
      (α : S) (Lim : IsLimit α)
      (σ₁ σ₂ : S) (o₁ : IsOrd σ₁) (o₂ : IsOrd σ₂)
      (h₁ : ⟨ σ₁ ∈ˢ α ⟩) (h₂ : ⟨ σ₂ ∈ˢ α ⟩)
      → ⟨ fst (bound2 σ₁ σ₂ o₁ o₂) ∈ˢ α ⟩

Source of the bodies: `.pod-state/worktrees/LJ-1-715/src/L/Ordinal.lagda.md:205-229`.

**ADD. DO NOT RESTRUCTURE `bound2`.** No extra `.agda` diagnostic. Name any file that cannot typecheck `.agda.txt`.

**FLOOR `src/Everything.lagda.md` WITH ONE AGDA PROCESS BEFORE YOU CLAIM GO.** `[LJ-1.715]` never ran it. Conjunct 1 did, at concurrency 2, and that is the park.

**BEFORE YOU RETURN, RUN `.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-715-SPLIT` AND PASTE ITS OUTPUT.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-715-SPLIT/Probe715Split.agda::bound2-in-limit"]

## SCOPE (write)
- src/L/Ordinal.lagda.md
- agents/tasks/LJ-1-715-SPLIT/Probe715Split.agda
- agents/tasks/LJ-1-715-SPLIT/lj-1.715-SPLIT-report.md
- agents/tasks/LJ-1-715-SPLIT/review-of-bound2-in-limit.md
- agents/tasks/LJ-1-715-SPLIT/runs/
- Never `src/Everything.lagda.md`. Floor it. Do not edit it.

## PREMISES

1. **THE LEMMA IS NOT IN THE LIVE TREE.** I opened `src/L/Ordinal.lagda.md:221-229`. That span is `mem-ord`. `bound2-in-limit` has supply 0. Basis: src/L/Ordinal.lagda.md:221
2. **IT IS IN THE 715 WORKTREE, AND THE PROBE THERE CLOSES.** `IsLimit` at 205, `bound2-in-limit` at 221-229. Probe rc 0 at 0.82 s. Isolated master rc 0 at 0.80 s. Basis: .pod-state/worktrees/LJ-1-715/src/L/Ordinal.lagda.md:221
3. **THE PARK IS EVERYTHING, NOT THE TERM.** Conjunct 1 failed on Everything, rc 251, 206.66 s, heap wall, concurrency 2. Obligations delta is already -1. Basis: dev/pod/transitions/2026-08.jsonl:4925
4. **THE REPORT'S "HEAP WALL NONE" IS THE ISOLATED MASTER.** It is not the accept arm. Basis: agents/tasks/LJ-1-715/lj-1.715-report.md:149
5. **`bound2` STAYS UNTOUCHED.** Basis: src/L/Ordinal.lagda.md:185
6. **THE HOST HAS FORTY DEPENDENTS.** That is why this is `heavy` and why Everything is the risk. Basis: src/L/Ordinal.lagda.md:185

## MEASURED TODAY

- dependents: L.Ordinal => 40
- supply: bound2-in-limit => 0

## WHAT IS DELIVERED ALREADY

The proof, in the worktree, 33 lines, hole-and-retry at the union-clause family. Live `src/` has none of it. A parked close does not commit. Named reading is this brief, the accept arm via the transition line, the 715 report HEAD and section 2, and the worktree fence at Ordinal.lagda.md:199-229. About 14k tokens at 4 B per token.

## THE REASONING

This is not a new lemma and it is not a shelve. The term closed. The close did not. The neighbour is a second invention of `bound2-in-limit`; the obligation is to copy the worktree bodies and to run the check `[LJ-1.715]` skipped.

## W3, THE WIDEST UNMEASURED TERM

Whether Everything at heavy `-M4g` and one Agda process accepts those 33 lines. Estimate 33 lines transcribed plus one Everything floor. Basis: agents/tasks/LJ-1-715/runs/accept-1.out:16

## WHAT GO AND NO-GO EACH EARN

**GO** lands the lemma in live `src/` and unblocks `[LJ-1.711]`. **NO-GO** that Everything still walls, after a transcription with no extra `.agda` and one process, is a finding about `L.Ordinal`'s 40 dependents at this cap, not about the term. Do not invent a third landing.

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
  changed_files_any = ["agents/tasks/LJ-1-715-SPLIT/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-715-SPLIT/review-of-LJ-*-*.md"]

[[branch]]
id = "lint-back-to-author"
priority = 13
action = "escalate"
head_slot = "coder"

  [branch.when]
  exit_code = 1
  error_class_in = ["lint"]

[[branch]]
id = "accept-failed"
priority = 14
action = "escalate"
head_slot = "coder_adversarial"

  [branch.when]
  exit_code = 1
  obligations_delta_max = -1
  changed_files_none = ["agents/tasks/LJ-1-715-SPLIT/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-715-SPLIT/Probe715Split.agda"]
  changed_files_none = ["agents/tasks/LJ-1-715-SPLIT/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-715-SPLIT/review-of-*.md"]

[[branch]]
id = "heap-wall-park"
priority = 30
action = "park_and_split"

  [branch.when]
  heap_wall = true

[[branch]]
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

MANDATORY for kind `build` (writes a master under src/. The heaviest bundle, because a build is where seconds and lines are actually spent.):

- **P-h. Definability walks are module-parameterized, never function-parameterized**
  **Rule:** A definability walk (the `defSet≡` extensionality of an InL-idiom constructibility lemma) takes its set arguments as parameters of a module, not of a function, and those parameters stay ABSTRACT through the walk: the formulas and the readers never mention a concrete `sett` body (`slice`, `satSet`, a stage over them); the instantiation at real sets happens only at the lemma-assembly le...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:200
- **P-k. A read lemma is stated where its consumers use it, not where its proof ends**
  **The law.** When a lemma exists so that consumers can rewrite with it, its stated right-hand side must be **the form the consumers actually need**, not the form the proof happened to reach. If it stops one layer early, every consumer re-normalizes the missing layer, and the same conversion is paid once per consumer instead of once in total. **Absorb the last layer into the lemma and seal it**,...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2463
- **P-l. A statement may be ABOUT a concrete stage without dragging that stage's PRESENTATION into its type**
  **The law.** Being about a concrete position is not what costs. Naming a transparent construction in a statement's TYPE is. If the tower's stage values are `opaque` upstream, a theorem may quantify over, hypothesize about and conclude at `Sset ω` freely, because the stage is an ATOM to the elaborator and nothing unfolds. If instead the type mentions a transparent presentation, such as `⟪ sucV (...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2367
- **P-m. The check-cost rate is a content-class certificate, and instantiation is the expensive class**
  **Rule:** Seconds per line identify a block's CONTENT CLASS before any profile is run, and line count alone predicts nothing. **Parameterized content**, whose definitions check at bound variables under a module telescope, checks near **0.01 s per line**. **Instantiation content**, which states object-language formulas at a concrete carrier, proves decodes that walk the satisfaction relation, an...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2522
- **P-n. Satisfaction content at a concrete carrier is a payable floor, not a defect**
  **Rule:** When a proof states object-language formulas at a CONCRETE carrier and proves their two-way decodes, the elaborator normalizes the carrier's presentation at every such definition, and **named branches with written types do not remove that cost**. I-5's cure applies to a missing type, not to this; if every hot branch already carries a written type, the remaining cost is the machinery a...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2545
- **R-35. Union representations are meta-poisoned; state memberships at small indices**
  **Rule:** Index or path extraction from the representation of a union of an open term (`⟪ ⋃ x ⟫`-level fiber extraction, `separation-ax` over a union) leaves unsolved metas or churns the presentation machinery; state the membership at the SMALL INDEX instead (an existential over `⟪ y ⟫` with the inclusion applied), and keep constructions at the stuck-member level.
  Full entry: dev/LESSONS.md:808
- **R-38. A consumer's alias of a transparent imported operation is a birth site**
  **Rule:** P-c extends one layer up: when a consumer names a composite of a TRANSPARENT imported operation (a derived op whose body reaches an imported sett/union tower), the consumer's alias is itself a birth site and must be sealed opaque with its spec inside, even though the imported operation was delivered transparent. Transparent-by-delivery kit operations (the Images F10 and the left/right...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:855
- **R-40. A deep successor-chain membership witness normalizes super-linearly; climb by small closures**
  **Rule:** An ordinal-membership premise stated at a deep iterated successor (`+ω-iter n`, a `sucV`-chain) forces the conversion checker to normalize the whole chain against the level's union representation, and the cost is super-linear in the depth. State the witness at a SHALLOW index and climb by the limit-ordinal successor closure (`limit-succ-mem`, `L.Rud.Hierarchy:455`), one step per line....
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:955
- **I-5. Inner-world truncation branches carry written types**
  **Rule:** In the inner world, every `PT.rec`/`PT.map` branch gets a named `where` function with a WRITTEN type; a branch whose type is left to inference re-elaborates the inner satisfaction machinery per constraint and reads as a conversion wall. The trap's target class is wider than the retiring stack recorded: it fires on equations between iterated Kuratowski pairs, not only on disjunctions o...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:1255
- **C-12. Agda runs under a hard heap cap; parallel writers under a quota**
  **Rule:** Every agda invocation runs under a GHC heap cap (`GHCRTS=-M<n>g`) so a runaway typecheck dies with a clean "Heap exhausted" exit instead of OOM-killing the machine; the orchestrator's audits run at `-M16g` and `make` exports a default. **OWNER-RULED 2026-08-23, SECOND RULING THE SAME DAY: WIDE and HEAVY split apart again, WIDE smaller and concurrent.** The first ruling that date flatt...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2135
- **D-10. Price the truth of a recorded residue before pricing its proof**
  **Rule:** A residue recorded under the wall protocol names a TARGET, and a target can be false; before dispatching a discharge batch, spend the five minutes checking the target's truth at the intended generality (a Tarskian or cardinality obstruction is the usual killer), and record the corrected target beside the original.
  Full entry: dev/LESSONS.md:1375
- **C-22. A dispatched agent writes its deliverable incrementally, never at the end**
  **Rule:** When an agent's deliverable is a file, the brief must require it WRITTEN EARLY as a skeleton and filled incrementally, saving after each answer lands. An agent that researches for its whole budget and leaves the writing to the end returns nothing when the budget runs out, and its research dies with it. A partial dossier is a real deliverable; an unwritten perfect one is not.
  Full entry: dev/LESSONS.md:2307

## STANDING (program-generated, do not edit)

The records every dispatch may need. They are NOT candidates, they are not the answer to any search, and no return has to account for them. The search below spends its whole budget on what is not here.

- STANDING archive/dev/JOURNAL-archived.md
- STANDING dev/literature/truncation-and-selection.md
- STANDING dev/literature/devlin-II5.md
- STANDING dev/literature/digest.md
- STANDING archive/dev/LJ-dispatch-index.md
- STANDING archive/dev/JOURNAL.md
- STANDING dev/literature/terms-2026-08.md
- STANDING dev/ARCHIVE.md
- STANDING dev/literature/geology.md
- STANDING archive/dev/DECISIONS-archived.md

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev, archive/scripts, dev/ARCHIVE.md:
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 168.640)
- CANDIDATE archive/dev/DD-archived.md  (score 162.435)
- CANDIDATE archive/dev/PLAN-archived.md  (score 144.054)
- CANDIDATE archive/dev/TASKS-archived.md  (score 100.002)
- CANDIDATE archive/dev/STATUS-archived.md  (score 97.342)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 27.120)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 23.555)
- CANDIDATE dev/literature/primary-sources.md  (score 22.490)
- CANDIDATE dev/literature/devlin-errata.md  (score 21.587)
- CANDIDATE dev/literature/BIBLIOGRAPHY.md  (score 19.110)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
