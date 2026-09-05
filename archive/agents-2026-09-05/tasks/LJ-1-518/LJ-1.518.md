# LJ-1.518: the hypothesis that links the formula's order to the rank's

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-518/Probe518.agda`:

    ord-reads-Q : (Q a : S) → IsOrd (fst a) → Type ℓ

**the hypothesis that `Q` is the ∈-order on `a` as a set of pairs, STATED and
INHABITED at the ∈-order itself.** Land nothing in `src/`.

**THIS IS THE LAST NAMED GAP ON THE CODING LEG.** `[LJ-1.497]` refuted the old
adequacy and wrote its replacement, with one hole in it
(`agents/tasks/LJ-1-497/lj-1.497-report.md:209-215`):

    rankFo-adequate′ :
        (Q a : S) (oa : IsOrd (fst a)) (z : S)
      → (Q reads as the ∈-order on a)          -- MISSING, see below
      → ⟨ (z ∷ []) ⊨ rankFo Q a ⟩
      → Σ[ m ∈ S ] Σ[ mx ∈ ⟨ fst m ∈ fst a ⟩ ]
          (fst z ≡ pr (fst m) (fst (rank-at′ a oa m mx)))

**`[LJ-1.497]` MEASURED WHY IT IS MISSING AND IT IS NOT AN OVERSIGHT.**
`rankFo Q a` reads its order from the SET `Q`, through `appAt`
(`agents/tasks/LJ-1-497/Probe497.agda:228-229`). `swo-rank` reads its order
from `oa : IsOrd (fst a)`, through `OrdSWO`
(`agents/tasks/LJ-1-490/Probe490.agda:212`). **Nothing links them.**
`[LJ-1.475]` said so in prose (`agents/tasks/LJ-1-475/lj-1.475-report.md:249`)
and `[LJ-1.497]` turned that prose into a refutation.

**THE RANK IS NO LONGER THE OBSTACLE.** `[LJ-1.515]` is GO: `swo-rank′`
terminates on the re-based order (`agents/tasks/LJ-1-515/Probe515.agda:112-113`),
the padding is deleted, and **`swo-rank′-∅` is PROVED** (`:218-221`), which is
exactly the property `[LJ-1.497]`'s refutation demanded. **So this hypothesis is
the only thing between the tree and a true adequacy.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-518/Probe518.agda::ord-reads-Q"]

## SCOPE (write)
- agents/tasks/LJ-1-518/Probe518.agda
- agents/tasks/LJ-1-518/lj-1.518-report.md
- agents/tasks/LJ-1-518/review-of-ord-reads-Q.md
- agents/tasks/LJ-1-518/runs/

## PREMISES

1. `[LJ-1.497]` wrote the replacement adequacy with this hypothesis missing. Basis: agents/tasks/LJ-1-497/lj-1.497-report.md:209
2. It marked the hypothesis as the missing piece. Basis: agents/tasks/LJ-1-497/lj-1.497-report.md:211
3. `rankFo` reads its order from the set `Q` through `appAt`. Basis: agents/tasks/LJ-1-497/Probe497.agda:228
4. `swo-rank` reads its order from `IsOrd`, through `OrdSWO`. Basis: agents/tasks/LJ-1-490/Probe490.agda:212
5. `[LJ-1.475]` named the disconnect in prose. Basis: agents/tasks/LJ-1-475/lj-1.475-report.md:249
6. `[LJ-1.515]` is GO on the replacement rank. Basis: agents/tasks/LJ-1-515/Probe515.agda:112
7. `swo-rank′-∅` is proved. Basis: agents/tasks/LJ-1-515/Probe515.agda:218
8. `swo-rank′-∅-only` is proved beside it. Basis: agents/tasks/LJ-1-515/Probe515.agda:228
9. `preds` forms and has exactly the members of `a`. Basis: agents/tasks/LJ-1-513/Probe513.agda:103
10. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
11. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**TEN DISPATCHES BUILT THIS ROUTE, ONE REFUTED IT, AND TWO REPAIRED IT.** The
formula is sound, the rank is replaced and proved `∅` at a minimal element, and
the predecessor set forms. **One hypothesis is unstated.**

## THE REASONING

**D-10, BEFORE ANY AGDA.** `Q` is a SET of pairs and the ∈-order is a relation.
Say at `file:line` how the tree turns one into the other, and whether `appAt`
reading `Q` at `(x, m)` is the same statement as `x ∈ m`. **If the two cannot
be equated without a choice of encoding, name the encoding the tree already
uses and state the hypothesis at THAT encoding.** Do not invent one.

**STATE IT AND THEN INHABIT IT AT THE ∈-ORDER.** A hypothesis nobody can
satisfy is not a hypothesis. **The deliverable is the type together with one
witness**: the ∈-order on `a`, as a set of pairs, satisfying it. If no such set
exists in the tree, STOP and say which construction is missing.

**DO NOT BUILD `rankFo-adequate′`.** AD12 gives this brief one obligation, and
the adequacy is the next task after this one.

**DO NOT WEAKEN `rankFo` AND DO NOT CHANGE `swo-rank′`.** Both are delivered and
measured. If the hypothesis cannot be stated against them as they are, that is
the finding.

**DO NOT POSTULATE.**

**REQUIRED REPORT SECTION `## WHAT THE ADEQUACY NEEDS NOW`.** With this
hypothesis in hand, restate `rankFo-adequate′` with no holes and say whether
every input it names is delivered, at `file:line`. **Do not build it.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 160 lines in the probe, of which the obligation is
about 40. BASIS: `[LJ-1.515]` rebuilt this telescope and the rank in a
comparable file. Comparables are of SHAPE and nothing may be funded against
them.

## W3, THE WIDEST UNMEASURED TERM

It is the witness, because a statable hypothesis that nothing satisfies would
leave the adequacy exactly where `[LJ-1.507]` left `someEnv`: green against an
empty antecedent.

    ord-set-witness : (a : S) (oa : IsOrd (fst a)) → Σ[ Q ∈ S ] ord-reads-Q Q a oa

**Write it FIRST, or at least state it, and typecheck it ALONE.** This session
has already lost three dispatches to a statement nothing satisfied
(`[LJ-1.507]`). **Do not repeat that.**

ESTIMATE for W3: about 30 lines and under 45 seconds. **Do not fund it against
`[LJ-1.515]`'s numbers**: that ran a recursion and this builds a set of pairs.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO LEAVES THE CODING LEG WITH ONE TASK: the adequacy itself**, every input
of which would then be delivered.

**A NO-GO SAYS THE FORMULA AND THE RANK CANNOT BE LINKED AT ANY ENCODING**,
which would retire `[LJ-1.475]`'s formula rather than its adequacy, and send the
counting leg back for a ruling with ten dispatches of evidence behind it.

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
  changed_files_none = ["agents/tasks/LJ-1-518/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-518/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-518/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-518/Probe518.agda"]
  changed_files_none = ["agents/tasks/LJ-1-518/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-518/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 167.700)
- CANDIDATE archive/dev/JOURNAL.md  (score 154.667)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 139.149)
- CANDIDATE dev/ARCHIVE.md  (score 120.079)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 108.499)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 52.620)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 46.144)
- CANDIDATE dev/literature/digest.md  (score 36.331)
- CANDIDATE dev/literature/terms-2026-08.md  (score 35.533)
- CANDIDATE dev/literature/geology.md  (score 29.531)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
