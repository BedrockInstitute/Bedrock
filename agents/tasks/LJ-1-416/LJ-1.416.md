# LJ-1.416: the rank of a well-order, as DATA, at a generic small carrier

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-416/Probe416.agda`, at a GENERIC small
type `A` with a GENERIC well-order on it.

    swo-rank-mono : (a b : A) → SWO._<∙_ w a b
                  → ⟨ swo-rank a ∈ˢ swo-rank b ⟩

`swo-rank : A → S` and `swo-rank-ord : (a : A) → IsOrd (swo-rank a)` are built
on the way and are part of this obligation.

**THE CARRIER IS SMALL AND THE ORDER IS NOT. THAT IS THE WHOLE TASK.** Take
`A : Type ℓ` and `w : SWO A` with the order level instantiated at `ℓ-suc ℓ`,
which is the instantiation the tower uses (`src/L/Choice/Step.lagda.md:58`).
`boundingOrd` accepts an index type at level `ℓ` only
(`src/L/Ordinal.lagda.md:154`). So the predecessor family must be indexed by
`A` itself and never by `Σ[ b ∈ A ] (b <∙ a)`, which sits at `ℓ-suc ℓ`.

**DO NOT USE `leastOf` AND DO NOT USE `PT.rec`.** This term selects nothing.
It computes.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-416/Probe416.agda::swo-rank-mono"]

## SCOPE (write)
- agents/tasks/LJ-1-416/Probe416.agda
- agents/tasks/LJ-1-416/lj-1.416-report.md

## PREMISES
- `boundingOrd` bounds a family of ordinals indexed by a SMALL type by one ordinal, and it returns a genuine pair and not a truncated existence. Basis: src/L/Ordinal.lagda.md:154
- The bound is delivered with its ordinal certificate and its membership law. Basis: src/L/Ordinal.lagda.md:155
- `SWO` carries `wf∙`, a well-foundedness field, so a recursion on the order is available without any extra hypothesis. Basis: src/L/WellOrder/Base.lagda.md:107
- `SWO` carries `tri∙`, trichotomy, so the comparison is DECIDED and no LEM is needed to split on it. Basis: src/L/WellOrder/Base.lagda.md:104
- `SWO` carries `irr∙`, irreflexivity. Basis: src/L/WellOrder/Base.lagda.md:105
- The order level is a module parameter of the well-order chapter, and the tower instantiates it at `ℓ-suc ℓ`. Basis: src/L/WellOrder/Base.lagda.md:54
- The tower's own instantiation of that chapter is at `ℓ-suc ℓ`. Basis: src/L/Choice/Step.lagda.md:58
- `boundingOrd` is already applied to a member type of a stage, so the small-index shape is delivered and not hypothetical. Basis: src/L/Reflect.lagda.md:447
- The ordinals of this chapter are the ambient ones. Basis: src/L/Ordinal.lagda.md:59

## WHAT IS DELIVERED ALREADY

**THE SUP DEVICE, AND IT IS ALREADY USED AT THIS EXACT SHAPE.** `Fbnd` at
`src/L/Reflect.lagda.md:447` calls `boundingOrd` on `⟪ Lset σ ⟫ ^ k`, a member
type of a stage. It is the closest delivered comparable in the tree and it is
green today.

**THE RECURSION PRINCIPLE.** `wf∙` is a field of the record, so the accessibility
predicate arrives with the order and costs nothing to obtain.

**THE SPLIT.** `tri∙` decides `a <∙ b` against `a ≡ b` against `b <∙ a`, so the
family below is definable without classical logic.

## WHAT IS MISSING

**NOTHING IN THE TREE TURNS A WELL-ORDER INTO AN ORDINAL.** There is no `rank`,
no `orderType` and no `otp` under `src/` or under `archive/src/`. This task
builds the first one.

## THE REASONING

**THE FAMILY IS INDEXED BY THE WHOLE CARRIER, AND THE ORDER ONLY SELECTS WHAT
IT CONTRIBUTES.** Define, inside the recursion at `a` with its accessibility
witness:

    f : A → S
    f b = swo-rank b        when `tri∙ b a` reports `b <∙ a`
    f b = ∅                 in the two other cases

Then `swo-rank a` is the bounding ordinal of `f`, that is
`fst (boundingOrd A f _)`. **`f` is total on `A`, which is small, so
`boundingOrd` applies.** The two other cases contribute the empty set, which is
an ordinal and which changes no bound that matters.

**WHY THAT GIVES MONOTONICITY.** For `a <∙ b`, the family at `b` sends `a` to
`swo-rank a`, and `boundingOrd`'s membership law says every family value is a
member of the bound. So `⟨ swo-rank a ∈ˢ swo-rank b ⟩` is exactly that law
instantiated at `a`. **The proof is one projection and no induction.**

**W2 (DD4).** The term is generic in `A` and in `w`. Name no stage, no cardinal
and no numeral. `[LJ-1.418]` instantiates it at the tower. **A term that names
`Lset` has failed this clause.**

**W3, THE WIDEST UNMEASURED TERM, AND IT IS A LEVEL AND NOT A PROOF.**

    rank-recursion-elaborates : A → S

**Build the recursion ALONE, with the body returning `∅` in every case, run it,
and report whether the recursion is accepted at these levels BEFORE you prove
anything about it.** The risk is that the recursion's motive, which mentions
`Acc _<∙_ a` at `ℓ-suc ℓ`, and `boundingOrd`'s demand for `Type ℓ`, cannot be
met at once. **If they cannot, that is the finding and it is worth the whole
dispatch.** ESTIMATE: about 12 code lines for the skeleton. BASIS: `Fbnd` at
`src/L/Reflect.lagda.md:447-449` is three lines plus its statement, and this
adds the accessibility argument and the trichotomy split. ESTIMATE for the whole
obligation: about 45 code lines. BASIS: the same comparable plus the two
one-projection proofs. **Comparables of SHAPE and never of size, and nothing may
be funded against them.**

**REPORT THE LEVELS YOU ACTUALLY USED.** Write in the report the level of `A`,
the level of `_<∙_`, and the level `boundingOrd` demanded. If you had to move
any of the three, say which and why. **That table is what `[LJ-1.417]` and
`[LJ-1.418]` are priced against.**

**D-10.** If the level obstruction is real, do not weaken the statement to
something you can prove. Do not shrink the order to level `ℓ`, because the tower
does not offer it there. State the obstruction as a type and stop.

## WHAT GO AND NO-GO EACH EARN

**A GO OPENS A ROUTE THAT NEEDS NO PAIRING AND NO TRUNCATION.** The campaign's
whole bill to date is a pairing that must be DATA. A rank needs neither.

**A NO-GO EARNS THE LEVEL WALL AT `file:line`, AND IT IS WORTH AS MUCH.** If
`boundingOrd`'s `Type ℓ` cannot meet an order at `ℓ-suc ℓ`, say so with the
exact error and the exact two levels. **That would close the route in one
dispatch instead of four, and it is a full return.**

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev, archive/scripts, dev/ARCHIVE.md:
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 149.577)
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 143.628)
- CANDIDATE dev/ARCHIVE.md  (score 134.647)
- CANDIDATE archive/dev/JOURNAL.md  (score 125.613)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 104.144)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 86.753)
- CANDIDATE dev/literature/devlin-II5.md  (score 56.968)
- CANDIDATE dev/literature/digest.md  (score 51.115)
- CANDIDATE dev/literature/terms-2026-08.md  (score 46.833)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 43.017)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

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
  changed_files_any = ["agents/tasks/LJ-1-416/Probe416.agda"]
  changed_files_none = ["agents/tasks/LJ-1-416/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-416/review-of-*.md"]

[[branch]]
id = "heap-wall-escalate"
priority = 30
action = "escalate"
head_slot = "mathematician_adversarial"

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
