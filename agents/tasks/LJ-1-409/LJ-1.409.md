# LJ-1.409: a code that FITS, by trimming it to the pairs it is about

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-409/Probe409.agda`.

    place-code :
        (a c : S)
      → ∥ Σ[ F ∈ S ] InjCode F a c ∥₁
      → ∥ Σ[ F ∈ Mem (Lset (SiteBound.β a)) ] InjCode (SiteBound.up a F) a c ∥₁

**THIS IS `[LJ-1.397]`'s `code-lands` WITH ITS `Placement` HYPOTHESIS REMOVED**
(`agents/tasks/LJ-1-397/CodeLands.agda:40-41` and `:46-49`). That task proved
the implication FROM the placement and named the placement as the campaign's
bill on the coded side. This task pays the bill a different way: **it does not
place the given code, it replaces the given code by one that fits.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-409/Probe409.agda::place-code"]

## SCOPE (write)
- agents/tasks/LJ-1-409/Probe409.agda
- agents/tasks/LJ-1-409/review-of-place-code.md
- agents/tasks/LJ-1-409/lj-1.409-report.md

## PREMISES
- `InjCode` is four conjuncts, and every one of them is a universally quantified condition on the PAIRS the code holds. Basis: src/L/Cardinal.lagda.md:223
- The fourth conjunct reads a pair out of the code and lands its second component in the target. Basis: src/L/Cardinal.lagda.md:228
- `SiteBound.β` is the ordinal the bookkeeping runs in, produced by `stageBound`. Basis: src/L/Cardinal.lagda.md:166
- `stageBound` is above a set's own stage and above `ω`. Basis: src/L/Choice/Stage.lagda.md:366
- `bound-below₂` places a member of a member of a set inside `Lset (stageBound ...)`. Basis: src/L/Choice/Stage.lagda.md:370
- `PairBound` builds the set that holds every pair over two sets, with the membership read delivered. Basis: src/L/InjChain.lagda.md:276
- `InjChain` already carves a graph out of that bound by separation, and it is delivered and green. Basis: src/L/InjChain.lagda.md:339
- `hasSeparationL` is the model's separation and it takes a bound and a one-place formula. Basis: src/L/Axioms/Full.lagda.md:144
- `pr` is the pair. Basis: src/V/Coding.lagda.md:175
- `[LJ-1.397]` reduced the whole `S`-to-`Mem` implication to the one placement step. Basis: agents/tasks/LJ-1-397/CodeLands.agda:40
- `InternalLeastCard.Good` quantifies its code over `Mem (Lset (SiteBound.β κ))`, which is why the `Mem` form is the one the tree consumes. Basis: src/L/Cardinal.lagda.md:240

## WHAT IS DELIVERED ALREADY

**THE IMPLICATION, GIVEN THE PLACEMENT.** `code-lands` is green under the
hypothesis (`agents/tasks/LJ-1-397/CodeLands.agda:46-49`), and the rest of it is
one `Σ≡Prop` transport. Take that file's shape; do not re-derive it.

**THE CARVE.** `src/L/InjChain.lagda.md:339` separates a graph out of
`PairBound.bnd` and reads its membership back at `:344`. That is the same move
this task makes, at a different formula.

## WHAT IS MISSING

**A CODE THAT SITS WHERE THE TREE LOOKS FOR IT.** `InjCode F a c` puts NO bound
on `F` (`src/L/Cardinal.lagda.md:223-228`), so an arbitrary code can be
arbitrarily large, and `[LJ-1.397]` measured that nothing delivered places one
(`agents/tasks/LJ-1-397/CodeLands.agda:38-41`).

## THE REASONING

**READ THE FOUR CONJUNCTS AND NOTICE WHAT NONE OF THEM SAYS.** Each conjunct is
a condition on the pairs `F` holds (`src/L/Cardinal.lagda.md:223-228`). **None
of them says `F` holds ONLY pairs.** So a code may carry any amount of matter
that no conjunct reads, and that matter is what makes it too big. The cure is
not to place the code. It is to throw the unread matter away.

**THE TRIM.** With `F` given, put

    F' = { p ∈ PairBound.bnd a c | p ∈ F }

by `hasSeparationL` (`src/L/Axioms/Full.lagda.md:144`), exactly as
`src/L/InjChain.lagda.md:339` carves its composite out of the same bound.
Then argue the four conjuncts for `F'`:

- Each conjunct's hypothesis is `⟨ pr x y ∈ F' ⟩`, and membership in `F'`
  gives membership in `F` by the separation spec, so the conjunct transfers
  DOWN for free.
- Each conjunct's conclusion that asserts a pair IS in the code has to
  transfer UP, and that is where the bound is read: the pair is over `a` and
  `c`, so it is in `PairBound.bnd a c` by `PairBound`'s own membership lemma
  (`src/L/InjChain.lagda.md:295-311`), and separation puts it back in `F'`.

**THEN THE PLACEMENT IS ABOUT A BOUNDED SET AND NOT AN ARBITRARY ONE.** `F'` is
a subset of `PairBound.bnd a c`, and `c` is reachable from `a` in the cases the
tree consumes. Decide whether `Lset (SiteBound.β a)` holds `F'`, using
`bound-below₂` (`src/L/Choice/Stage.lagda.md:370`) and `stageBound`'s own
guarantee (`:366`).

**IF IT DOES NOT, THAT IS THE MEASUREMENT AND IT IS THE POINT OF THE TASK.**
Report the SMALLEST number of successor steps `n` for which
`⟨ fst F' ∈ˢ Lset (<n successors of SiteBound.β a>) ⟩` is provable, and say
which lemma supplies each step. **A number is a full return here. A guess is
not.** Write the obstruction into
`agents/tasks/LJ-1-409/review-of-place-code.md` and leave the obligation a
hole, as `[LJ-1.396]` and `[LJ-1.404]` did.

**DO NOT TOUCH `src/`.** If the answer is that the chapter's `SiteBound.β` must
grow, say so with the number; changing the chapter is a later task and not this
one.

**W2 (DD4).** `place-code` is generic in `a` and `c`. It names no cardinal, no
ordinal and no numeral.

**W3, THE WIDEST UNMEASURED TERM.** It is the UPWARD transfer of the conjuncts
to `F'`, because the downward direction is free and the upward direction is the
only place the bound is read. **The probe is `trim-conj4`: state conjunct 4 of
`InjCode` for `F'` ALONE, given conjunct 4 for `F` and the separation spec, run
it, and report its code lines before you write the other three.** ESTIMATE for
the obligation: about 60 code lines. BASIS: `Comp`'s carve and its two
membership readings at `src/L/InjChain.lagda.md:335-350`, a delivered
comparable of SHAPE at about 16 code lines, and `code-lands` itself, delivered
at 17 code lines (`agents/tasks/LJ-1-397/CodeLands.agda:46-62`). **Neither is a
comparable of size and nothing may be funded against them.**

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS THE CAMPAIGN'S NAMED BILL ON THE CODED SIDE.** `[LJ-1.397]` called
`Placement`「the campaign's named bill on the coded side」, and `[LJ-1.403]`
named the same thing twice more as its gaps 1 and 2
(`agents/tasks/LJ-1-403/lj-1.403-report.md:144-163`). A GO retires all three at
once and makes `[LJ-1.397]`'s `coded-arrow` unconditional.

**A NO-GO EARNS A NUMBER**: how far above `SiteBound.β a` a code has to live.
That converts an unpriced residue into a priced one, and it is worth as much as
a GO. **A stated NO-GO is a full return.**

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
  changed_files_any = ["agents/tasks/LJ-1-409/Probe409.agda"]
  changed_files_none = ["agents/tasks/LJ-1-409/review-of-place-code.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 42
  error_class = "unsolved_meta"
  changed_files_any = ["agents/tasks/LJ-1-409/review-of-place-code.md"]

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

## LAWS (program-generated, do not edit)

MANDATORY for kind `probe` (measures one thing and keeps the file as the report's other half. Gating, heap discipline, the transplant law, which is what a probe most often gets wrong, and the extent law, because a probe that refutes has measured ONE site.):

- **D-1. The probe doctrine**
  **Rule:** Before committing to a heavy or hard-to-reverse path, run the cheapest decisive probe with its abort criterion fixed in advance; a red verdict costs the attempt and nothing else.
  Full entry: dev/LESSONS.md:1064
- **P-l. A statement may be ABOUT a concrete stage without dragging that stage's PRESENTATION into its type**
  **The law.** Being about a concrete position is not what costs. Naming a transparent construction in a statement's TYPE is. If the tower's stage values are `opaque` upstream, a theorem may quantify over, hypothesize about and conclude at `Sset ω` freely, because the stage is an ATOM to the elaborator and nothing unfolds. If instead the type mentions a transparent presentation, such as `⟪ sucV (...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2357
- **P-i. The conversion-explosion playbook (imported from the source project)**
  **Rule:** When cubical Agda hangs or exhausts memory on this codebase family, the cause is one of three heavy-thing classes forced into normalization, and the cure is selected by the decision tree below, not by trial. Imported whole from the antecedent development's worklog (`../fol-reification/docs/WORKLOG.md` §5, twenty measured cases); read that section before any surgery on a hang.
  Full entry: dev/LESSONS.md:229
- **C-12. Agda runs under a hard heap cap; parallel writers under a quota**
  **Rule:** Every agda invocation runs under a GHC heap cap (`GHCRTS=-M<n>g`) so a runaway typecheck dies with a clean "Heap exhausted" exit instead of OOM-killing the machine; the orchestrator's audits run at `-M16g` and `make` exports a default. Sub-agent concurrency is TIERED (owner-widened 2026-08-02 once the caps and the watchdog were live): WIDE mode for routine batches, up to FOUR concurre...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2135
- **D-10. Price the truth of a recorded residue before pricing its proof**
  **Rule:** A residue recorded under the wall protocol names a TARGET, and a target can be false; before dispatching a discharge batch, spend the five minutes checking the target's truth at the intended generality (a Tarskian or cardinality obstruction is the usual killer), and record the corrected target beside the original.
  Full entry: dev/LESSONS.md:1375
- **C-22. A dispatched agent writes its deliverable incrementally, never at the end**
  **Rule:** When an agent's deliverable is a file, the brief must require it WRITTEN EARLY as a skeleton and filled incrementally, saving after each answer lands. An agent that researches for its whole budget and leaves the writing to the end returns nothing when the budget runs out, and its research dies with it. A partial dossier is a real deliverable; an unwritten perfect one is not.
  Full entry: dev/LESSONS.md:2297
- **R-40. A deep successor-chain membership witness normalizes super-linearly; climb by small closures**
  **Rule:** An ordinal-membership premise stated at a deep iterated successor (`+ω-iter n`, a `sucV`-chain) forces the conversion checker to normalize the whole chain against the level's union representation, and the cost is super-linear in the depth. State the witness at a SHALLOW index and climb by the limit-ordinal successor closure (`limit-succ-mem`, `L.Rud.Hierarchy:455`), one step per line....
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:955
- **C-42. A refutation measures the site it names, and it never measures how far that site extends**
  **Rule:** A refutation is a measurement of ONE site. It says the statement there is false. **It says nothing about how many other sites carry the same false shape.** So when a refutation lands, the next action is not the cure. **It is the sweep: search the tree for the shape, and report the COUNT before you price the cure.** A cure funded against the named site is priced against a number nobody...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:3752

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev/TASKS-archived.md, archive/dev/JOURNAL-archived.md, archive/dev/DECISIONS-archived.md, dev/ARCHIVE.md:
- CANDIDATE archive/src/2026-08-09-rud-route/L/Coding
- CANDIDATE archive/src/2026-08-09-rud-route/L/PairAtoms.lagda.md
- CANDIDATE archive/dev/JOURNAL-archived.md
- CANDIDATE archive/dev/TASKS-archived.md
- CANDIDATE dev/ARCHIVE.md

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/j-hierarchy.md
- CANDIDATE dev/literature/digest.md
- CANDIDATE dev/literature/rudimentary-functions.md
- CANDIDATE dev/literature/terms-2026-08.md

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
