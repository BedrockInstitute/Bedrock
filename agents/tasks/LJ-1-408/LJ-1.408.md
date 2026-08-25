# LJ-1.408: may the pairing live inside the consumer's truncation?

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-408/Probe408.agda`.

    pair-cross :
        (α : V ℓ) (oα : IsOrd α) (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
      → (s₁ s₂ : sq α)
      → (m₁ c₁ m₂ c₂ : ⟪ α ⟫)
      → fst s₁ (m₁ , c₁) ≡ fst s₂ (m₂ , c₂)
      → (m₁ ≡ m₂) × (c₁ ≡ c₂)

**THIS IS `pair-inj` WITH TWO DIFFERENT PAIRINGS**, and it is the exact step
`L.StageCardinal`'s `h-inj` would have to make if the square law were carried
INSIDE the consumer's truncation instead of beside it
(`src/L/StageCardinal.lagda.md:353` reads `B.pair-inj` at ONE pairing).

**IF IT IS FALSE, REFUTE IT, GREEN, AND LEAVE THE OBLIGATION A HOLE.** That is a
full return and it is what `[LJ-1.396]` and `[LJ-1.404]` both did
(`agents/tasks/LJ-1-396/Probe396.agda:106-110`,
`agents/tasks/LJ-1-404/Probe404.agda:141-145`). Write the obstruction into
`agents/tasks/LJ-1-408/review-of-pair-cross.md`.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-408/Probe408.agda::pair-cross"]

## SCOPE (write)
- agents/tasks/LJ-1-408/Probe408.agda
- agents/tasks/LJ-1-408/review-of-pair-cross.md
- agents/tasks/LJ-1-408/lj-1.408-report.md

## PREMISES
- The consumer takes the square law as a MODULE parameter, so it must be data before the module opens. Basis: src/L/StageCardinal.lagda.md:17
- The chapter spends that parameter at exactly one place. Basis: src/L/StageCardinal.lagda.md:283
- `class-pred` is a TRUNCATED existential and it names `B.pair`. Basis: src/L/StageCardinal.lagda.md:319
- `h` is `leastOf` over that predicate, so `h` is canonical GIVEN the predicate. Basis: src/L/StageCardinal.lagda.md:350
- `h-inj` reads two packages out of two truncations and compares them with `pair-inj` and `cnt-inj`. Basis: src/L/StageCardinal.lagda.md:353
- `cnt` is the formula count and it is a function of the stage embedding. Basis: src/L/StageCardinal.lagda.md:288
- `sq α` is the pairing and its injectivity, as a Sigma, so it is not a proposition. Basis: src/L/Ordinal/SquareLaw.lagda.md:685
- `leastOf` returns data from a truncated non-emptiness whenever the predicate is an hProp. Basis: src/L/WellOrder/Base.lagda.md:158
- `∈-irrefl` refuses a self-membership, which is how two members of an ordinal are separated. Basis: src/V/Hierarchy.lagda.md:155

## WHAT IS DELIVERED ALREADY

**THE CONSUMER, WHOLE.** `LimitStep` builds `h` and `h-inj`
(`src/L/StageCardinal.lagda.md:350` and `:353`) and `Upper.stage-card-upper`
runs the outer recursion (`:564`). Nothing here is rebuilt.

## WHAT IS MISSING

**NOBODY HAS ASKED WHETHER THE CONSUMER NEEDS THE PAIRING AS DATA.** The whole
campaign has assumed it does, because the module parameter is data. That is a
fact about the module's SHAPE and not about its proof.

## THE REASONING

**WHY THIS QUESTION DECIDES THE CAMPAIGN.** `[LJ-1.407]` proves the square law
at every band ordinal up to a truncation, with no residue. Whether that is
enough turns on one thing: can the consumer take it truncated? `h` itself is
already canonical, because it is a `leastOf` over an hProp
(`src/L/StageCardinal.lagda.md:350`). So the pairing could in principle be moved
INSIDE `class-pred`'s truncation and `h` would still be data. The step that then
has to survive is `h-inj`, and `h-inj` compares two packages that would carry
two DIFFERENT pairings. `pair-cross` is that step and nothing else is.

**THE REFUTATION ROUTE, AND IT IS CHEAP.** A pairing composed with a swap of its
two arguments is again a pairing: if `s₁ = (f , f-inj)` then

    s₂ = (λ p → f (snd p , fst p) , <injectivity, by ΣPathP and f-inj>)

is a term of `sq α`. At `s₂` the equation `fst s₁ (u , v) ≡ fst s₂ (v , u)` holds
by `refl`, and `pair-cross` would then force `u ≡ v` for ANY two members. Two
distinct members of an infinite `α` are available, and `∈-irrefl` separates
them. **Measure that, do not assume it.**

**WHAT THE REPORT OWES BESIDE THE TERM, AND IT COSTS NO AGDA.** Two readings,
each answered with `file:line` and a count:

1. **`## THE OTHER SITE`.** `grep` `src/L/StageCardinal.lagda.md` for the module
   parameter `sq` and report EVERY use site with its line. If the count is one,
   say so: the parameter could be an argument of `limit-step` instead of a
   module parameter, and the report should say what that costs in the chapter.
2. **`## THE FAMILY`.** `LimitStep` also takes the stage embeddings as a FAMILY
   `ih` (`src/L/StageCardinal.lagda.md:281`), and `Upper.branch` builds that
   family from the recursion (`:534-559`). Say whether the family could be
   pointwise truncated, and name the term that breaks if it is. **Do not build
   it. Name it.**

**W2 (DD4).** `pair-cross` is generic in `α` and in both pairings. It names no
ordinal and no numeral. A refutation names ONE site, and that is what a
refutation must do (C-42).

**W3, THE WIDEST UNMEASURED TERM.** It is the SWAPPED PAIRING, because it is the
one term that has to be built and because its injectivity is a `ΣPathP` over a
swapped product, which is where an associativity or a transport can surprise.
**The probe is `swap-sq`: state `swap-sq : (α : V ℓ) → sq α → sq α` alone, run
it, and report its code lines before you write anything else.** ESTIMATE for the
obligation: about 25 code lines including the refutation. BASIS:
`[LJ-1.404]`'s `pair-const` and `pair-const-inj`, measured at 6 code lines
(`agents/tasks/LJ-1-404/lj-1.404-report.md:53`), plus that task's
refutation block, measured at four terms. **Comparables of SHAPE, not of size.**

**C-42 BINDS THIS RETURN.** If you refute, sweep: report the COUNT of sites in
`src/` that compare two counts under two different pairings, before you price
any cure.

## WHAT GO AND NO-GO EACH EARN

**A GO ENDS THE CAMPAIGN'S UNTRUNCATION PROBLEM.** With `pair-cross` true, the
pairing moves inside `class-pred`, `[LJ-1.407]`'s truncated square law reaches
the consumer, and every open item about codes, `Ne⁺` and the ambient arrow is
withdrawn.

**A NO-GO EARNS THE CAMPAIGN'S BILL, STATED ONCE AND FOR ALL**: the consumer
needs the pairing as DATA, at `file:line`, for a named reason. That is the
measured warrant `[LJ-2.5]` asks for, and it is worth as much as a GO. **A
stated NO-GO is a full return.** Say in the report, as a TYPE, what would have
to be canonical for `h-inj` to survive a truncated pairing.

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
  changed_files_any = ["agents/tasks/LJ-1-408/Probe408.agda"]
  changed_files_none = ["agents/tasks/LJ-1-408/review-of-pair-cross.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 42
  error_class = "unsolved_meta"
  changed_files_any = ["agents/tasks/LJ-1-408/review-of-pair-cross.md"]

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
- CANDIDATE archive/src/2026-08-09-rud-route/L/CardinalCount.lagda.md
- CANDIDATE archive/src/2026-08-09-rud-route/L/Ordinal/Pairing.lagda.md
- CANDIDATE archive/dev/JOURNAL-archived.md
- CANDIDATE archive/dev/TASKS-archived.md
- CANDIDATE dev/ARCHIVE.md

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md
- CANDIDATE dev/literature/devlin-II5.md
- CANDIDATE dev/literature/digest.md
- CANDIDATE dev/literature/terms-2026-08.md

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
