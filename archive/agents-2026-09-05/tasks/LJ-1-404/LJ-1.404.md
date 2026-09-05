# LJ-1.404: the selected cardinal is infinite, so it IS closed under successor

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build TWO terms in `agents/tasks/LJ-1-404/Probe404.agda`, at a GENERIC ordinal.

    kappa-infinite :
        (a : S) (oa : IsOrd (fst a))
      → ⟨ ω ∈ fst a ⟩
      → ⟨ ω ∈ fst (LeastCardInjL.κ a oa) ⟩

    kappa-is-limit⁺ :
        (a : S) (oa : IsOrd (fst a))
      → ⟨ ω ∈ fst a ⟩
      → (γ : V ℓ) → ⟨ γ ∈ fst (LeastCardInjL.κ a oa) ⟩
      → ⟨ sucV γ ∈ fst (LeastCardInjL.κ a oa) ⟩

**TAKE THE EXACT SPELLING OF EVERY MEMBERSHIP FROM THE SITE.**
`src/L/Cardinal.lagda.md` uses `∈ˢ` in some clauses and the bare `∈` in others;
match `κ-min-at` at `src/L/Cardinal.lagda.md:140-142` and say in the report which
you used.

**`LeastCardInjL` IS DELIVERED IN `src/`**, at `src/L/Cardinal.lagda.md:60`. Open
it. Do not restate it and do not copy any part of it into your file.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-404/Probe404.agda::kappa-infinite",
               "agents/tasks/LJ-1-404/Probe404.agda::kappa-is-limit⁺"]

## SCOPE (write)
- agents/tasks/LJ-1-404/Probe404.agda
- agents/tasks/LJ-1-404/lj-1.404-report.md

## PREMISES
- `LeastCardInjL a oa` produces the ambient least cardinal `κ` of `a` as DATA and takes no hypothesis beyond the ordinal. Basis: src/L/Cardinal.lagda.md:60
- Its `nonempty` premise is discharged inside the module by the IDENTITY injection, so the selection runs at EVERY ordinal L-element, including the finite ones. Basis: src/L/Cardinal.lagda.md:113-114
- `κ-inj` gives the injection of `⟪ fst a ⟫` into `⟪ fst κ ⟫`, truncated. Basis: src/L/Cardinal.lagda.md:133-134
- `κ-min-at` refutes a merely existing injection of `⟪ fst a ⟫` into any `⟪ fst δ ⟫` at a member `δ` of `fst κ`. Basis: src/L/Cardinal.lagda.md:140-142
- `finite-excl` refutes an injection out of an ordinal that holds `ω` into a FINITE ordinal's square. Basis: src/L/Ordinal/SquareLaw.lagda.md:664-668
- The same clause at `ω` itself, in the form the chain uses. Basis: src/L/InjChain.lagda.md:153-155
- `ord-tri` compares any two ordinals and is the tool for the three-way split. Basis: src/L/Ordinal/Linear.lagda.md:136
- `ω-ord`. Basis: src/L/Ordinal.lagda.md:263
- `mem-ord` lifts an ordinal's member to an ordinal. Basis: src/L/Ordinal.lagda.md:221
- `∈-irrefl` is what kills a successor membership in itself. Basis: src/L/Absorption.lagda.md:19
- **THE CONSUMER SUPPLIES A NEARBY HYPOTHESIS AND NOT THIS ONE.** `L.StageCardinal`'s `sq` parameter is quantified over `δ` with `(⟨ δ ∈ ω ⟩ → Empty.⊥)`, which ALLOWS `δ ≡ ω`. Basis: src/L/StageCardinal.lagda.md:16-19
- `squareω` is delivered and covers the `δ ≡ ω` case outright. Basis: src/L/InjChain.lagda.md:184-185

## WHAT IS DELIVERED ALREADY

**THE SELECTION AT EVERY ORDINAL.** `LeastCardInjL` gives `κ` as data, the
truncated arrow `κ-inj`, and the minimality refutation `κ-min-at`
(`src/L/Cardinal.lagda.md:122-142`).

**THE FINITE EXCLUSION.** `FiniteBase.finite-excl` refutes an injection out of an
`ω`-holding ordinal into a finite ordinal's square
(`src/L/Ordinal/SquareLaw.lagda.md:664-668`), and `finite-excl-ω` is the same
clause stated at `ω` (`src/L/InjChain.lagda.md:153-155`).

**THE TRICHOTOMY.** `ord-tri` (`src/L/Ordinal/Linear.lagda.md:136`).

## WHAT IS MISSING

**A PRIOR PROBE BUILT `kappa-is-limit` WITHOUT AN INFINITY HYPOTHESIS AND IT IS
FALSE THAT WAY.** The counterexample is `a := sucV ∅`, the ordinal 1: `⟪ 1 ⟫` is
a singleton, the identity injects it into itself, so the selection returns
`κ ≡ sucV ∅`; then `γ := ∅` is a member of `κ` and `sucV ∅ ∈ sucV ∅` is refuted
by `∈-irrefl`. **A finite ordinal is not closed under successor, and nothing in
the statement forbade a finite `a`.** This task adds the hypothesis and proves
the two terms that make it usable.

## THE REASONING

**THE HYPOTHESIS TRAVELS FROM `a` TO `κ`, AND THAT IS THE FIRST TERM.**

`kappa-is-limit⁺` needs `⟨ ω ∈ fst κ ⟩`, and the caller has `⟨ ω ∈ fst a ⟩`.
Those are different ordinals and the step between them is `kappa-infinite`,
which is why it is a separate obligation and comes first.

Suppose `fst κ` were finite. `κ-inj` gives `⟪ fst a ⟫ ↪ ⟪ fst κ ⟫`, truncated,
and `fst a` holds `ω`. That is an injection out of an `ω`-holding ordinal into a
finite one, which `finite-excl` refutes
(`src/L/Ordinal/SquareLaw.lagda.md:664-668`). **Read that signature before you
plan the proof: it takes `f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫`, a map into the SQUARE, not
a plain injection.** Adapting a plain injection to it costs a pairing with a
fixed member of `⟪ β ⟫`, and finding that member is a real step. **Measure it and
report it.** If the adaptation is not free, say so and use `finite-excl-ω`
(`src/L/InjChain.lagda.md:153-155`) or state what a plain-injection form would
cost. The truncation is free throughout because the conclusion is `Empty.⊥`.

**THE SECOND TERM IS THE SUCCESSOR CLOSURE, AND THE INFINITY IS NOW IN HAND.**
With `⟨ ω ∈ fst κ ⟩`, split `γ` against `ω` by `ord-tri`
(`src/L/Ordinal/Linear.lagda.md:136`):

- `γ ∈ ω`: the successor of a numeral is a numeral, and `ω` is a member of
  `fst κ`, so transitivity carries `sucV γ` into `fst κ`.
- `γ ≡ ω`: `sucV ω` must be a member of `fst κ`. **This is the case to watch.**
  It does not follow from `⟨ ω ∈ fst κ ⟩` alone, and if you cannot close it, that
  is the honest boundary of the term: report it as an added hypothesis with its
  type rather than assuming it.
- `ω ∈ γ`: this is the infinite case, and it is where `AmbCard` at `κ` does the
  work: an ambient injection out of `⟪ fst κ ⟫` into an infinite member would
  contradict minimality through `κ-min-at`.

**WHAT THIS DOES NOT GIVE YOU, AND DO NOT CLAIM IT.** It gives closure at the
SELECTED `κ` and at no other ordinal. It does not prove `AmbCard (fst a)`, it does
not touch the arrow's truncation, and it does not discharge any module parameter.

**W2 (DD4).** Write both terms at a generic `a`. Name no numeral, no cardinal and
no site in any statement. The counterexample above is a REFUTATION at a site and
belongs in the report, never in a statement. Answer W2 in the report.

**W3, THE WIDEST UNMEASURED TERM.** It is the CONSUMER BRIDGE, because the
consumer's hypothesis is not this task's hypothesis and the gap is a whole case.
`L.StageCardinal` quantifies `sq` over `δ` with `(⟨ δ ∈ ω ⟩ → Empty.⊥)`
(`src/L/StageCardinal.lagda.md:16-19`), which ALLOWS `δ ≡ ω`, while both terms
here want `⟨ ω ∈ fst a ⟩`. **The probe is `infinite-or-omega`: state

    infinite-or-omega : (δ : V ℓ) → IsOrd δ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
                      → (δ ≡ ω) ⊎ ⟨ ω ∈ δ ⟩

alone, prove it by `ord-tri`, run it, and report the number of code lines before
you write anything else.** It is what lets a caller feed these terms, and the
`δ ≡ ω` branch is then `squareω` outright (`src/L/InjChain.lagda.md:184-185`).
ESTIMATE for the two obligations together: about 35 code lines. BASIS:
`finite-excl-ω` at `src/L/InjChain.lagda.md:153-169`, a delivered comparable of
SHAPE at 17 code lines, and `amb-init'`'s own three-way `ord-tri` closure proof at
`agents/tasks/LJ-1-393/Probe393.agda:213-221`, 9 code lines. **Neither is a
comparable of size and nothing may be funded against them.**

## WHAT GO AND NO-GO EACH EARN

**A GO REPAIRS A REFUTED TERM AT ITS OWN SITE AND CONNECTS IT TO THE CONSUMER.**
With `kappa-is-limit⁺` and the bridge, the positive side of the band recursion
reaches `Init` and therefore `via-col-square`
(`src/L/Ordinal/SquareLaw.lagda.md:960-961`), which is the square law as DATA.

**A NO-GO EARNS THE CASE THAT CANNOT CLOSE, AT `file:line`.** The `γ ≡ ω` case is
the likely one. If it needs `⟨ sucV ω ∈ fst κ ⟩` as a further hypothesis, say so
with its type: that is a fact about the selection and it re-plans the positive
side. **A stated NO-GO is a full return.**

## BRANCHES
```toml pod-branches
[[branch]]
id = "go"
priority = 10
action = "done"
outcome = "go"

  [branch.when]
  exit_code = 0
  obligations_delta_max = -2
  heap_wall = false

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-404/Probe404.agda"]
  changed_files_none = ["agents/tasks/LJ-1-404/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 42
  error_class = "unsolved_meta"
  changed_files_any = ["agents/tasks/LJ-1-404/review-of-*.md"]

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
- CANDIDATE archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md  (score 46.203)
- CANDIDATE archive/src/2026-08-09-rud-route/L/Ordinal  (score 40.118)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 36.550)
- CANDIDATE archive/dev/TASKS-archived.md  (score 30.220)
- CANDIDATE dev/ARCHIVE.md  (score 25.771)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 48.660)
- CANDIDATE dev/literature/terms-2026-08.md  (score 27.115)
- CANDIDATE dev/literature/devlin-II5.md  (score 23.442)
- CANDIDATE dev/literature/digest.md  (score 19.008)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
