# LJ-1.396: `AmbCard` has a producer, and the tree already holds it

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build TWO terms in `agents/tasks/LJ-1-396/Probe396.agda`, at a GENERIC ordinal.

    amb-card-at-kappa :
        (a : S) (oa : IsOrd (fst a))
      → AmbCard (fst (LeastCardInjL.κ a oa))

    kappa-is-limit :
        (a : S) (oa : IsOrd (fst a))
      → (γ : V ℓ) → ⟨ γ ∈ fst (LeastCardInjL.κ a oa) ⟩
      → ⟨ sucV γ ∈ fst (LeastCardInjL.κ a oa) ⟩

`AmbCard` is `[LJ-1.393]`'s notion. Spell it in your own file, unfolded, as that
task did (`agents/tasks/LJ-1-393/Probe393.agda:102-104`):

    AmbCard α = (β : V ℓ) → IsOrd β → ⟨ β ∈ α ⟩ → ⟨ ω ∈ β ⟩
              → (⟪ α ⟫ ↪ ⟪ β ⟫) → Empty.⊥

**`LeastCardInjL` IS DELIVERED IN `src/`**, at `src/L/Cardinal.lagda.md:60`. Open
it. Do not restate it, and do not copy any part of it into your file.

**THE SECOND TERM NEEDS `[LJ-1.392]`'s `suc-absorb`. TAKE IT AS A MODULE
HYPOTHESIS**, with the type its report gives
(`agents/tasks/LJ-1-392/Probe392.agda:121`), and do not import that probe. This
is `[LJ-1.395]`'s precedent (`agents/tasks/LJ-1-395/lj-1.395-report.md:44-50`).

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-396/Probe396.agda::amb-card-at-kappa",
               "agents/tasks/LJ-1-396/Probe396.agda::kappa-is-limit"]

## SCOPE (write)
- agents/tasks/LJ-1-396/Probe396.agda
- agents/tasks/LJ-1-396/lj-1.396-report.md

## PREMISES
- `LeastCardInjL` takes one ordinal L-element and no other hypothesis. Basis: src/L/Cardinal.lagda.md:60
- It PRODUCES the ambient least cardinal `κ` of `a` as DATA, because `leastOf` absorbs the truncation. Basis: src/L/Cardinal.lagda.md:122-123
- Its `nonempty` premise is discharged inside the module by the IDENTITY injection, so the selection runs at EVERY ordinal L-element. Basis: src/L/Cardinal.lagda.md:109-114
- `κ-inj`, the injection of `⟪ fst a ⟫` into `⟪ fst κ ⟫`, is TRUNCATED and the chapter says so in a comment. Basis: src/L/Cardinal.lagda.md:132-134
- `κ-min-at` refutes a MERELY existing ambient injection of `⟪ fst a ⟫` into `⟪ fst δ ⟫` at every `δ` that is a member of `fst κ`. Basis: src/L/Cardinal.lagda.md:140-142
- `isL-trans` lifts a member of an L-element to an L-element, which is what `κ-min-at`'s `δ : S` argument needs. Basis: src/L/Constructible.lagda.md:380
- `AmbCard` is a DEFINITION in a probe and `[LJ-1.393]` states that the campaign does not know what producing it costs. Basis: agents/tasks/LJ-1-393/Probe393.agda:98-101
- `[LJ-1.395]` reports that `AmbCard` has NO producer. That sentence is this task's target. Basis: agents/tasks/LJ-1-395/lj-1.395-report.md:219
- `amb-init'` builds `Init` from five inputs, and `AmbCard` is the only one of the five that has no supplier today. Basis: agents/tasks/LJ-1-393/Probe393.agda:207-221
- `via-col-square` turns `Init α` into `sq α`, untruncated. Basis: src/L/Ordinal/SquareLaw.lagda.md:960-961
- `suc-absorb` is GREEN at every ordinal that holds `ω`, and it is an AMBIENT injection. Basis: agents/tasks/LJ-1-392/Probe392.agda:121
- `comp-inj` composes two ambient injections. Basis: src/L/StageCardinal.lagda.md:500
- `sq`. Basis: src/L/Ordinal/SquareLaw.lagda.md:685-687
- `_↪_`. Basis: src/L/Cardinal.lagda.md:47-48

## WHAT IS DELIVERED ALREADY

**THE SELECTION, IN `src/`, AT EVERY ORDINAL.** `LeastCardInjL a oa` gives the
ordinal `κ` as data (`src/L/Cardinal.lagda.md:122-123`), the truncated injection
`κ-inj` (`:133-134`), and the refutation `κ-min-at` (`:140-142`). Nothing about
it is a probe and nothing about it is truncated except `κ-inj`.

**`amb-noinj²`, GREEN.** It turns `AmbCard α` plus the member square laws into
`Init`'s fourth conjunct, by one composition
(`agents/tasks/LJ-1-393/Probe393.agda:119-131`).

**`amb-init'`, GREEN.** With `AmbCard α` in hand, `Init α` follows
(`agents/tasks/LJ-1-393/Probe393.agda:207-221`).

## WHAT IS MISSING

A producer for `AmbCard`. Two reports say the campaign does not have one
(`agents/tasks/LJ-1-393/Probe393.agda:98-101` and
`agents/tasks/LJ-1-395/lj-1.395-report.md:219`).

## THE REASONING

**THE PRODUCER IS ONE COMPOSITION UNDER A TRUNCATION, AND THE TRUNCATION IS
FREE BECAUSE THE CONCLUSION IS `Empty.⊥`.**

Take `κ` from `LeastCardInjL a oa`. Take `β`, an infinite ordinal member of
`fst κ`, and an ambient injection `e : ⟪ fst κ ⟫ ↪ ⟪ β ⟫`. You must reach
`Empty.⊥`.

1. `κ-inj` gives `∥ ⟪ fst a ⟫ ↪ ⟪ fst κ ⟫ ∥₁` (`src/L/Cardinal.lagda.md:133`).
2. Map `comp-inj` with `e` under the truncation. That gives
   `∥ ⟪ fst a ⟫ ↪ ⟪ β ⟫ ∥₁`.
3. Lift `β` to an L-element with `isL-trans`
   (`src/L/Constructible.lagda.md:380`), and apply `κ-min-at`
   (`src/L/Cardinal.lagda.md:140-142`). That is `Empty.⊥`.

**NO STEP UNTRUNCATES ANYTHING.** `PT.map` carries step 2 and `Empty.⊥` absorbs
the truncation at step 3. This is why the producer costs no principle.

**THE SECOND TERM IS THE SAME MOVE AT A SUCCESSOR.** `AmbCard (fst κ)` refutes
AMBIENT injections, and `suc-absorb` PRODUCES one ambiently
(`agents/tasks/LJ-1-392/Probe392.agda:121`). So `fst κ` cannot be the successor
of an infinite member, and closure under successor follows by the ordinal
trichotomy. `amb-init'` needs exactly this closure, and it built the same
trichotomy from a different hypothesis
(`agents/tasks/LJ-1-393/Probe393.agda:213-221`). **Read that proof before you
write yours: three of its four cases are the ones you need.**

**WHAT THIS DOES NOT GIVE YOU, AND DO NOT CLAIM IT.** It gives `AmbCard` at the
SELECTED `κ` and at no other ordinal. `AmbCard (fst a)` itself stays without a
producer, and the arrow from `a` down to `κ` stays TRUNCATED
(`src/L/Cardinal.lagda.md:132-134`). Say both in the report.

**W2 (DD4).** Write both terms at a generic `a`. Name no ordinal, no site and
no numeral in any statement. Answer W2 in the report.

**W3, THE WIDEST UNMEASURED TERM.** It is step 3's lift of `β` to an L-element.
`κ-min-at` takes a `δ : S`, your `β` is a bare `V ℓ`, and `isL-trans` needs a
membership in a level. **The probe is `beta-lifts`: state that one step alone,
run it, and report the number of code lines it took before you write anything
else.** ESTIMATE for the two obligations together: about 25 code lines. BASIS:
`amb-noinj²`, a delivered comparable of SHAPE at 12 code lines
(`agents/tasks/LJ-1-393/Probe393.agda:119-131`), and `amb-init'`'s closure proof
at 8 code lines (`:213-221`). **It is not a comparable of size and nothing may
be funded against it.**

## WHAT GO AND NO-GO EACH EARN

**A GO retires the sentence「`AmbCard` has no producer」and makes the POSITIVE
side of the band recursion free.** With `AmbCard (fst κ)` and `amb-init'`, the
square law at `κ` is DATA through `via-col-square`, and the campaign's residue
falls to the arrow alone.

**A NO-GO earns the step that fails, at `file:line`.** If `κ-min-at` cannot be
reached at a bare member, that is a fact about the chapter's interface and the
next brief repairs the interface. **A stated NO-GO is a full return.**

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
  changed_files_any = ["agents/tasks/LJ-1-396/Probe396.agda"]
  changed_files_none = ["agents/tasks/LJ-1-396/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 42
  error_class = "unsolved_meta"
  changed_files_any = ["agents/tasks/LJ-1-396/review-of-*.md"]

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
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 149.891)
- CANDIDATE dev/ARCHIVE.md  (score 133.412)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 92.996)
- CANDIDATE archive/dev/TASKS-archived.md  (score 85.495)
- CANDIDATE archive/src/2026-08-09-rud-route/L/Condensation.lagda.md  (score 43.227)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 45.013)
- CANDIDATE dev/literature/devlin-II5.md  (score 34.265)
- CANDIDATE dev/literature/geology.md  (score 31.830)
- CANDIDATE dev/literature/terms-2026-08.md  (score 29.587)
- CANDIDATE dev/literature/digest.md  (score 23.990)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
