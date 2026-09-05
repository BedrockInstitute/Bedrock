# LJ-1.406: `Init` at the ambient least cardinal, from a TRUNCATED hypothesis

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-406/Probe406.agda`.

    init-at-kappa :
        (a : S) (oa : IsOrd (fst a))
      → ⟨ ω ∈ˢ fst (κL a oa) ⟩
      → (ih : (β : V ℓ) → IsOrd β → ⟨ β ∈ˢ fst (κL a oa) ⟩
            → (⟨ β ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq β ∥₁)
      → Init (fst (κL a oa))

`κL` is the SEALED ambient least cardinal, spelled as `[LJ-1.398]` seals it
(`agents/tasks/LJ-1-398/Probe398.agda:126-133`). `Init` and `sq` are the
chapter's own (`src/L/Ordinal/SquareLaw.lagda.md:692-699` and `:685-687`).

**THE POINT OF THIS TASK IS THE WORD `∥ ∥₁` IN THE HYPOTHESIS.** The induction
hypothesis arrives TRUNCATED and the conclusion is `Init`, whose fourth
conjunct ends in `Empty.⊥`. A truncation may be eliminated into a proposition,
so a truncated `sq` is enough to prove a no-injection clause. **Nothing in this
task untruncates anything.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-406/Probe406.agda::init-at-kappa"]

## SCOPE (write)
- agents/tasks/LJ-1-406/Probe406.agda
- agents/tasks/LJ-1-406/lj-1.406-report.md

## PREMISES
- `via-col-square` turns `Init α` into `sq α` and it is delivered and green. Basis: src/L/Ordinal/SquareLaw.lagda.md:960
- `Init` has four conjuncts and the fourth ends in `Empty.⊥`. Basis: src/L/Ordinal/SquareLaw.lagda.md:692
- `sq α` is the pairing and its injectivity, as a Sigma. Basis: src/L/Ordinal/SquareLaw.lagda.md:685
- `κ-inj` is the injection of the site into its ambient least cardinal, and it is TRUNCATED. Basis: src/L/Cardinal.lagda.md:132
- `κ-min-at` refuses a TRUNCATED injection of the site into any member of `κ`, and its conclusion is `Empty.⊥`. Basis: src/L/Cardinal.lagda.md:140
- `oκ` is the ordinal certificate of `κ`, delivered. Basis: src/L/Cardinal.lagda.md:125
- `[LJ-1.404]` delivers successor-closure of `κ` from `⟨ ω ∈ˢ fst a ⟩`, green. Basis: agents/tasks/LJ-1-404/Probe404.agda:202
- `[LJ-1.398]` measured that the TRANSPARENT `LeastCardInjL.κ` exhausts an 8 GB heap and that an opaque seal is the cure. Basis: agents/tasks/LJ-1-398/lj-1.398-report.md:144
- `isL-ord` lifts an ordinal to an L-element in one line. Basis: agents/tasks/LJ-1-398/Probe398.agda:80

## WHAT IS DELIVERED ALREADY

**THE WHOLE POSITIVE SIDE OF THE SQUARE LAW.** `via-col-square`
(`src/L/Ordinal/SquareLaw.lagda.md:960`) is green and takes `Init α` to `sq α`.
Nothing about it has to be rebuilt or reproved.

**THE THREE CHEAP CONJUNCTS OF `Init` AT `κ`.** Conjunct 1 is `oκ`
(`src/L/Cardinal.lagda.md:125`). Conjunct 2 is this brief's hypothesis, because
`[LJ-1.404]` REFUTED it as a theorem: the selected `κ` can be `ω` itself
(`agents/tasks/LJ-1-404/lj-1.404-report.md:18-24`). Conjunct 3 is
`[LJ-1.404]`'s `kappa-is-limit⁺`, green at `agents/tasks/LJ-1-404/Probe404.agda:202`.

**THE MINIMALITY CLAUSE.** `κ-min-at` (`src/L/Cardinal.lagda.md:140`) already
takes its injection TRUNCATED and returns `Empty.⊥`.

## WHAT IS MISSING

**CONJUNCT 4 OF `Init` AT `κ`, AND NOBODY HAS TRIED TO BUILD IT.** Every
dispatch since `[LJ-1.393]` reached `Init` through `AmbCard` and `amb-init'`,
which is a chain of three hypotheses (`agents/tasks/LJ-1-398/lj-1.398-report.md:85-90`).
Conjunct 4 at the ambient least cardinal does not need that chain.

## THE REASONING

**READ CONJUNCT 4 AND NOTICE WHERE IT ENDS.**

    (β : S) → IsOrd β → ⟨ β ∈ˢ α ⟩ → ⟨ ω ∈ˢ β ⟩
      → (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
      → ((m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥

It ends in `Empty.⊥`. `Empty.⊥` is a proposition. So every hypothesis you use to
prove it may be TRUNCATED, and `PT.rec` is the only device you need.

**THE FOUR STEPS, AT `α := fst κ`.** Take `β` infinite with `β ∈ˢ fst κ`, and
`f` injective into the square of `β`.

1. `ih β` gives `∥ sq β ∥₁`. The goal is `Empty.⊥`, so eliminate it by `PT.rec`.
2. Inside, `sq β` is `(g , g-inj)`. Then `λ m → g (f m)` is a map
   `⟪ fst κ ⟫ → ⟪ β ⟫`, injective by `g-inj` then the injectivity of `f`. That is
   `⟪ fst κ ⟫ ↪ ⟪ β ⟫`, as DATA, and it costs three lines.
3. `κ-inj` is `∥ ⟪ fst a ⟫ ↪ ⟪ fst κ ⟫ ∥₁` (`src/L/Cardinal.lagda.md:132`).
   Map step 2's arrow over it with `PT.map` and get
   `∥ ⟪ fst a ⟫ ↪ ⟪ β ⟫ ∥₁`. Composition of two injections is the same three
   lines `[LJ-1.390]` and `[LJ-1.398]` both wrote (`agents/tasks/LJ-1-398/Probe398.agda:85-99`).
4. `κ-min-at (β , isL-ord β oβ)` takes exactly that truncation and returns
   `Empty.⊥` (`src/L/Cardinal.lagda.md:140`).

**THAT IS THE WHOLE TASK.** Conjuncts 1 and 3 are delivered, conjunct 2 is a
hypothesis, conjunct 4 is the four steps above.

**THE ORDINAL CERTIFICATE OF `β`.** `β` is a member of `fst κ`, and `mem-ord`
gives its certificate from `oκ`; `[LJ-1.404]` does it at
`agents/tasks/LJ-1-404/Probe404.agda:211-213`.

**THE SEAL, AND IT IS A MEASUREMENT AND NOT A COPY.** `[LJ-1.398]` measured an
8 GB heap exhaustion when `LeastCardInjL.κ` is spelled transparently, and cured
it with an opaque `κL` (`agents/tasks/LJ-1-398/lj-1.398-report.md:140-153`).
A measured cure does not transfer by analogy. **Seal it here, and say in the
report whether this site needed the seal**: run conjunct 4 once with the seal,
and if it is cheap, say so and stop. Do NOT spend a heap event to prove the
seal was needed.

**W2 (DD4).** `init-at-kappa` is generic in `a`. It names no cardinal, no site
and no numeral. Write it that way and answer W2 in the report.

**W3, THE WIDEST UNMEASURED TERM.** It is CONJUNCT 4, because it is the one
place where a truncation, a composition and `κ-min-at`'s sealed comparison meet,
and because `κ-min-at` is the exact term `[LJ-1.398]` measured as the heap
waller. **The probe is `clause4-at-kappa`: state conjunct 4 ALONE, with `ih` and
`κ-inj` as the only inputs, run it before you write the other three conjuncts,
and report its code lines and its seconds.** ESTIMATE for the obligation: about
30 code lines. BASIS: `[LJ-1.398]`'s `kappa-decides`, measured at 36 code lines
and 1.53 s median at this same site (`agents/tasks/LJ-1-398/lj-1.398-report.md:161-168`),
a comparable of SHAPE and not of size. **Nothing may be funded against it.**

## WHAT GO AND NO-GO EACH EARN

**A GO REPLACES A CHAIN OF THREE HYPOTHESES WITH ONE DELIVERED TERM.**
`[LJ-1.398]`'s positive case runs `amb-card-at-kappa`, then `kappa-is-limit`,
then `amb-init'`, then `via-col-square` (`agents/tasks/LJ-1-398/lj-1.398-report.md:85-90`).
A GO here reaches `Init` from `κ-min-at` alone, and `AmbCard` leaves the route.

**A NO-GO EARNS THE STEP THAT CANNOT BE MADE UNDER A TRUNCATION, AT `file:line`.**
If conjunct 4 needs the injection as data at any point, name that point. That
finding is larger than this task: it would say the no-injection clause is not
the free half it looks like, and the next brief is written from it.

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
  changed_files_any = ["agents/tasks/LJ-1-406/Probe406.agda"]
  changed_files_none = ["agents/tasks/LJ-1-406/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 42
  error_class = "unsolved_meta"
  changed_files_any = ["agents/tasks/LJ-1-406/review-of-*.md"]

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
- CANDIDATE archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md
- CANDIDATE archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md
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
