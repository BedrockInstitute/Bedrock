# LJ-1.398: the band recursion on the two selections, and what is left

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build TWO terms in `agents/tasks/LJ-1-398/Probe398.agda`, at a GENERIC band.

    band-owes-2 : Type (ℓ-suc ℓ)

    sq-band-2 : band-owes-2
              → (α : V ℓ) → IsOrd α → ⟨ α ∈ sucV α₀ ⟩ → (⟨ α ∈ ω ⟩ → Empty.⊥)
              → sq α

`sq-band-2` must match `L.StageCardinal`'s module parameter EXACTLY, not merely
resemble it (`src/L/StageCardinal.lagda.md:17-19`). **Check the match with a term
that instantiates the chapter, and say in the report that you checked it.**
`[LJ-1.395]` did this with `plugs-in` and its report names the check
(`agents/tasks/LJ-1-395/lj-1.395-report.md:27`).

`band-owes-2` is a type YOU write. It states what the recursion still owes when
the four cases below are spent. **Keep it as small as the cases allow, and say in
the report what each conjunct is for.**

**THE FOUR CASES, AND THE SUPPLIER OF EACH.** Recurse by `∈-induction`
(`src/V/Hierarchy.lagda.md:177-180`). At an infinite band ordinal `α`, split by
`lem` on `IsCardinalL`, which is a proposition because it concludes in
`Empty.⊥`.

| the case | the supplier |
|---|---|
| `α ≡ ω` | `squareω`, delivered (`src/L/InjChain.lagda.md:184-185`) |
| `IsCardinalL` FAILS at `α` | `[LJ-1.397]`'s `coded-arrow`, then the composite below |
| `IsCardinalL` holds and `α` is the ambient least cardinal of itself | `[LJ-1.396]`'s `amb-card-at-kappa`, then `amb-init'`, then `via-col-square` |
| `IsCardinalL` holds and `α` is NOT | `band-owes-2`. **This is the residue** |

**TAKE EVERY SUPPLIER AS A HYPOTHESIS OF YOUR OWN MODULE.** Do not import an
earlier probe and do not copy its proof. Take the STATEMENT of each with the type
its report gives. **This is what makes the task cheap, separately checkable, and
immune to a supplier that later changes.** `[LJ-1.395]` set the precedent and its
report explains the one spelling constraint the witness meter puts on a module
hypothesis (`agents/tasks/LJ-1-395/lj-1.395-report.md:44-56`).

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-398/Probe398.agda::band-owes-2",
               "agents/tasks/LJ-1-398/Probe398.agda::sq-band-2"]

## SCOPE (write)
- agents/tasks/LJ-1-398/Probe398.agda
- agents/tasks/LJ-1-398/lj-1.398-report.md

## PREMISES
- The consumer takes `sq` as a module parameter over every `δ` in `sucV α₀` outside `ω`, with no cardinality hypothesis. Basis: src/L/StageCardinal.lagda.md:17-19
- The parameter is spent at exactly one place in the chapter. Basis: src/L/StageCardinal.lagda.md:283
- `∈-induction` is delivered. Basis: src/V/Hierarchy.lagda.md:177-180
- `squareω` closes the base case. Basis: src/L/InjChain.lagda.md:184-185
- `via-col-square` turns `Init α` into `sq α` untruncated. Basis: src/L/Ordinal/SquareLaw.lagda.md:960-961
- `amb-init'` builds `Init α` from `AmbCard α`, two memberships and the member square laws. Basis: agents/tasks/LJ-1-393/Probe393.agda:207-221
- `LeastCardInjL` produces the ambient least cardinal of any ordinal L-element as DATA. Basis: src/L/Cardinal.lagda.md:122-123
- Its witness stays truncated, and the chapter says so. Basis: src/L/Cardinal.lagda.md:132-134
- `comp-inj` composes two ambient injections. Basis: src/L/StageCardinal.lagda.md:500
- `[LJ-1.390]`'s `descent-core` is the composite that turns an arrow plus the law below into the law above. Basis: agents/tasks/LJ-1-390/Probe390.agda:110-131
- `[LJ-1.395]` built this recursion once with a different split and returned GO. Basis: agents/tasks/LJ-1-395/lj-1.395-report.md:31-35
- Its residue was the arrow at every negative site. Basis: agents/tasks/LJ-1-395/lj-1.395-report.md:205-210
- `IsCardinalL` is a proposition-valued refutation of a coded injection at every member. Basis: src/L/Cardinal.lagda.md:230-233
- `mem-ord` gives the ordinal certificate at a member. Basis: src/L/Ordinal.lagda.md:221-222
- `ord-tri` gives the trichotomy the `α ≡ ω` split needs. Basis: src/L/Ordinal/Linear.lagda.md:136
- `∈-irrefl`. Basis: src/V/Hierarchy.lagda.md:155
- `sq`. Basis: src/L/Ordinal/SquareLaw.lagda.md:685-687
- `Init`. Basis: src/L/Ordinal/SquareLaw.lagda.md:692-699
- `_↪_`. Basis: src/L/Cardinal.lagda.md:47-48

## WHAT IS DELIVERED ALREADY

`[LJ-1.395]` assembled this recursion with the split on `AmbCard` and returned GO
(`agents/tasks/LJ-1-395/lj-1.395-report.md:31-35`). **This task is not that task
again.** It changes ONE thing, the notion the split decides, and the change moves
the residue from every negative site to one positive site.

## WHAT IS MISSING

The recursion under the split that makes both sides payable, and the exact size
of what is left after it.

## THE REASONING

**THE TWO SPLITS FAIL AT OPPOSITE PLACES, AND THIS TASK MEASURES THE SECOND
ONE.**

`[LJ-1.395]` split on `AmbCard`. Its positive side is free, because `amb-init'`
turns `AmbCard` into `Init`. Its negative side owes an AMBIENT arrow, which
`[LJ-1.394]` measured is unreachable
(`agents/tasks/LJ-1-394/lj-1.394-report.md:36-44`).

Split on `IsCardinalL` instead. The NEGATIVE side is then free, because the
failure hands over a CODED witness and `[LJ-1.397]`'s `coded-arrow` reads it out
as data. The POSITIVE side splits again:

- When `α` IS the ambient least cardinal of itself, `[LJ-1.396]` gives
  `AmbCard α`, `amb-init'` gives `Init α`, and `via-col-square` gives `sq α` as
  data. **Free.**
- When it is not, `α` is an L-cardinal that the ambient theory injects into
  something smaller, merely. **That case is the residue, and it is what
  `band-owes-2` must state.**

**THE DESCENT STEP IS DELIVERED AND YOU MUST NOT REBUILD IT.** Given the arrow
`⟪ α ⟫ ↪ ⟪ b ⟫` as data and `sq b` from the induction hypothesis, the composite
that gives `sq α` is `[LJ-1.390]`'s `descent-core`
(`agents/tasks/LJ-1-390/Probe390.agda:110-131`). Take its STATEMENT as a
hypothesis, like the others.

**DO NOT MAKE THE RESIDUE BIGGER THAN THE CASE.** The residue is owed at ONE
class of ordinal: an L-cardinal in the band that is not its own ambient least
cardinal. If your `band-owes-2` quantifies over more ordinals than that, the
report must say why, at `file:line`.

**W2 (DD4).** The recursion is generic in `α` and in `α₀`. Name no site.
Answer W2 in the report.

**W3, THE WIDEST UNMEASURED TERM.** It is the SECOND positive split: deciding
whether `α` is its own ambient least cardinal. `LeastCardInjL` gives `κ` as data
(`src/L/Cardinal.lagda.md:122-123`), so the decision is an ordinal comparison of
`fst κ` with `fst α`, and the ordinal trichotomy decides it. **The probe is
`kappa-decides`: state that comparison alone, run it, and report its cost before
you assemble anything.** ESTIMATE for the two obligations: about 90 code lines.
BASIS: `[LJ-1.395]`'s own assembly, a delivered comparable of SHAPE with one
fewer case, whose report gives its measured size
(`agents/tasks/LJ-1-395/lj-1.395-report.md`, section 1). **Do not fund against
90.**

## WHAT GO AND NO-GO EACH EARN

**A GO reduces the whole GCH module parameter to ONE named case**, at one class of
ordinal, with every other case fed by a delivered or a green term. That is the
first time this campaign would hold a single-obligation state.

**A NO-GO earns the mismatch between two suppliers' types, at `file:line`.** An
assembly that fails when every case has a supplier is a statement about the
motive or about an interface, and both are cheap to repair once named.

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
  changed_files_any = ["agents/tasks/LJ-1-398/Probe398.agda"]
  changed_files_none = ["agents/tasks/LJ-1-398/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 42
  error_class = "unsolved_meta"
  changed_files_any = ["agents/tasks/LJ-1-398/review-of-*.md"]

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

## YOUR ROLE (program-generated, do not edit)

**You write the Agda this brief names, and the probe it names (A21).** The mathematician specifies; you build it and make it typecheck. Your report is the other half of that channel, so write what the next brief will need.

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev/TASKS-archived.md, archive/dev/JOURNAL-archived.md, archive/dev/DECISIONS-archived.md, dev/ARCHIVE.md:
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 189.157)
- CANDIDATE dev/ARCHIVE.md  (score 150.004)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 134.018)
- CANDIDATE archive/dev/TASKS-archived.md  (score 111.105)
- CANDIDATE archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md  (score 65.645)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 63.307)
- CANDIDATE dev/literature/digest.md  (score 52.450)
- CANDIDATE dev/literature/devlin-II5.md  (score 51.127)
- CANDIDATE dev/literature/terms-2026-08.md  (score 46.989)
- CANDIDATE dev/literature/geology.md  (score 36.794)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
