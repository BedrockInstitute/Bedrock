# LJ-1.395: the band recursion, and the one residue it leaves

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build TWO terms in `agents/tasks/LJ-1-395/Probe395.agda`, at a GENERIC band.

    band-owes : Type (ℓ-suc ℓ)

    sq-band : band-owes
            → (α : V ℓ) → IsOrd α → ⟨ α ∈ sucV α₀ ⟩ → (⟨ α ∈ ω ⟩ → Empty.⊥)
            → sq α

`sq-band` is the recursion the whole campaign is aiming at. It discharges
`L.StageCardinal`'s module parameter exactly
(`src/L/StageCardinal.lagda.md:17-20`), so its type must match that parameter and
not merely resemble it. **Check that match and say in the report that you checked
it.**

`band-owes` is a type YOU write. It names what the recursion still owes after
the three cases are spent.

**THE THREE CASES, AND EACH ONE HAS A NAMED SUPPLIER.** Recurse by `∈-induction`
(`src/V/Hierarchy.lagda.md:177-180`). At an infinite band ordinal `α`, split by
`lem` on `AmbCard α`, which is a proposition because it is a function into
`Empty.⊥`.

| the case | the supplier |
|---|---|
| `α ≡ ω` | `squareω`, delivered (`src/L/InjChain.lagda.md:184-185`) |
| `AmbCard α` holds | `[LJ-1.393]`'s `amb-init`, then `via-col-square` |
| `AmbCard α` fails | `[LJ-1.394]`'s `not-ambcard-gives`, then `descent-amb` |

**TAKE EVERY SUPPLIER AS A HYPOTHESIS OF YOUR OWN MODULE.** Do not import the
earlier probes and do not copy their proofs. Take the STATEMENT of each as a
parameter, with the type its report gives, and assemble. **That is what makes
this task cheap and separately checkable.**

**THREE CLAUSES BIND `band-owes`, AND THEY EXIST TO STOP ONE GAME.** A residue
type that holds the conclusion makes `sq-band` vacuous and measures nothing.
These are `[LJ-1.390]`'s three clauses, restated because they bind here too.

1. **It is CLOSED.** It takes no parameter from `sq-band`'s telescope.
2. **It never applies `sq` to a variable that `sq-band` binds.**
3. **The report gives ONE line that says why it is not the conclusion in
   disguise.**

**If `sq-band` cannot be built, state the obstruction at `file:line` and stop.
Both answers discharge this task.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-395/Probe395.agda::band-owes",
               "agents/tasks/LJ-1-395/Probe395.agda::sq-band"]

## SCOPE (write)
- agents/tasks/LJ-1-395/Probe395.agda
- agents/tasks/LJ-1-395/lj-1.395-report.md

## PREMISES
- The consumer takes `sq` as a MODULE PARAMETER quantified over every `δ` with `δ ∈ sucV α₀` and `δ ∉ ω`, and it carries no cardinality hypothesis. Basis: src/L/StageCardinal.lagda.md:17-20
- The parameter is applied at exactly one place inside the chapter. Basis: src/L/StageCardinal.lagda.md:283
- `∈-induction` is delivered and needs no new well-foundedness. Basis: src/V/Hierarchy.lagda.md:177-180
- `squareω` supplies the base case and needs no route. Basis: src/L/InjChain.lagda.md:184-185
- `via-col-square` turns `Init α` into `sq α`. Basis: src/L/Ordinal/SquareLaw.lagda.md:960-961
- `[LJ-1.390]` already built this recursion's shell with a different residue, by the same `∈-induction`. Basis: agents/tasks/LJ-1-390/Probe390.agda:180-219
- `[LJ-1.337]` built the same recursion earlier still, and its open branch was the ordinal that is closed and not `Init`. Basis: agents/tasks/LJ-1-337/lj-1.337-report.md:262-263
- `lem` is stated at `ℓ-suc ℓ`, which is the level `AmbCard` lives at. Basis: src/L/StageCardinal.lagda.md:15
- `ord-tri` gives the ordinal trichotomy the `α ≡ ω` split needs. Basis: src/L/Ordinal/Linear.lagda.md:136
- `mem-ord` gives the ordinal certificate at a member, which the recursion needs at every step. Basis: src/L/Ordinal.lagda.md:221-222
- `suc-ord` carries the band membership down to a member. Basis: src/L/StageCardinal.lagda.md:545-546
- `∈-irrefl`. Basis: src/V/Hierarchy.lagda.md:155
- `sq`. Basis: src/L/Ordinal/SquareLaw.lagda.md:685-687
- `_↪_`. Basis: src/L/Cardinal.lagda.md:47-48
- THE ARCHIVED ROUTE LISTED WHAT REMAINED BEFORE ITS COUNTING COULD RUN, and the list is this recursion's three cases in the archived vocabulary. Basis: agents/tasks/archive/L3-32-T47/l3.32-t47-report.md:135-158
- The archived route reached its counting at `κ+`, the tower stages and the cardinals below them, and said the consumer must verify the three `Init` clauses or restate its cardinal notion with them. Basis: agents/tasks/archive/L3-32-T47/l3.32-t47-report.md:137-142

## WHAT IS DELIVERED ALREADY
- The consumer's exact parameter type: src/L/StageCardinal.lagda.md:17-20
- The recursion shell, twice built, with two different residues: agents/tasks/LJ-1-390/Probe390.agda:180-219, agents/tasks/LJ-1-337/ProbeLJ1337B.agda:203-204
- `squareω`: src/L/InjChain.lagda.md:184-185
- `via-col-square`: src/L/Ordinal/SquareLaw.lagda.md:960-961
- `∈-induction`: src/V/Hierarchy.lagda.md:177-180
- `ord-tri`: src/L/Ordinal/Linear.lagda.md:136
- `mem-ord`: src/L/Ordinal.lagda.md:221-222
- The band-membership descent the recursion needs: src/L/StageCardinal.lagda.md:543-546
- A probe header that already opens most of these: agents/tasks/LJ-1-390/Probe390.agda:29-50

## WHAT IS MISSING

**THE RECURSION HAS BEEN BUILT TWICE AND BOTH TIMES ITS RESIDUE WAS TOO BIG.**
`[LJ-1.337]` built it and left the branch「δ closed and not `Init δ`」open
(`agents/tasks/LJ-1-337/lj-1.337-report.md:262-263`). `[LJ-1.390]` built it and
left a three-way disjunction whose second disjunct is `Init` at every internal
cardinal (`agents/tasks/LJ-1-390/lj-1.390-report.md:82-95`). **Neither residue
had a supplier.**

**THE ARCHIVED ROUTE LEFT THE SAME LIST AND CALLED IT「what remains before the
counting can run」** (`agents/tasks/archive/L3-32-T47/l3.32-t47-report.md:135-158`).
Its four items are this recursion's cases in the archived vocabulary:
`Init` at the counting's ordinals, the transfer at the non-initial sites, the
re-pointing, and the untruncated transfer that stayed blocked. **Read that
section. It is the closest thing this project has to a map of this task**, and
the second item is `[LJ-1.394]`.

**WHAT IS NEW IS THAT EVERY CASE NOW HAS A NAMED SUPPLIER.** `[LJ-1.393]`
supplies the `AmbCard` case and `[LJ-1.394]` supplies its negation. **So this
task is the first time the recursion is assembled with all three cases fed, and
the size of what is LEFT is the measurement.**

**WHAT IS STILL MISSING AFTER THIS TASK, STATED IN ADVANCE SO THE REPORT CANNOT
HIDE IT.** `AmbCard` has no producer, exactly as `Init` had none before
`[LJ-1.393]`. **The recursion does not need one**, because the case split is by
`lem` and not by a witness. **But `[LJ-1.394]`'s negative side may not deliver
data**, and if it does not, `band-owes` carries that gap and this report must
name it as the campaign's next bill.

## THE REASONING

**ASSEMBLE, DO NOT REPROVE.** Every case has a supplier and each supplier is a
hypothesis of your module. If you find yourself proving `Init`, proving
`suc-absorb` or building an injection out of a numeral, stop: you are rebuilding
`[LJ-1.392]` or `[LJ-1.393]` and this task does not pay for that.

**THE RECURSION'S MOTIVE IS WHERE THIS GOES WRONG, AND IT HAS GONE WRONG TWICE.**
The motive must carry the band membership and the infinitude down to every
member, or the induction hypothesis is unusable at the descent step.
`[LJ-1.390]`'s `Goal` and `descent-step` show one motive that works
(`agents/tasks/LJ-1-390/Probe390.agda:180-204`), and the chapter's own `P` shows
another (`src/L/StageCardinal.lagda.md:530-533`). **Read both before you write
yours.**

**THE `α ≡ ω` CASE IS NOT AUTOMATIC.** `squareω` is stated at `ω` and the
recursion holds an arbitrary infinite band ordinal. `ord-tri` on `α` and `ω`
gives three branches and `α ∈ ω` is refuted by the infinitude hypothesis. **The
chapter already does exactly this split** at
`src/L/StageCardinal.lagda.md:543-546`, and reading those four lines is cheaper
than deriving it again.

**THE `AmbCard` SPLIT IS BY `lem` AND THAT IS SOUND HERE.** `AmbCard α` is a
function into `Empty.⊥`, so it is a proposition, and `lem` at `ℓ-suc ℓ`
(`src/L/StageCardinal.lagda.md:15`) decides it. **This is the one place in the
route where a classical step is both needed and clean. Say so in the report**,
because a reader who does not see it will suspect the split is the whole
difficulty, and it is not.

**W2 AND DD4.** The recursion is generic in the band and in `α₀`. Nothing here
may name a site. `[LJ-1.386]` measured that nothing in this tree certifies
`+ω ω` as a band ordinal
(`agents/tasks/LJ-1-386/lj-1.386-report.md:211-236`), so a fixed site would
inherit that doubt for nothing.

**W3, THE WIDEST UNMEASURED TERM AND ITS PROBE.** The widest unmeasured term is
**the motive**: whether one `∈-induction` motive carries the band membership,
the infinitude and the ordinal certificate to every member without a transport.
**The probe is the motive alone**: write `band-owes` and the motive, get the
induction to typecheck with every case as a hole, and report that before you
fill any case. **The estimate is about 40 code lines for the two terms together,
on the basis of a delivered comparable of SHAPE: `Goal`, `descent-step`,
`band-ord` and `descent-closes` are 33 code lines for the same shell**
(`agents/tasks/LJ-1-390/Probe390.agda:180-219`). **It is not a comparable of
size**, because that shell had one case and this one has three. **Do not fund
anything against 40.**

**WRITE THE REPORT FIRST AND FILL IT AS YOU GO** (C-22). Run the probe while
this task is live. Nothing typechecks it after the task closes.

**REPORT THE NUMBER YOU MEASURED.** Give the wall seconds at the caliber the
program set on your pane, as the median of three consecutive runs, and give the
empty-module floor on the same machine on the same day.

## WHAT GO AND NO-GO EACH EARN

**A GO earns the square law at every band ordinal, conditional on `band-owes`,
and it earns the exact size of `band-owes`.** If `band-owes` turns out empty,
this closes `L.StageCardinal`'s module parameter and the largest open item on
the GCH route.

**A NO-GO earns the obstruction in the assembly, named at `file:line`.** An
assembly that fails when every case has a supplier is a statement about the
motive or about a mismatch between two suppliers' types, and either is worth
knowing before more suppliers are built. **A stated NO-GO is a full return and
not a failure.**

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
  changed_files_any = ["agents/tasks/LJ-1-395/Probe395.agda"]
  changed_files_none = ["agents/tasks/LJ-1-395/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 42
  error_class = "unsolved_meta"
  changed_files_any = ["agents/tasks/LJ-1-395/review-of-*.md"]

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

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev/TASKS-archived.md, archive/dev/JOURNAL-archived.md, archive/dev/DECISIONS-archived.md, dev/ARCHIVE.md:
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 186.952)
- CANDIDATE dev/ARCHIVE.md  (score 146.424)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 140.907)
- CANDIDATE archive/dev/TASKS-archived.md  (score 112.423)
- CANDIDATE archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md  (score 59.214)

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 49.101)
- CANDIDATE dev/literature/devlin-II5.md  (score 47.809)
- CANDIDATE dev/literature/digest.md  (score 44.696)
- CANDIDATE dev/literature/terms-2026-08.md  (score 35.008)
- CANDIDATE dev/literature/geology.md  (score 30.855)
