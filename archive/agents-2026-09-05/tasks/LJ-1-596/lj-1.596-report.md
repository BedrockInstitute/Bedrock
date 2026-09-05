# LJ-1.596 report: B9 through the internalization machine

## HEAD
head_slot: coder
machine: shared
verdict: NO-GO

obligation: agents/tasks/LJ-1-596/Probe596.agda::b9-inf (NOT INHABITED)
stop: agents/tasks/LJ-1-596/review-of-b9-inf.md

The report was written as a skeleton before any Agda and filled as each answer
landed (C-22, `dev/LESSONS.md:2299`). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-596/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M4g"` (`agents/tasks/LJ-1-596/runs/w3-1.out:2`), ONE
Agda process at a time, guarded by a PID file copied from `[LJ-1.593]`'s
harness (`agents/tasks/LJ-1-596/runs/run.sh:10-16`). I did not set `GHCRTS`.
Nothing is postulated, `--safe` is on, and the probe carries no hole, so every
reduction in it is a measurement and not a claim. Every file of this task is a
raw `.agda`, a `.sh` or a `.md`, so none carries an ` ```agda ` fence, all
count 0 in-fence lines, and the ratio bar cannot fire on them.

## VERDICT

**NO-GO on `b9-inf`, and `agents/tasks/LJ-1-596/review-of-b9-inf.md` states
it.** The probe is GREEN, EXIT 0, four cold runs (`runs/final-1.out`,
`runs/final-2.out`, `runs/final-3.out`, `runs/final-4.out`, the last
postdating every edit to every file of this task), and no term named `b9-inf`
is in it.
`B9Inf` is stated in the probe, copied letter for letter from
`agents/tasks/LJ-1-593/Probe593.agda:511-514`.

**THE NO-GO IS ABOUT THE MACHINE'S FIT AND NOT ABOUT THE OBJECT'S TRUTH.** The
machine, `src/L/Recursion.lagda.md`, does not apply to `stage-card-upper` as
the tree has it, for three measured reasons, and the conditional term in the
probe says exactly what input would make it apply. That input is a chapter of
`src/`, which `[LJ-1.594]` had already priced
(`agents/tasks/LJ-1-594/Probe594.agda:434-439`); this task adds the machine's
own interface to that price and a term that converts the chapter into `B9Inf`.

**ONE HEAP WALL WAS MET AND ROUTED IN THIS DISPATCH, NOT REPORTED AS A
FINDING.** Runs `p11`, `p12` and `p15` exhausted the 4 GB cap at 63 to 67 s.
The cause was found by bisection (`p14`, `p16`): a `with`-abstraction over a
decided membership unfolded the totalized function's normal form. The cure was
tested under the same cap: take the total function as the conditional's
hypothesis and factor the four conjuncts out of the record-carrying frame. The
final shape checks in 3.5 s and 769 MB (`runs/final-1.out`).

## D-10, BEFORE ANY AGDA, AND IT IS THE CHAPTER'S INTERFACE

**WHAT IT TAKES** (`Takes` and `takes-is-the-record`, probe section 0; the
fields at `src/L/Recursion.lagda.md:105-108`):

| field | site | what it is |
|---|---|---|
| `dom : S` | `src/L/Recursion.lagda.md:105` | the index set, an element of L |
| `graph : Formula S 2` | `src/L/Recursion.lagda.md:106` | the two-variable formula, value first, index second |
| `funct` | `src/L/Recursion.lagda.md:107-108` | single-valuedness, stated as contractibility |

The `Definition` record (`src/L/Recursion.lagda.md:272-279`) takes instead a
TOTAL function `fn : S → S` (`:275`), the formula (`:276`), and the two
adequacy implications `defines` (`:277`) and `only` (`:278-279`).

**WHAT IT GIVES** (`gives-table`, `gives-in`, probe section 0): `Of.table`
(`src/L/Recursion.lagda.md:179-180`), the replacement image, an element of L
by construction, with `table-in` (`:185-187`), `table-out` (`:189-190`) and
`val`/`val-uniq` (`:192-197`). `smallDom` (`:133-134`) discharges the domain
for any small family of elements of L. **THE ENGINE IS `hasReplacementL`**
(`:361`), and the chapter is a wrapper around it.

**DOES `stage-card-upper`'s RECURSION FIT IT?** No, as the tree has it. The
three mismatches are rows of the probe and of the slice, each at `file:line`:

1. **The value is function-valued.** `P` (`src/L/StageCardinal.lagda.md:530-532`)
   returns an injection between fibers; the machine consumes S-valued
   functions. The `refl` row is W3's `P-is-function-valued`.
2. **The graph does not state.** See `## W3` below.
3. **The data does not reach the machine.** `stage-card-upper` needs the
   square-law family as module data (`src/L/StageCardinal.lagda.md:17-20`),
   reached only through `SqCollect`, marked "Not inhabited"
   (`src/L/StageBound.lagda.md:42`). `B9Inf`'s three hypotheses supply the
   truncated square only, and `[LJ-1.592]` already measured that the
   propositional-motive induction dissolves the collection while leaving the
   code open (`agents/tasks/LJ-1-592/Probe592.agda:275-279`).

## DID THE MACHINE FIT

**NO, AND THE PROBE SAYS PRECISELY WHAT HAD TO BE SUPPLIED.**

- The chapter's prose sentence (`src/L/Recursion.lagda.md:259-262`) was tested
  against the record's own fields. **The second half of the sentence is TRUE
  as stated**: no field of either record mentions the recursion's shape,
  depth, order of descent or clause complexity. **The first half says less
  than the type demands**: "expressible" is not a property the type checks;
  the record demands a formula AND `defines` AND `only`
  (`src/L/Recursion.lagda.md:277-279`), and adequacy in both directions is
  the mathematics itself. `Condition` and `condition-is-the-record` (probe
  section 1) are the re-ascription.
- At a fixed stage the machine's slot DOES fill, from abstract adequacy: W3's
  `module Elem.Given` hands the actual `Recursion` and `Definition` records a
  formula parameter plus its adequacy, and the machine runs. **What no
  chapter of this tree supplies is the formula.** The two ingredients of the
  graph's class predicate that the object language cannot name are W3's
  `Ingredients` rows: the meta syntax `Formula ⟪ Lset (⟪ α ⟫↪ m) ⟫ 1`
  (`src/L/StageCardinal.lagda.md:281-282`) and the count `cnt` through `ih`
  (`:288-289`, `:283`), which is the recursion's own value at a member.
- **The tree has two internalized recursions and they are the precedent and
  the price.** `satGraph` (`src/L/Coding/Graph.lagda.md:238`) internalized
  the satisfaction recursion, adequate through `L.Coding.Uniform`'s `exists`
  and `unique`. `LsetGraph` (`src/L/Coding/Sequence.lagda.md:353`)
  internalized the tower, adequate through `L.Hierarchy`'s `Lset-defines` and
  `Lset-only`. Both steps read their argument through the satisfaction
  machinery alone. `stage-card-upper`'s step does not: `class-pred`
  (`src/L/StageCardinal.lagda.md:319-324`) re-reads the system being built
  through `cnt`, which counts formula constants through the branch injection.
  That is why the missing graph is a chapter.

## WHAT THIS PAYS

**NOTHING IS DISCHARGED.** No row of the campaign's bill is paid by this task.
What the probe adds is one conditional, and its hypotheses are exactly the two
missing inputs:

- `Machine.pays-input` (probe section 3): at a GENERIC carrier `(a b : S)`
  (clause W2), given an ambient injection `g` and `Machine.Input` (a total
  function that pair-codes `g` on the domain, and a `Formula S 2` adequate to
  it in both directions), the machine's table IS an `InjCode`, all four
  conjuncts of `src/L/Cardinal.lagda.md:223-228`.
- `b9inf-given-graph` (probe section 3.4): the same, instantiated at the
  bill's own pair `(LsetS (fst δ) ordδ , δ)`, with the transport to `Lδ` along
  `fst Lδ ≡ Lset (fst δ)`.

**WHOEVER SUPPLIES `Machine.Input` AND THE AMBIENT INJECTION GETS `B9Inf`
FROM THIS FILE'S OWN TERM**, and with it, by `[LJ-1.593]`'s corollary
(`square-from-b9inf`, `agents/tasks/LJ-1-593/Probe593.agda:521-530`), the
coded square law. The function half of `Machine.Input` is constructible from
LEM alone (W3's `Elem.fn`); **the formula half is the chapter
`[LJ-1.594]` priced and no probe can write it.**

## W3, THE WIDEST UNMEASURED TERM

**THE GRAPH WAS WRITTEN FIRST AND TYPECHECKED ALONE**, as the brief ordered:
`agents/tasks/LJ-1-596/runs/W3.agda`, GREEN on `runs/w3-11.out` (2.76 s, 799
MB), and GREEN again after the citation edits on `runs/final-w3-2.out` (3.09
s). The chain behind it compiled once, in `runs/w3-3.out` (18.49 s, 2,083 MB).

**THE ANSWER IS: THE GRAPH STATES AS A TYPE AND NOT AS A TERM.** The slice
carries: `step` and `stage-card-upper` TYPE ONLY under the tower as abstract
data (`module Tower`, no conversion problem; `[LJ-1.584]` measured the one
this avoids, `agents/tasks/LJ-1-584/runs/w3b-1.out`); the `refl` that `P` is
function-valued; the element-level function `Elem.fn`; its adequacy
`Elem.Adequate`; the actual records of `src/L/Recursion.lagda.md` instantiated
from abstract adequacy (`Elem.Given`); and the two unnamable ingredients
(`Ingredients.F-at`, `Ingredients.CntShape`, `Ingredients.ClassPredShape`).

The brief estimated about 15 lines and under 2 minutes. Measured: 231 lines
(about 100 of them comment), 11 runs to green, of which one was the chain
compile at 18.49 s. **The estimate was for a formula that does not exist; the
slice's deliverable was the measurement that it does not.**

## PRICES

**CALIBER.** `GHCRTS="-A64m -I0 -M4g"`, set by the program on this pane and
not by me. ONE Agda process at a time. **THE HEAP WALLS AND THE CURE:**
`p11`, `p12`, `p15` exhausted the 4 GB cap at 63 to 67 s; bisection (`p14`:
sections 0-2 and 4 alone GREEN at 2.87 s; `p16`: the function frame alone
GREEN at 3.20 s) located the cause in a `with`-abstraction over decided
membership that unfolded the totalized function's normal form. The restructure
(function and adequacy as the conditional's hypothesis; four conjuncts
factored out of the record-carrying frame) was tested under the same cap and
checks in 3.5 s. **No number below was measured under any other caliber.**

| run | what | wall s | max RSS | exit |
|---|---|---|---|---|
| `w3-1` | W3, first attempt | 1.20 | 244 MB | 42 |
| `w3-3` | W3, chain compile (`L.StageBound` etc.) | 18.49 | 2,083 MB | 42 |
| `w3-11` | W3 GREEN | 2.76 | 799 MB | 0 |
| `final-w3-2` | W3 GREEN, cold, post-citation-edit | 3.09 | 799 MB | 0 |
| `p11` | probe, first complete shape | 65.09 | 4,676 MB | **251** |
| `p12` | probe, conjuncts factored, `with` kept | 62.90 | 4,531 MB | **251** |
| `p14` | probe, sections 0-2 and 4 only (floor) | 2.87 | 779 MB | 0 |
| `p15` | probe, function frame with `with` | 67.00 | 4,531 MB | **251** |
| `p16` | probe, function frame without the proofs | 3.20 | 821 MB | 0 |
| `p17`-`p32` | fix iterations (orientation of six paths) | 2.7-3.7 | about 769 MB | 42 |
| `p33` | probe GREEN, complete | 3.94 | 769 MB | 0 |
| `final-1` | probe GREEN, cold for this file | 3.55 | 769 MB | 0 |
| `final-2` | probe GREEN, cold for this file | 3.57 | 769 MB | 0 |
| `final-3` | probe GREEN, cold, post-citation-edit | 3.49 | 769 MB | 0 |
| `final-4` | probe GREEN, cold, postdates every edit | 3.94 | 769 MB | 0 |

**ESTIMATE AGAINST MEASURED.** The brief estimated about 220 lines in the
probe, of which the obligation about 55, and called the estimate the least
certain in the queue.

| | lines | of which the obligation |
|---|---|---|
| estimate | 220 | 55 |
| measured | 440 (+231 in W3) | 0 (not inhabited) |

The overrun is the conditional and the interface rows. The brief's plan was
one term; the deliverable that informs the next brief is the machine's
interface, the re-ascription, the three mismatch rows and the conditional,
and those are the 440 lines. The obligation itself cost 0 lines because it is
not inhabited, and the statement plus its narrowing relation cost 13.

## WHAT THE NEXT BRIEF NEEDS

1. **THE RULING THE BRIEF ANTICIPATED IS NOW BEFORE THE OWNER.** This is the
   fourth measured failure on this object. Three of the four say the same
   thing: the missing input is a CODE, and the tree builds codes in exactly
   three ways (`[LJ-1.592]`'s count). The fourth (this one) adds: the
   internalization machine converts ONE missing chapter into `B9Inf`, by the
   probe's own term. The chapter is `[LJ-1.594]`'s "one `Formula` with its
   `defines` and its `only`", now with the machine's interface priced and the
   two-input conditional written.
2. **IF THE OWNER FUNDS THE CHAPTER, THE NEXT BRIEF NEEDS ITS FRAME.**
   Devlin's engine is the level-recursion formula `E(f, α)` with the bound set
   `K(u)`, "the finite sequences over formulas, variables and members of u"
   (`dev/literature/devlin-II5.md:337-347`, item 7). `[LJ-1.86]`'s warning
   stands: the stage containing `AllCodes A` exists and the proof cannot
   choose it, because `lam` is a module parameter at every frame
   (`archive/dev/LJ-dispatch-index.md:160`).
3. **THE ALTERNATIVE ROUTE IS STILL `[LJ-1.592]`'s.** `CodedStep` paid by `W`
   closes the same row; `W` is at most `V = L` and `[LJ-1.591]` measured that
   row 2 buys row 5 with it. The owner's choice is between the chapter (true,
   priced, unstarted) and `W`/row 2 (a bill row, hypothesis-shaped).
4. **A MEASURED ELABORATION LAW, FOR WHOEVER WRITES THE CHAPTER.** A
   `with`-abstraction over a decided membership, in a type that mentions a
   function defined by case on that same decision, unfolds the function's
   normal form and walls at 4 GB in this frame. The cure that measured at
   3.5 s: take the function as a hypothesis and never abstract over its
   scrutinee.

## ARCHIVE USED

Every CANDIDATE the brief listed is named.

- **`archive/dev/LJ-dispatch-index.md`**: READ and USED. `:160` says "| LJ-1.86
  | Is there a stage containing AllCodes A | EXISTS; proof cannot choose it |
  AllCodes-stage is green. But lam is a module parameter at every frame, so
  the obligation moves to the frame |". It is the frame warning in `## WHAT
  THE NEXT BRIEF NEEDS` item 2, and it is why this task did not price the
  chapter's frame itself.
- **`archive/dev/JOURNAL.md`**: READ and USED. `:940-941` say
  "`src/L/StageCardinal.lagda.md:15-19` both demand an injective
  `⟪δ⟫ × ⟪δ⟫ → ⟪δ⟫` and nothing more. The obligation is an INJECTION and not an"
  (object-language arithmetic). It is the law behind this report's mismatch 3:
  the machine would need the square as DATA, and the obligation is not an
  arithmetic the truncated square can pay.
- **`archive/dev/JOURNAL-archived.md`**: NOT USED, declined. Not read past a
  `grep` for "square". It is the closed narrative record of the retired
  route; a live document carries no history and nothing in it can settle a
  type question at today's tree.
- **`archive/dev/DECISIONS-archived.md`**: NOT USED, declined. Its `D<n>`
  series is the archived decision series and binds nothing today.
- **`dev/ARCHIVE.md`**: NOT USED, declined. I retired no module, so clause W4
  gives me no row to write there.

## LITERATURE USED

Every CANDIDATE the brief listed is named.

- **`dev/literature/devlin-II5.md`**: READ and USED. `:337-338` say "the
  Σ₀ matrix C(w, v, u) and the bound set K(u), the finite sequences over
  formulas, variables and members of u", and `:340-342` name "E(f, α), the
  level-recursion formula". This is the classical shape of the chapter that
  would reopen B9, and it is cited in the review's reopener and in this
  report's next-brief item 2.
- **`dev/literature/truncation-and-selection.md`**: READ and USED. `:83` says
  "So a proof that only needs cardinal arithmetic never needs an injection as"
  data, and `:148` says "index is a proposition. **A data payload does not
  come out.**". Both are the law behind mismatch 3: the truncated square
  cannot yield the `SqFam` the machine's route would need, and no
  untruncation is licensed here.
- **`dev/literature/terms-2026-08.md`**: NOT USED, declined. It is the
  terminology dossier; this task names nothing new and the Boundary forbids
  me to add a glossary entry.
- **`dev/literature/digest.md`**: NOT USED, declined. Its Gandy-Jensen against
  Devlin-Basic split does not touch the machine's interface or the graph's
  ingredients.
- **`dev/literature/geology.md`**: NOT USED, declined. It is a geology dossier
  for `[L3.32-T12]` and is not about the level-size theorem.

## WHAT WAS NOT DONE

No term named `b9-inf` exists in any file of this task. I did not fund or
attempt the square law (`[LJ-1.593]` forbids it,
`agents/tasks/LJ-1-593/review-of-square-coded.md:82`). I did not attempt "any
coded injection" (`[LJ-1.592]` measured that the count is three). I did not
assert B9 or B9Inf; both are stated, and `b9-pays-b9inf` restates
`[LJ-1.593]`'s narrowing so the relation between the rows is a term of this
file. I did not edit `src/`, did not land anything there, did not postulate,
did not set `GHCRTS`, did not run `make check` (I committed nothing and
touched no file the check reads), did not commit and did not push.
