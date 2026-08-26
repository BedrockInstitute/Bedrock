# LJ-1.656 report: the level formula, which is Devlin's own object

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.656
obligation: agents/tasks/LJ-1-656/Probe656.agda::level-formula
verdict: **NO-GO ON THE OBLIGATION. The stop is
`review-of-level-formula.md`. COMPONENT 1 OF 3 IS DELIVERED, the set half
of component 3 is delivered, and components 2 and 3 are REDUCED, with no
residue at the stage and none at the alphabet, to TWO ROWS AT THE CLASS
CARRIER.**

The obligation reads `missing` (`runs/meter-obligation.out`,
`1 UNRESOLVED of 1`, `probe_red=False`: the probes are green and the name
is absent, not broken). Twenty other names are green
(`runs/meter-names.out`, `0 UNRESOLVED of 20`).

**READ THESE FIVE SENTENCES BEFORE YOU QUEUE ANYTHING.**

1. **THE STAGE IS NOT THE PROBLEM AND NEITHER IS THE ALPHABET.**
   `level-formula-from-class` (`runs/Probe656B.agda`, section 6.5) delivers
   `LevelFormula` from two rows stated ENTIRELY at the class carrier. The
   passage between the stage's inner world and the class carrier is an
   EQUALITY of truth values, spent in both directions, costing nothing.
2. **THE SOUNDNESS ROW IS `[LJ-1.52]`'s, AND IT IS FOUR HUNDRED
   DISPATCHES OLD.** `[LJ-1.570]` named it "THE ONE SYNTACTIC ROW THAT IS
   NOT DELIVERED" (`agents/tasks/LJ-1-570/Probe570.agda:285-293`). Grep
   over `src/`: no `GraphAgree`, no `StepAgree`, no `ApproxAgree`, and
   `LevelHood0` has no consumer at all.
3. **AND IT CANNOT BE A FREE ROW.** `extAtB-junk` and `extAt-pins`
   (section 5, both green) measure the mechanism: the bounded extension
   frame pins its value only against the satisfiers that lie in `K`, the
   machine frame pins it against every satisfier there is. The tree
   states the price itself, as `extAtB→extAt`'s third argument
   (`src/L/Condensation.lagda.md:2514-2521`). **I did not prove the row
   false and this report claims no such thing** (section 5 below).
4. **THE BRIEF'S PREMISE 5 IS RIGHT, AND MEASUREMENT 1 IS WHY.** The
   delivered UNBOUNDED graph formula CARRIES CONSTANTS
   (`runs/COUNT-GRAPH.agda.txt`, `runs/floor-1.out`), so it does not
   erase, does not embed into `Code`, and cannot be this obligation's
   `lv`. `[LJ-1.651]`'s slot shape is the only route, and this probe
   takes it.
5. **LAW P-l WAS MEASURED THREE TIMES IN THIS TASK AND IT PAID EVERY
   TIME.** Section 6 below. One `subst` went from *killed at
   1,532,526,592 bytes after 229.22 s* to *4.86 s at 877,805,568 bytes*
   with no change to the mathematics.

Written as a skeleton before any Agda beyond the floor and filled as each
answer landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-656/`. Agda ran under the caliber the program set on
this pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier, ONE Agda process at a
time. I did not set `GHCRTS`. Nothing is postulated, every delivered file
carries `--safe`, no delivered file carries a hole, and nothing lands in
`src/`. The probes are raw `.agda` files, so they carry no ` ```agda `
fence, count 0 in-fence lines, and the ratio bar cannot fire on them.

**EVERY NUMBER BELOW IS MEASURED WITH A WARM `src/` INTERFACE CACHE**
(708 `.agdai` files under `_build/` at the start of the task, 713 at the
end). No number here is a cold-cache number, and this report does not
bound one.

## 1. WHAT IS DELIVERED

Every name is metered green in `runs/meter-names.out`.

| name | file | what it is | hypothesis |
|---|---|---|---|
| `lv` | A, `Frame` | **COMPONENT 1: the formula, `Formula Code 2`** | none |
| `lset-in-stage` | A, `Frame` | the stage holds the level of each of its ordinals | none |
| `levelOf`, `levelOf-fst` | A, `Frame` | that level, sealed, and its read | none |
| `Σ₁-step1` | A | the grade certificate | none |
| `ordAt1`, `Δ₀-ordAt1`, `ordAt1-out`, `ordAt1-in` | A | ordinality at slot 1, and its two readings | none |
| `Alphabet.toAmb`, `Alphabet.irrel` | A | one parameter-free formula, any alphabet, one meaning | none |
| `extAtB-junk`, `extAt-pins` | A | **the slack in the bounded frame, and its absence in the machine frame** | none |
| `level-formula-from-rows` | A, `Frame` | the assembly: two satisfaction rows give `LevelFormula` | 2 rows |
| `stage⊆L`, `toC`, `fst-toC` | B | the stage lies in `L` | none |
| `Δ₀-stage≡class` | B | **the Δ₀ passage, an EQUALITY** | none |
| `code≡id`, `peel-rot-gen`, `peel-rot` | B | the alphabet step and the rename step | none |
| `matrix-bridge`, `ord-bridge` | B | the two bridges, both equalities | none |
| `matrixDecode-from-tree` | B | the tree's own spelling reaches the row | none |
| `stage-sound-from-agree` | B | soundness at the stage | `MatrixDecode` |
| `complete-at`, `ord-at` | B | completeness at a VARIABLE value slot | none |
| `stage-complete-from-witness` | B | completeness at the stage | `ClassWitness` |
| `level-formula-from-class` | B | **THE HEADLINE: the obligation from two class rows** | both |

`Probe656.agda` is 405 lines, 162 non-blank non-comment.
`runs/Probe656B.agda` is 319 lines, 175 non-blank non-comment.

## 2. THE FLOOR, AND MEASUREMENT 1

**THE FLOOR IS CHEAP AND THE FRAME IS NOT THE PROBLEM.**
`runs/Floor656.agda`, `runs/floor-2.out`: exit 0 in 4.16 s at
712,982,528 bytes, `src/` imports only, the obligation's type restated
verbatim and nothing of its proof. `[LJ-1.650]`'s wall on cross-task
imports (`agents/tasks/LJ-1-650/lj-1.650-report.md:59-67`) did not recur,
because this probe imports no predecessor probe.

**MEASUREMENT 1, AND IT DECIDED THE SHAPE BEFORE ANY PROOF.** The first
floor asked whether the delivered UNBOUNDED graph formula carries a
constant. If it did not, it would erase to a parameter-free formula and
embed into `Code`, and `LevelFormula`'s alphabet would cost nothing.

**IT CARRIES CONSTANTS.** `runs/COUNT-GRAPH.agda.txt`,
`runs/floor-1.out`, exit 42 in 5.04 s at 775,405,568 bytes:
`countFo (LsetGraphAt zero (suc zero)) ≡ 0` fails, and Agda's own output
reduces the count to thirty-five explicit `suc`s and then STICKS on
unreduced `countFo` subterms whose printed trees name
`L.Coding.Graph.satGraphAt`, `L.Coding.Powerset.DefinesAt` and
`L.Coding.Model.extAt`. **So the erase route is shut for the machine
graph and only the SLOT machinery reaches `Formula Code 2`.** That is the
brief's premise 5, confirmed rather than assumed. The file is named
`.agda.txt` because it cannot typecheck, which is what the brief ordered.

## 3. W3, ANSWERED: THE COMPLETENESS HALF AT ORDINAL γ

The brief named the completeness half the widest unmeasured term and
priced it at 150 to 300 lines. **It SPLITS, and the two halves have
nothing to do with each other.**

**THE SET HALF IS FREE, AND CHEAPER THAN ANY ESTIMATE.**
`lset-in-stage` is 2 lines of proof. And it **does not spend `succλ`**:
the level of an ordinal `δ` of the stage is already at the stage indexed
by `δ` ITSELF, because a carrier is one of its own definable subsets
(`defSet⊤≡A`, `src/L/Definability.lagda.md:178`, reached through
`𝒟ₒ-intro`, `src/L/Constructible.lagda.md:301`). Successor closure was in
the telescope and this route does not use it.

**THE SATISFACTION HALF IS `ClassWitness`, AND THE STAGE IS NOT IN IT.**
After `matrix-bridge`, what completeness owes is: at each ordinal `γ` of
the stage, a bound `K` and a filler `u` **that are members of the stage**
and satisfy the bounded matrix, read at the CLASS carrier. `complete-at`
turns that into the obligation's own satisfaction and costs nothing.

**THE GRADE WALL DID NOT RECUR.** `[LJ-1.646]`'s wall was a grade wall
(2,287 unbounded `∃̇` interleaved with 2,159 unbounded `∀̇`,
`agents/tasks/LJ-1-646/lj-1.646-report.md:90-91`). Nothing in this task
met it: `Σ₁-step1` is the tree's own certificate and the formula is Σ₁
with a Δ₀ core, exactly as `[LJ-1.651]` measured. **The wall this task met
was a different one and section 6 is its measurement.**

## 4. WHAT `LevelFormula` ACTUALLY NEEDED THAT THE BRIEF DID NOT SAY

**THE SOUNDNESS HALF CARRIES NO ORDINALITY HYPOTHESIS**
(`agents/tasks/LJ-1-650/Probe650.agda:325`), and the tree's only
delivered landing demands one: `ride-only` takes
`IsOrd (fst (lookup b γ))` (`src/L/Condensation.lagda.md:422-425`).
**So on the route the tree delivers, the formula has to SAY it**, and
`lv` is two conjuncts and not one. `[LJ-1.651]`'s `lset-formula` is the
first conjunct alone, so it does not reach this obligation on that route
even if every row below were paid. **I did not measure whether some
other route proves soundness without the conjunct**, and this report
does not claim there is none.

The tree has `isOrdAt` at slot 0 of a one-slot environment
(`src/L/BoundedSubset.lagda.md:74-78`). Moving it to slot 1 of a two-slot
environment by `renameFo` needs a grade-preservation theorem for
`renameFo`, and **`[LJ-1.651]` already recorded that the tree carries
none** (its section 4's open note). So `ordAt1` is written out and its Δ₀
witness is the same four constructors. **That open note is now a
measured cost and not a note: it cost this task a restatement.**

## 5. WHAT I DID NOT PROVE

**I DID NOT PROVE `GraphAgree` FALSE.** Section 4 of
`review-of-level-formula.md` measures the MECHANISM by which the bounded
frame under-determines its value; that is not a refutation of the row.

**THE CHEAPEST EXPERIMENT THAT WOULD SETTLE IT**, named so the next brief
can price it rather than guess: exhibit a concrete `K` in `L` at which
every conjunct of `graphBndAt` holds with a value that is NOT
`Lset γ`. The conjuncts to discharge are `domB`
(`src/L/Condensation.lagda.md:1749-1756`), the two bounded universals of
`approxBndAt` (`:2471-2477`), and the outer `extAtB` of `stepBndAt`
(`:2417`), whose body `witB` bottoms out in `bodyB` (`:2404-2408`) whose
FIRST conjunct is a membership in the carrier slot. **That last fact is
what makes the experiment plausible without touching the code machinery
at all**, and it is where I would start. **This task did not attempt it
and does not bound its price.**

## 6. THE WALL THIS TASK MET, AND IT WAS NOT A GRADE WALL

**A SHARED-MACHINE RESOURCE FACT CAME FIRST, AND IT IS NOT A FACT ABOUT
ANY TERM.** Agda was killed by the operating system, EXIT=137 (SIGKILL),
repeatedly: `runs/p-13.out`, `runs/p-14.out`, `runs/p-15.out`,
`runs/pa-1.out`. At the time, `memory_pressure -Q` read **3 to 4 percent
system-wide free** and `omlx-server` held **15.7 GB** of the 64 GB box.
The floor (712,982,528 bytes) survived that pressure; a file at
862,765,056 bytes did not. **The repository's own gate already knows this
number**: `scripts/gate/check-omlx-quiet.py` refuses `make check` below
`free_memory_pct_for_extra`, 25 percent. `runs/retry.sh` is this task's
answer: it WAITS for that same 25 percent and then runs once. **This is
not rerunning the same code hoping for a different result: the code was
fixed and the RESOURCE was what changed.**

**AND THEN A REAL ONE, AND IT IS LAW P-l THREE TIMES.** Every kill below
happened at a peak of about 1.53 GB against a 2 GB caliber, and each cure
is a delivered law applied at its own site.

| # | what was transparent in a type | before | after |
|---|---|---|---|
| 1 | `LsetGraphAt`, named in `GraphAgree` and in `matrix-decode` | `runs/p-10.out` 442.52 s; `runs/p-13.out`, `runs/p-14.out` EXIT=137 | row restated one link lower, at the MATRIX (`MatrixDecode`) |
| 2 | `matrix₀`, the erased matrix | `runs/pb-2.out` 262.99 s at 985,792,512 bytes, killed | `opaque` + `matrix₀-inv` as the read |
| 3 | `levelOf`, a pair with a proof inside | `runs/pb-8.out` **229.22 s at 1,532,526,592 bytes, killed, for ONE `subst`** | value slot kept a VARIABLE in `complete-at` and `ord-at`; **`runs/pb-11.out` 4.86 s at 877,805,568 bytes** |

**CURE 3 IS THE ONE WORTH KEEPING, AND IT IS NOT THE ONE I TRIED FIRST.**
Sealing `levelOf` with `opaque` cut the TIME (229.22 s to 63.74 s,
`runs/pb-8.out` against `runs/pb-10.out`) and did NOT cut the peak: still
1,533,575,168 bytes, still killed. What cut the peak was keeping the
construction OUT of the lemma: `complete-at` takes the value slot as a
variable and is instantiated at `F.levelOf` in one application. **The
seal and the abstraction are two different cures and only the second one
paid.** The tree's `L.Coding.Sequence` law about named payloads
(`src/L/Coding/Sequence.lagda.md:143-145`) was applied too and, measured
alone, it also did not pay: `runs/pb-6.out`, 169.38 s at 1,545,125,888
bytes, killed.

**THE SPLIT INTO TWO FILES IS PART OF THE SAME RESTRUCTURING.** With
section 6 in one file the whole probe was killed; split, each half
elaborates in a smaller window and part A's interface survives a kill of
part B. The import is ONE link and inside the task home.

## 7. HEAP AND TIME, IN FULL

| run | file | exit | wall | peak bytes |
|---|---|---|---|---|
| `floor-1` | `runs/COUNT-GRAPH.agda.txt` | 42 (measurement 1) | 5.04 s | 775,405,568 |
| `floor-2` | `runs/Floor656.agda` | 0 | 4.16 s | 712,982,528 |
| `p-2` | `Probe656.agda` (sections 1-2) | 0 | 5.69 s | 648,019,968 |
| `p-4` | `Probe656.agda` (sections 1-5) | 0 | 7.58 s | 860,340,224 |
| `p-7` | `Probe656.agda` (parameter-free core) | 0 | 14.50 s | 851,001,344 |
| `p-9` | `Probe656.agda` (with section 6.4) | 0 | 118.65 s | 877,920,256 |
| `p-10` | `Probe656.agda` (with section 6.5) | 42 | 442.52 s | 908,361,728 |
| `p-13` | `Probe656.agda` (one file) | **137 SIGKILL** | - | - |
| `pa-4` | `Probe656.agda` (split, sealed) | 0 | 13.08 s | 862,765,056 |
| `pb-2` | `runs/Probe656B.agda` (graph in types) | killed by signal | 262.99 s | 985,792,512 |
| `pb-3` | `runs/Probe656B.agda` (row at the matrix) | killed by signal | 215.34 s | 1,536,720,896 |
| `pb-6` | `runs/Probe656B.agda` (payloads named) | killed by signal | 169.38 s | 1,545,125,888 |
| `pb-8` | `runs/Probe656B.agda` (`levelOf` sealed, one `subst`) | killed by signal | 229.22 s | 1,532,526,592 |
| `pb-10` | `runs/Probe656B.agda` (sealed, full) | killed by signal | 63.74 s | 1,533,575,168 |
| `pb-11` | `runs/Probe656B.agda` (**variable value slot**) | 0 | **4.86 s** | **877,805,568** |
| `final-Floor656` | `runs/Floor656.agda` | 0 | 3.28 s | 689,356,800 |
| `final-Probe656` | `Probe656.agda` | 0 | 14.22 s | 864,960,512 |
| `final-Probe656B` | `runs/Probe656B.agda` | 0 | 4.64 s | 876,773,376 |

**The highest peak of any GREEN run is 877,920,256 bytes, 41 % of the
2,147,483,648-byte wide cap.** No delivered term walls on its own heap.
The caps in `runs/run.sh` are wall-clock caps of 900 s enforced by a perl
alarm, because this macOS has no `timeout` (`[LJ-1.602]`, `[LJ-1.610]`);
no run came near one. **Every `.agda` file under this task home
typechecks** (`find` returns exactly three: `Probe656.agda`,
`runs/Probe656B.agda`, `runs/Floor656.agda`, and the final pass is green on
all three). The one file that cannot typecheck is named `.agda.txt`,
which is what the brief ordered and what `[LJ-1.636]` and `[LJ-1.643]`
each lost a return to.

## 8. W2, W4, AND THE WORKING TREE

**W2.** The generic-carrier rule is answered and it was answered in the
CHEAPEST direction available: the two lemmas that carry this task's
content, `Alphabet.toAmb` and `Δ₀-stage≡class`, are stated generically
(in the structure, in the alphabet, in the formula and in its arity) and
instantiated. Nothing is proved twice at two carriers. The one place a
predecessor's proof is restated rather than imported is `ordAt1`, and
section 4 gives the reason: the tree has no grade-preservation theorem
for `renameFo`.

**W4.** Nothing was retired and nothing was deleted. No `dev/ARCHIVE.md`
row is owed by this task.

**THE WORKING TREE**, exactly as the report describes it:

- `agents/tasks/LJ-1-656/Probe656.agda` - part A, green.
- `agents/tasks/LJ-1-656/runs/Probe656B.agda` - part B, green. **It is
  under `runs/` because the brief's write scope names
  `Probe656.agda` and `runs/` and no second top-level probe; part B is
  inside the directory the scope grants rather than outside the scope
  the brief declared.**
- `agents/tasks/LJ-1-656/lj-1.656-report.md` - this report.
- `agents/tasks/LJ-1-656/review-of-level-formula.md` - the stop.
- `agents/tasks/LJ-1-656/runs/` - every run, the floor, the failing
  measurement as `.agda.txt`, `run.sh` and `retry.sh`.
- No `src/` change. No file authored under `_build/` (the interface cache
  entries are Agda's own). Not committed, not pushed.

## 9. WHAT THE NEXT BRIEF NEEDS

**9.1 THE OBLIGATION IS NOW TWO ROWS AND BOTH ARE STATED IN THE TREE.**
`FrameB.MatrixDecode` and `FrameB.ClassWitness` (`runs/Probe656B.agda`). Both
are at the class carrier. Neither mentions the stage, the hull, the code
alphabet or `succλ`. Either is a task; neither is this one.

**9.2 `MatrixDecode` HAS A DELIVERED REDUCTION AND AN UNBUILT ONE.**
`matrixDecode-from-tree` reaches it from the tree's own spelling of the
matrix. From there, `[LJ-1.570]`'s `matrix-decode`
(`agents/tasks/LJ-1-570/Probe570.agda:300-322`) proves
`GraphAgree → MatrixDecode`, green, at today's tree. **So the whole
remaining soundness price is `GraphAgree`, and it is `[LJ-1.52]`'s.**

**9.3 AND C-42 APPLIES TO THIS ONE, NOT ONLY TO A REFUTATION.**
`[LJ-1.52]` left THREE rows as hypotheses, not one: `GraphAgree`,
`StepAgree` and `ApproxAgree`
(`agents/tasks/archive/LJ-1-52/ProbeLJ152B.agda:53-70`). Grep over `src/`
finds none of the three. **Before pricing a cure for `GraphAgree`, count
how many queued tasks rest on the other two.** This task did not do that
sweep and it is not this task's scope.

**9.4 THE ORDINALITY CONJUNCT IS ABOUT THE OBLIGATION'S TYPE, NOT ABOUT
MY SHAPE.** Soundness quantifies over every pair of stage members with no
hypothesis, and the tree's only delivered landing needs `IsOrd` at slot
1. So on that route `lv` carries it. A brief that asks for the level
formula and forgets this asks for a term that the delivered landing
cannot close.

**9.5 IF THE OWNER WANTS THE REFUTATION, IT IS A SEPARATE TASK.**
Section 5 names the experiment and the four conjuncts it must discharge.
It is a coder task, it lands in a task home, and it is not cheap.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: **NOT READ, DECLINED.** It is a
  dispatch index. This task's history is three predecessor task homes and
  one archived probe pair, and each is cited at the line it was read.
- `archive/dev/JOURNAL-archived.md`: **NOT READ, DECLINED.** Its
  level-hood material is `[LJ-1.646]`'s grade wall, and
  `agents/tasks/LJ-1-651/lj-1.651-report.md:202` already quotes the
  archived measurement in full, so section 3 above cites it through that
  quotation rather than reopening the archive.
- `archive/dev/JOURNAL.md`: **NOT READ, DECLINED.** Same reason: the live
  journal carries no history this task turns on, and a live document
  carries no history.
- `dev/ARCHIVE.md`: **DECLINED.** It is the register of retired modules.
  This task retires nothing (section 8), so it owes no row and reads none.
- `archive/dev/ORCHESTRATION.md`: **DECLINED.** The archived operating
  document, superseded by `dev/memos/LJ-4-pod-program-design.md`. Nothing
  in this task turns on how the loop is operated.

**AND ONE ARCHIVE PATH THE SEARCH DID NOT OFFER WAS READ, so it is named
here rather than left silent**: `agents/tasks/archive/LJ-1-52/`, both
`ProbeLJ152A.agda` and `ProbeLJ152B.agda`.
`agents/tasks/archive/LJ-1-52/ProbeLJ152A.agda:48` reads

> GraphAgree : Type (ℓ-suc ℓ)

and it is the row this task stops at.
`agents/tasks/archive/LJ-1-52/ProbeLJ152B.agda:53` reads

>   StepAgree : Type (ℓ-suc ℓ)

which is section 9.3's second unbuilt row.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: **READ.** At
  `dev/literature/devlin-II5.md:214` the line is

  > 1. Level-hood as Σ₁ with a Σ₀ matrix: there is a Σ₀ formula Φ(z, v, γ) of

  That is the shape `lv` takes, and the brief's premise 2 quotes the same
  line. It is why the formula is one Σ₁ closure over a Δ₀ core and why
  the closure's witnesses may be taken at the stage: Devlin's `z` is the
  bound and the filler, and both are members.
- `dev/literature/truncation-and-selection.md`: **NOT READ, DECLINED.**
  This task lifts no truncation: the one truncation it introduces
  (`ClassWitness`) it also consumes, through `PT.rec` at a proposition,
  and no selection principle enters.
- `dev/literature/digest.md`: **NOT READ, DECLINED.** It is the
  corpus-wide digest; `devlin-II5.md` is its II.5 chapter at full detail
  and is the only chapter this task's object comes from.
- `dev/literature/terms-2026-08.md`: **DECLINED.** It is a terminology
  file. This task adds no `dev/glossary.toml` entry and proposes none.
- `dev/literature/primary-sources.md`: **DECLINED.** It is the source
  register. The digest entry above carries the statement directly and no
  primary text had to be located.
