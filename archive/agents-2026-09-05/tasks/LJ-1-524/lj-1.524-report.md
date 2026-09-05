# LJ-1.524 report: `svAt`, the first conjunct, with `Q` determined

## HEAD
head_slot: coder
machine: shared
verdict: GO

## VERDICT

**GO. `svAt-at-carve` is built, with no holes.**
`agents/tasks/LJ-1-524/Probe524.agda:263-266`, exit 0, caliber
`-A64m -I0 -M8g` taken from the pane, one Agda process at a time.
`runs/full-1.out` to `runs/full-3.out`.

    svAt-at-carve :
        (a : S) (oa : IsOrd (fst a)) (bnd : S)
      → SvAtOf (Carve.G a oa bnd) a
    svAt-at-carve = Carve.thm

with `SvAtOf F a = ⟨ (F ∷ a ∷ []) ⊨ svAt zero ⟩` (`Probe524.agda:151-152`)
and `Carve.G a oa bnd = fst (rank-graph (ordQ a oa) a bnd)`
(`Probe524.agda:193-194`), `ordQ a oa = P521.ord-set-witness a oa .fst`
(`Probe524.agda:106-107`).

**THE TYPE IS `InjCode`'s FIRST CONJUNCT AND THE FILE PROVES IT IS.**
`svAt-is-first-of-InjCode` (`Probe524.agda:154-155`) is
`(F a b : S) → InjCode F a b → SvAtOf F a`, inhabited by `fst`. That
typechecks only if `SvAtOf F a` is definitionally the first component of
`InjCode F a b` (`src/L/Cardinal.lagda.md:225`). So the obligation cannot
have drifted from the conjunct.

**`Q` IS DETERMINED AND NOT HYPOTHESISED.** The telescope is
`(a , oa , bnd)`. No `ord-reads-Q` argument survives, and no `Q` argument
survives. The ruling holds.

**NOTHING IS POSTULATED. NOTHING LANDED IN `src/`. `swo-rank` IS NOT
RESTORED. `rankFo-adequate′` IS NOT REBUILT. The other three conjuncts
are NOT attempted.**

I did not write a `review-of-*.md`, because this is not a stop.

## ONE DEPARTURE FROM THE PREDECESSORS' PRACTICE, DECLARED

**THIS PROBE IMPORTS A PREDECESSOR PROBE**, `LJ-1-521.Probe521`
(`Probe524.agda:70`). Five predecessor reports state as a fact that "a
probe does not import a probe"
(`agents/tasks/LJ-1-507/lj-1.507-report.md:384`,
`agents/tasks/LJ-1-518/lj-1.518-report.md:214`,
`agents/tasks/LJ-1-520/lj-1.520-report.md:420`,
`agents/tasks/LJ-1-521/lj-1.521-report.md:178`, and again at `:425`).

**I SEARCHED FOR THE RULE THAT SAYS SO AND FOUND NONE.** `grep` over
`AGENTS.md`, `dev/pod/instructions/coder.md`, `dev/LESSONS.md`,
`dev/pod/rulings.toml` and `agents/README.md` returns no such clause. What
`agents/README.md` does carry is the REASON behind the habit, and it is a
real one: "**Nothing typechecks your probe once your task closes.**"
(`agents/README.md:92`). An import makes this file depend on a frozen
record.

**THE TREE ALREADY CARRIES CROSS-TASK PROBE IMPORTS.**
`agents/tasks/LJ-1-184/ProbeLJ1184C.agda:29` imports
`LJ-1-178.ProbeLJ1178A`; `agents/tasks/LJ-1-224/ProbeGraphSupply.agda:24`
imports `LJ-1-210.GenModel`. `bedrock.agda-lib:2` makes it legal:
`include: src agents/tasks`.

**THE BRIEF FORCED THE CHOICE AND I SAY SO PLAINLY.** It orders "DO NOT
REBUILD `rankFo-adequate′`" and prices the whole task at about 200 lines,
"of which the obligation is about 50 and the rest is the rebuilt carve and
adequacy". `[LJ-1.521]` measured that adequacy at 1176 lines
(`agents/tasks/LJ-1-521/lj-1.521-report.md:287`). **A 150-line rebuild of a
1176-line proof does not exist.** The two instructions are consistent only
under an import, so I imported, and `Probe521.agda` is committed and clean
in this worktree (`git log -1 -- agents/tasks/LJ-1-521/Probe521.agda` is
`24f4b7fe`).

**WHAT THE IMPORT COSTS, MEASURED.** With `Probe521.agdai` warm the file is
12.20 s median; with it deleted as well, 15.66 s (`runs/full-with-import.out`,
exit 0). So the import is about 3.5 s, and a rebuild would have been the
whole 1176 lines instead.

**If the critic rules that the habit is a rule, the cure is a re-dispatch
that rebuilds the adequacy, and it should be priced at `[LJ-1.521]`'s 1176
lines and not at this brief's 200.**

## D-10, BEFORE ANY AGDA

**THE BRIEF ORDERED ONE CHECK: do the four steps compose end to end. THEY
DO, AND NO ADAPTER IS NEEDED.** I checked each at its `file:line` before
writing Agda.

| step | at | output | consumed by |
|---|---|---|---|
| enter the carve | `src/L/Coding/Model.lagda.md:329-330` | `fst (prʟ x y) ≡ pr (fst x) (fst y)` | `rank-graph-out` |
| `rank-graph-out` | `agents/tasks/LJ-1-490/Probe490.agda:111-116` | `⟨ z ∈ˢ bnd ⟩ × ⟨ (z ∷ []) ⊨ rankFo Q a ⟩` | `rankFo-adequate′` |
| `rankFo-adequate′` | `agents/tasks/LJ-1-521/Probe521.agda:1006-1011` | `Σ[ m ] Σ[ mx ] (fst z ≡ pr (fst m) (fst (rank-at′ a oa m mx)))` | `pr-inj` |
| `pr-inj` | `src/V/Coding.lagda.md:178-179` | `(fst x ≡ fst m) × (fst y ≡ fst (rank-at′ …))` | `↾-reflects` |
| `↾-reflects` | `src/FOL/ZFStructure.lagda.md:164-167` | `m ≡ m'` | `rank-at′-irr` |

**ONE STEP THE BRIEF DID NOT NAME, AND IT IS NOT AN ADAPTER.** `↾-reflects`
gives `m ≡ m'`; the conclusion needs
`fst (rank-at′ a oa m mx) ≡ fst (rank-at′ a oa m' mx')`. Transporting the
first to the second is `rank-at′-irr` (`Probe524.agda:128-145`), and it is
NOT a fifth step nobody priced: the brief's own list ends at "`isPropTgt`
is exactly this argument, already written"
(`agents/tasks/LJ-1-521/lj-1.521-report.md:324-325`). `rank-at′-irr` is
`isPropTgt`'s `J` block (`Probe521.agda:982-1000`) at a weaker conclusion,
five lines, and it is the same design law: **the motive does not name the
path.**

**ONE PREMISE OF THE BRIEF I CHECKED AND CONFIRMED.**
`[LJ-1.490]`'s `rankFo` (`Probe490.agda:95-104`) and `[LJ-1.521]`'s
(`Probe521.agda:493-502`) are the same formula. `[LJ-1.521]` split
`assignAt`'s body into `asgσ`/`asgρ`/`asgχ`/`asgψ` and `supAt`'s into
`supB2`/`supB1`/`supBody`; unfolding those names gives `[LJ-1.490]`'s
bodies character for character. So the carve rebuilt here at
`[LJ-1.521]`'s `rankFo` is `[LJ-1.490]`'s carve.

## 1. W3, THE INSTANTIATION

**GREEN AT THE FIRST ATTEMPT.** `agents/tasks/LJ-1-524/runs/W3.agda`,
written before the obligation and with the obligation omitted, exit 0 on
the first run (`runs/w3-try1.out`, 4.59 s with `Probe521` cold).

    adequate-at-witness :
        (a : S) (oa : IsOrd (fst a)) (z : S)
      → ⟨ (z ∷ []) ⊨ P521.rankFo (ordQ a oa) a ⟩
      → Σ[ m ∈ S ] Σ[ mx ∈ ⟨ fst m ∈ fst a ⟩ ]
          (fst z ≡ pr (fst m) (fst (P521.rank-at′ a oa m mx)))

**THE RULING IS CONFIRMED, AND ONE THING THE BRIEF DID NOT KNOW MAKES IT
CHEAPER THAN THE BRIEF THOUGHT.** `[LJ-1.521]` ALREADY WROTE THIS TERM.
`rankFo-adequate′-nonvacuous` (`Probe521.agda:1169-1176`) is
`rankFo-adequate′` applied at `ord-set-witness a oa .fst` and nothing else.
So the brief's "nobody has fed `ord-set-witness`'s `Q` to a conjunct" is
right about a CONJUNCT and wrong about the adequacy: the instantiation
itself was already green in the tree before this task started. W3 measured
it again at this frame, under my own file, because a claim about a
predecessor's file is a claim I cannot check by citation alone.

**MEDIAN 1.51 s, PEAK RSS 347799552 BYTES**, three forced rechecks
(1.55 s / 1.51 s / 1.48 s at 347799552 / 347799552 / 347783168), all exit
0, `runs/w3-1.out` to `runs/w3-3.out`. The file is 66 lines: 31 comment,
10 blank, 25 code.

## 2. WHAT INSTANTIATING Q COST

**NOTHING.** In those words, as the brief asked.

The telescope after instantiation is `(a : S) (oa : IsOrd (fst a)) (bnd : S)`
and nothing else: no `Q`, no `ord-reads-Q`. Before instantiation it would
have been `(Q : S) (a : S) (oa : IsOrd (fst a)) (hQ : ord-reads-Q Q a oa)
(bnd : S)`, so instantiation REMOVES two binders and adds none. Nothing that
was provable at an arbitrary `Q` is now not provable, because **nothing was
provable at an arbitrary `Q`**: `rankFo-adequate′` consumes
`ord-reads-Q Q a oa` (`Probe521.agda:1006-1011`) and that is the only route
from a pair in the carve to a member-and-rank pair, so a conjunct at an
arbitrary `Q` has no proof to instantiate. The determined `Q` is strictly
more available than the hypothesised one, and `InjL` and `InjCode` name no
`Q` (`src/L/GCH.lagda.md:37-38`, `src/L/Cardinal.lagda.md:223-228`), so no
consumer can ask for a different one.

**ONE THING IT DID COST, AND IT IS NOT THE INSTANTIATION'S FAULT.** With
`Q` determined, the carve's name is `fst (rank-graph (ordQ a oa) a bnd)`,
a term with FIVE head symbols above `bnd`. Section 3 is what that cost and
how it was cured.

## 3. THE PRICE, AND THE ONE THING THAT RESISTED

**THE MATHEMATICS COST ABOUT SIX SECONDS. NAMING THE CARVE TWICE COST MORE
THAN TEN MINUTES.** That is the finding of this task, and it is worth more
to the next brief than the conjunct's own seconds.

**FIRST, THE MACHINE.** This pane is marked `machine: shared` and carries
`GHCRTS=-A64m -I0 -M8g`, which I read from the pane and never set. Every
run below records it in its own first line. `_build/tools/agda-watchdog.log`
records no kill during this task, and no run of mine hit the 8 GB cap: peak
RSS never exceeded 2612281344 bytes. **There is no heap event in this
report.** One Agda process at a time, always.

**TWO RUNS DID NOT FINISH AND NEITHER IS A PRICE.** Each is a LOWER BOUND
on a run that did not complete, and I say which is which every time.

- `runs/full-try2.out` carries a started line and no completion line. It
  was stopped by my own ten-minute cap.
- `runs/bisect-BisI.out` is `exit=137`, killed by my own five-minute cap.

**THE BISECTION.** With the obligation written and the file not finishing,
I cut the file at seven points and measured each. One Agda process at a
time. All cuts are kept as `runs/Bis*.agda.txt`.

| file cut after | wall | peak RSS | exit | run |
|---|---|---|---|---|
| the carve and W3 | 2.04 s | 400211968 | 0 | `runs/bisect-BisA.out` |
| `rank-at′-irr` | 1.99 s | 397246464 | 0 | `runs/bisect-BisB.out` |
| the `Carve` reading | 6.35 s | 1595949056 | 0 | `runs/bisect-BisC.out` |
| `SvAtOf`, `svAt-is-first-of-InjCode` | 6.57 s | 1562378240 | 0 | `runs/bisect-BisD.out` |
| `same` | 10.97 s | 2301755392 | 0 | `runs/bisect-BisE.out` |
| `agree` | 12.63 s | 2612281344 | 0 | `runs/bisect-BisF.out` |
| `sv` | 12.53 s | 2569043968 | 0 | `runs/bisect-BisG.out` |
| `thm`, environment written as `G` | 11.76 s | 2549104640 | 0 | `runs/bisect-BisH.out` |
| `thm`, environment written as a SECOND name | did not finish | not reached | 137 | `runs/bisect-BisI.out` |

**THE WHOLE MATHEMATICS IS THERE BY `sv`, AT 12.53 SECONDS. THE LAST LINE
IS FREE OR IT IS UNBOUNDED, AND THE ONLY DIFFERENCE IS WHETHER THE CARVE
HAS ONE NAME OR TWO.** BisH and BisI prove the same theorem by the same
term. BisH writes the carve as `G` in the statement and as `G` in the
proof: 11.76 s. BisI writes it as `carve a oa bnd` in one place and
`Carve.G a oa bnd` in the other: not finished in five minutes.

**WHY.** `_⊨_` recurses on the FORMULA, not on the environment, so
comparing two satisfaction predicates at `svAt zero` walks all the way down
to the atom `pr (fst x) (fst y) ∈ fst γ₀` (`src/L/Coding/Model.lagda.md:210-214`
and `:218-219`). `_∈_` on the cumulative hierarchy must put its right
argument in constructor form. Two spellings of the carve are not
syntactically equal, so that reduction unfolds `rank-graph`,
`hasSeparationL` and the presentation. One spelling and the comparison is a
syntactic hit and nothing is unfolded at all.

**THIS IS `[LJ-1.521]`'s LAW AT A NEW SITE, AND I RE-MEASURED IT RATHER
THAN TRANSFERRING IT.** `[LJ-1.521]` measured that putting a path inside a
type family unfolds `_∈ₛ_` through the presentation
(`lj-1.521-report.md:229-236`). Here no path is inside a family; what is
inside is a second SPELLING of the same set. The cure is the same shape
and the trigger is different, so the Boundary's "a measured cure does not
transfer by analogy" (`AGENTS.md:45`) is satisfied by the table above and
not by the citation.

**THE CURE IS ONE LINE OF DESIGN: THE CARVE HAS ONE NAME AND ITS BODY
APPEARS ONCE.** `Carve.G` (`Probe524.agda:193-194`) is that name. Every
type that mentions the carve says `G`, including `Hold`
(`Probe524.agda:203-204`), `Carve.thm` (`:254-255`) and the obligation's
own statement (`:263-266`). The body `fst (rank-graph Q a bnd)` appears
exactly once in the file.

**I KEPT NO SEAL AND I ADDED NONE.** `[LJ-1.521]` kept two `opaque` blocks
it could not re-justify (`lj-1.521-report.md:264-271`). This file adds
nothing to them; `swo-rank′` and `rank-at′` arrive already sealed through
the import, and that sealing is load bearing here in a way this task CAN
state: `rank-at′` appears in four types of section 5, and if it unfolded,
each of those would carry `swo-rank′` at a concrete `SWO` record. I did not
measure the unsealed variant, so this is a reason and not a measurement,
and I mark it as such.

## 4. THE OTHER THREE

The brief ordered a verdict on each and ordered that I not build them. **I
built none of them.** Each line below is checked at its `file:line` in this
worktree.

### the range clause: NEEDS ONLY THE `swo-rank′` RE-BASING

The clause is `(x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → ⟨ fst y ∈ fst b ⟩`
(`src/L/Cardinal.lagda.md:228`). `Carve.val` (`Probe524.agda:225-228`) already gives
`fst y ≡ fst (rank-at′ a oa m mx)`, so the clause reduces to: that rank is a
member of `b`. `boundingOrd`'s third component is exactly that
(`src/L/Ordinal.lagda.md:154-155`, `→ Σ[ β ∈ S ] (IsOrd β × ((x : X) → ⟨ f x ∈ˢ β ⟩))`).
**`[LJ-1.490]` forms that pack on `swo-rank`** (`Probe490.agda:211-213`),
the rank `[LJ-1.497]` refuted, so the pack must be re-formed on
`swo-rank′`. **That is the whole gap. Nothing else is missing.**

### `injAt`: NEEDS THE RE-BASING AND ONE LEMMA

`injAt-in` (`src/L/Coding/Injection.lagda.md:72-75`) wants
`(y x x' : S) → Holds₀ x y → Holds₀ x' y → fst x ≡ fst x'`, the mirror of
what this task proved. Through `Carve.read` it reduces to: the rank is
INJECTIVE, that is `fst (rank-at′ a oa m mx) ≡ fst (rank-at′ a oa m' mx')`
implies `m ≡ m'`. **That is not a delivered term.** `[LJ-1.521]`'s
`rank-mem-in` (`Probe521.agda:399-403`) plus `self∈sucV`
(`src/V/Model.lagda.md:236-237`) gives
`swo-rank′ w j ∈ swo-rank′ w k` whenever `j ≺ k`, and `SWO.tri∙` with
`∈-irrefl` closes it. **One lemma, arithmetic on delivered parts, and it is
not a wall.** `Bound` is also needed for the clause's codomain, so the
re-basing binds here too.

### `domAt`: HALF IS THE RE-BASING, HALF IS A NEW THEOREM

`domAt-out` (`src/L/Coding/Model.lagda.md:289-292`) is delivered: `Carve.arg`
(`Probe524.agda:221-222`) gives `fst x ≡ fst m`
with `mx : ⟨ fst m ∈ fst a ⟩` in hand.

`domAt-in` (`src/L/Coding/Model.lagda.md:294-296`) is NOT delivered and
nothing in the tree supplies it. It asks for the CONVERSE of
`rankFo-adequate′`: given `⟨ fst x ∈ fst a ⟩`, that `rankFo Q a` IS
SATISFIED at the pair of `x` and its rank, AND that the pair is in the
bound. **This task did not touch that converse and does not make it
cheaper.** `[LJ-1.521]` named its shape: it must exhibit an approximating
function as a set of the model and prove it satisfies `fnAt`, `assignAt`
and `supAt` (`lj-1.521-report.md:384-388`). The re-basing is needed for its
second half as well (`Bound.below`, `Probe490.agda:221-232`).

| conjunct | what it needs now |
|---|---|
| `svAt` | NOTHING. Delivered by this task, at a free `bnd`. |
| range clause | the `swo-rank′` re-basing of `Bound`, `C`, `bnd`, and nothing else |
| `injAt` | the re-basing, plus rank injectivity: one lemma from `rank-mem-in` |
| `domAt` | the re-basing, plus the CONVERSE of the adequacy: a new theorem |

**`svAt` DID NOT NEED THE RE-BASING AND THE FILE PROVES WHY.** `bnd` is a
free parameter of the obligation (`Probe524.agda:263-265`). `svAt` never
reads the bound: the separation carves out of ANY `bnd`
(`Probe524.agda:86-90`), and the conjunct only reads pairs already in the
carve. So the obligation as proved holds at whatever the re-based bound
becomes, and the brief's "Do it only if `svAt` needs it, and say so" is
answered: **it does not, and the free `bnd` is the evidence.**

## MEASUREMENTS

**Full-file median wall 12.20 s. Median peak RSS 2444214272 bytes.** Three
forced rechecks: 11.97 s, 12.29 s, 12.20 s, at 2444247040, 2444214272 and
2352332800 bytes. `runs/full-1.out` to `runs/full-3.out`, all exit 0. **No
heap event.** Caliber `-A64m -I0 -M8g`, read from the pane and never set by
me.

**W3 alone: median wall 1.51 s, median peak RSS 347799552 bytes.** Three
forced rechecks, `runs/w3-1.out` to `runs/w3-3.out`, all exit 0.

**A FOURTH FORCED RECHECK EXISTS AND I DO NOT HIDE IT.** After the report
was written I ran the delivered file once more to confirm it green:
10.42 s at 2444230656 bytes, exit 0, `runs/full-final.out`. It is FASTER
than any of the three above and I did not fold it into the median, because
the median the brief asked for is over the three rechecks, and moving the
figure after the fact on a run made for a different purpose is how a number
stops being checkable. **The honest reading of all four is 10.4 s to
12.3 s.**

**THE FORCED RECHECK DELETED ONLY THIS TASK'S INTERFACE.** Before each of
the six runs above I removed
`_build/2.8.0/agda/agents/tasks/LJ-1-524/Probe524.agdai` (respectively
`.../runs/W3.agdai`) and left everything else warm. **So each number is
this probe re-elaborated against warm interfaces for `src/` AND for
`LJ-1-521.Probe521`.** The one run with `Probe521.agdai` deleted as well is
15.66 s (`runs/full-with-import.out`, exit 0). **A cold-tree number is not
in this report and nothing may be funded against these as if it were.**

The file is 266 lines: 123 comment, 38 blank, 105 code.

## 5. ESTIMATE AGAINST MEASURED

**ESTIMATE for the Agda was about 200 lines, of which the obligation about
50. MEASURED 266 lines, of which 105 are code.** The estimate was close on
total lines and wrong about where they went, and I name each part.

- **The obligation: estimated about 50, measured about 30.** `Carve.thm`
  plus `svAt-at-carve` plus `Hold` is 10 lines; the reading (`sat`, `read`,
  `arg`, `val`) is 20. It came in UNDER because `svAt-in` does the whole
  object-language half in `src/`, and because `rankFo-adequate′` returns an
  untruncated `Σ` so no truncation is eliminated here at all.
- **The rebuilt carve: estimated with the adequacy at about 150, measured
  10.** `rank-graph` and `rank-graph-out` are four lines each. The other
  140 the brief allocated were for the adequacy, and the import replaced
  them.
- **`rank-at′-irr`: NOT ESTIMATED, measured 20.** The brief's step list
  ended at `↾-reflects`, and `isPropTgt` was named as "exactly this
  argument, already written". It is the argument, but it is written for a
  FIXED `z` and `svAt` compares two different `z`s that share a first
  component, so the term does not apply and its `J` block had to be
  re-spelled at a weaker conclusion. **This is the one place the brief's
  four-step chain is a five-step chain, and section D-10 above prices it.**
- **Comment: 123 lines, and 46 percent of the file.** Most of it is section
  5's price finding, which is the thing the next brief needs and which the
  file itself cannot carry any other way.

**W3's ESTIMATE was about 20 lines and under 40 seconds. MEASURED 25 code
lines and 1.51 seconds.** The brief was right not to fund it against
`[LJ-1.521]`'s numbers.

## THE RATIO BAR

**The bar cannot fire on this task and the brief says why.** The divisor is
the in-fence line count of this task's write scope, counted the ledger's
way: non-blank lines inside ` ```agda ` fences. My write scope is
`Probe524.agda`, `runs/`, and two `.md` files. **A raw `.agda` probe carries
no fence and counts 0**, and nothing in the scope is a `.lagda.md` master
under `src/`. So the 0.0123 seconds per in-fence line has no divisor here.

Recorded for the day the conjunct moves into `src/`: the mathematics is
12.20 s over 105 code lines, 0.116 s per code line. **That is not the
ratio the bar measures and it may not be compared with it.** It is here so
that whoever lands this in a master knows the order of magnitude before
they start, and section 3 tells them the one thing that would make it
unbounded.

## W2, THE GENERIC-CARRIER CLAUSE

**ANSWERED, AND THIS TASK ADDS NO FIXED FORM.** `rank-at′-irr`
(`Probe524.agda:128-145`) is stated at generic `a`, `oa`, `m`, `m'` and both
membership proofs, and is instantiated once, by `Carve.agree`
(`:239-245`). `Carve` itself is a module at generic `(a , oa , bnd)`, and
the obligation is its one projection. **The carve's `bnd` is free rather
than fixed at `[LJ-1.490]`'s `rank-bound`, which is W2 buying something
concrete here:** the same term serves the delivered bound and the re-based
one, so the `swo-rank′` re-basing will not reopen this conjunct.

**No deadline forced a fixed form and there is no conflict to report.**

## W4, THE RETIREMENT CLAUSE

**Not applicable. This task retires no module and deletes nothing.**
`dev/ARCHIVE.md` takes no row. Nothing under `src/` changed.

Priced against the ideal form written fresh today: the ideal `Probe524.agda`
is the file that is here, minus about 40 lines of the section 5 comment,
IF and only if the one-name law is by then written in `dev/LESSONS.md`. It
is not, so the comment is load bearing. **If the law lands as a lesson, the
40 lines come out and the file is about 226.**

## WHAT I DID NOT DO

- I did not carry `hQ` in the telescope. The ruling is instantiation and
  the instantiation is green.
- I did not build `domAt`, `injAt` or the range clause.
- I did not do the `swo-rank′` re-basing of `Bound`, `C` and `bnd`, because
  `svAt` does not need it and section 4 gives the evidence.
- I did not revert to `swo-rank` and I did not rebuild `rankFo-adequate′`.
- I did not postulate, and I used no `TERMINATING` or `NON_TERMINATING`.
- I did not set `GHCRTS`, and I never ran two Agda processes at once.
- I did not write anything into `src/`, and I did not commit or push.
- I did not add a `dev/glossary.toml` entry.
- I did not re-measure whether `[LJ-1.521]`'s two `opaque` seals are still
  load bearing. Section 3 says why I kept them and marks that as a reason,
  not a measurement.
- I did not propose the one-name finding as a `dev/LESSONS.md` entry. It is
  measured at ONE site, and C-42's discipline says the next action is the
  SWEEP and not the cure: **how many other types in the tree name a carved
  set by its body inside a `⊨` or a `∈` is unmeasured, and that count
  should come before any law is written.**

## GATES RUN

Every gate below exits 0 in this worktree.

- `scripts/gate/check-probes.py --check`: `check-probes: clean (5561
  tracked files, no probe outside agents/tasks/ and no generated file)`.
- `scripts/gate/lint-agda.py --check`: silent, clean.
- `scripts/gate/lint-prose.py --check`: silent, clean.
- `scripts/gate/check-fences.py --check`: `check-fences: clean (102
  masters, run threshold 3)`.
- `scripts/pod/check-closure.py --check closure`: `check-closure: clean
  (102 masters; closure, archive)`.
- `scripts/gate/check-rule-ids.py`: `check-rule-ids: clean (56 files, 165
  lessons, 68 decisions, dev/rules.toml)`.
- `scripts/pod/check-spec-surface.py --check`: `check-spec-surface: clean
  (8 surface file(s), 201 declaration(s), 7 guarded rule home(s), 499
  in-fence lines)`.
- `scripts/gate/check-glossary.py --check`: silent, clean.
- `make typecheck` was NOT run and does not cover this task: its recipe is
  `$(AGDA) $(EVERYTHING)` with `EVERYTHING := src/Everything.lagda.md`
  (`Makefile:15`, `:26`, `:49-50`), and no probe is in that index. The probe's own
  exit 0 is the evidence, and `runs/full-1.out` to `runs/full-3.out` carry
  it.
- **The worktree has no `.venv`.** It is gitignored and lives only in the
  main checkout, so every gate above was run as
  `/Users/alsg/Agentic/Bedrock/.venv/bin/python <script>` with this
  worktree as the working directory. That is the pinned interpreter and no
  global tool was used.

Working tree at the end of this task: `agents/tasks/LJ-1-524/` untracked
and nothing else changed (`git status --porcelain` is one line, `?? agents/tasks/LJ-1-524/`).

## ARCHIVE USED

The brief's corpus search named five candidates. I answer all five.

- **`dev/ARCHIVE.md`: READ, and it changed nothing.** `dev/ARCHIVE.md:271`
  carries "Twelve `opaque` blocks spread across `src/L/Godel/Operations.lagda`",
  the case `[LJ-1.521]` cites for "a seal is a measurement, not a habit".
  I read it before deciding whether to add a seal of my own, and I added
  none; section 3 records that. This task retires nothing, so the file
  takes no row.
- **`archive/dev/LJ-dispatch-index.md`: not used.** I grepped it for
  `swo-rank`, `rankFo`, `LJ-1.521` and `LJ-1.497` and it returned nothing.
  A dispatch index of closed work carries no statement this task needs.
- **`archive/dev/JOURNAL-archived.md`: not used.** Same grep, no hit. A
  journal is history, and the Boundary makes the live documents the source.
- **`archive/dev/JOURNAL.md`: not used.** Same grep, no hit.
- **`archive/dev/DECISIONS-archived.md`: declined.** It is the archived
  `D<n>` series, and the rules in force for this slot are the `W` clauses
  of `dev/memos/LJ-4-pod-program-design.md` section 3.1 and the Boundary.
  A bare `D<n>` resolves only against this archived file and binds nothing
  today, so reading it could only mislead.

## LITERATURE USED

The brief's corpus search named five candidates. I answer all five.

- **`dev/literature/truncation-and-selection.md`: READ, and it settled one
  question.** `:92` carries "HoTT Book Lemma 3.9.1: if `P` is a mere
  proposition then `P ≃ ∥P∥`." and `:193` carries "**The practical rule this
  gives.** When a proof stalls at "`PT.rec` demands a". I read both to
  check whether this conjunct needs a truncation elimination of its own.
  **It does not.** `rankFo-adequate′` already eliminates the three
  existentials of `rankFo` into `isPropTgt` (`Probe521.agda:1012-1030`) and
  returns an untruncated `Σ`; my conclusion `fst y ≡ fst y'` is a path in a
  set, so no `2-Constant` obligation arises anywhere in this file.
- **`dev/literature/devlin-II5.md`: not used.** It is the Condensation
  Lemma and the GCH in `L` at the level of the mathematics. This task
  builds one object-language conjunct at a delivered adequacy and takes no
  mathematical decision the dossier could inform.
- **`dev/literature/digest.md`: declined.** It pins the orthodox form of
  the RUD route, which `dev/ARCHIVE.md` records as retired. The route this
  task sits on is the coding leg, not the rud one.
- **`dev/literature/terms-2026-08.md`: not used.** It is a terminology
  dossier for the owner's naming ruling. This task adds no term and the
  Boundary forbids me to choose one.
- **`dev/literature/geology.md`: not used.** Set-theoretic geology is not
  in this task's path.
