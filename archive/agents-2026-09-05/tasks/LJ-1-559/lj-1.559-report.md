# LJ-1.559 report: `domAt` over the rank carve

## HEAD
head_slot: coder
machine: shared
verdict: GO

## VERDICT

**GO. `domAt-at-carve` is built, with no holes and no postulate.**
`agents/tasks/LJ-1-559/Probe559.agda:336-339`, exit 0, caliber
`-A64m -I0 -M8g` taken from the pane, one Agda process at a time. Three cold
runs at 4.00 s, 4.12 s and 3.99 s (`runs/full-1.out` to `runs/full-3.out`; the
interface was removed before each).

    domAt-at-carve :
        (a : S) (oa : IsOrd (fst a))
      → DomAtOf (Carve.G a oa) a

**THE FOURTH CONJUNCT IS DELIVERED AND THE CODING LEG NOW HAS ALL FOUR.**
`svAt` (`[LJ-1.524]`), the range clause (`[LJ-1.529]`), the rank injectivity
(`[LJ-1.531]`) and this. Read the section `WHAT AN ASSEMBLY COSTS` before you
queue B9: the four are NOT at one carve today, and that is a real obstacle
with a measured cure.

**TWO DISPATCHES SPENT 1800.01 s EACH ON THIS TERM AND IT COSTS 3.99 s.** The
gap is not a mystery and it is not luck. It is stated in
`WHY THE PREDECESSORS RAN LONG`, from this task's own numbers.

## THE FLOOR

The brief orders three numbers. Here they are, all at caliber
`-A64m -I0 -M8g`, one Agda process at a time.

**1. THE MINIMAL IMPORT SET.** `agents/tasks/LJ-1-559/runs/W3.agda:19-41`.
Eighteen imports and one predecessor probe:

    Base.Prelude, Base.Truth, Base.Classical (LEM)
    FOL.ZFStructure (module hPropStructure), FOL.Syntax (Formula),
    FOL.Absoluteness
    V.Hierarchy (𝒮ᵥ), V.Coding (pr), V.Presentation (fiber)
    L.Constructible (𝒮ʟ; isL; isL-trans; IsOrd)
    L.Ordinal (boundingOrd), L.InjChain lem (module PairBound)
    L.WellOrder.Base (SWO), L.Axioms.Full lem (hasSeparationL)
    L.Coding.Model (domAt)
    Cubical.Data.FinData, Cubical.HITs.CumulativeHierarchy.Base and
    .Properties
    LJ-1-521.Probe521

**THE FULL PROBE ADDS EXACTLY THREE MORE** (`Probe559.agda`, 22 import lines
against the floor's 19): `L.Cardinal lem` for `InjCode`, so that section 4 can
read the conjunct's type out of the definition rather than retyping it;
`Cubical.HITs.PropositionalTruncation`, for the one `PT.rec` and the five
`PT.∣_∣₁`; and `LJ-1-537.Probe537` for `approx-carve`. **Nothing else was
needed and nothing else was taken.** In particular the three sibling conjunct
probes are absent, as the brief orders.

**2. THAT SET WITH THE OBLIGATION'S TYPE AND NO PROOF: 4.12 s cold,
1.39 s and 1.45 s warm.** `runs/w3-1.out` to `runs/w3-3.out`, exit 0 each.
The cold number builds `P521`'s interface inside the run; the warm numbers do
not. `runs/W3.agda:90-92` states the type as a definition rather than a
hole, so the run exits 0 and the number is comparable with a full run.

**3. THE FINISHED TERM: 4.00 s, 4.12 s, 3.99 s.** `runs/full-1.out` to
`runs/full-3.out`, exit 0 each, own interface removed before each,
`P521` and `P537` warm.

**THE OBLIGATION COSTS ABOUT 2.6 s ABOVE ITS OWN FRAME.** 3.99 s against a
1.39 s warm floor. Peak resident set 1,020,510,208 bytes, against the
`-M8g` cap: no heap pressure at any point, and no WALL event.

**ONE MORE NUMBER THE BRIEF DID NOT ASK FOR AND THE NEXT TASK NEEDS.** With
`Probe559`, `Probe521` and `Probe537` interfaces ALL removed, so that a fresh
worktree pays the whole chain: **7.67 s**, exit 0, peak resident set
995,983,360 bytes (`runs/cold-all.out`). That is the true cost of this
obligation from nothing, with `src/` warm.

## WHY THE PREDECESSORS RAN LONG

Three sentences, as ordered, and then what I could rule in and out. **I have
no REPORT and no PROBE from either task; both left only their brief.** So each
sentence below says what its evidence is, and I mark inference as inference.

**FIRST, IT WAS NOT THE FRAME.** My floor is 1.39 s warm and 4.12 s cold and
the whole chain from nothing is 7.67 s, so no accumulation of import cost in
this frame can reach 1800 s, and the time therefore went into elaborating one
term, not into loading the site.

**SECOND, THE EVIDENCE NAMES THE TERM.** `[LJ-1.541]` left seven bisection
files and, next to `Pin.agda`, a file named `PinBody.agda`; `[LJ-1.547]` left
exactly two bisection files and they are named `BisName.agda` and
`BisBody.agda`
(`dev/pod/transitions/2026-08.jsonl:2996` and `:3003`, in the main checkout;
see the note at the end of this section). **`BisName` against `BisBody` IS
`[LJ-1.524]`'s measured axis**, which is whether a type spells the carve's
NAME or the carve's BODY, and `[LJ-1.524]` measured the body spelling at more
than ten minutes and again at more than eight minutes on this same carve
(`agents/tasks/LJ-1-524/Probe524.agda:160-171`). **So both predecessors were
bisecting the one blowup this site is known to have**, `[LJ-1.541]` over
`domAt` and `[LJ-1.547]` over the assembly, and I avoided it by obeying
`[LJ-1.524]`'s rule from the first line rather than rediscovering it. **This
is inference from FILENAMES in a transition record, not a reading of either
file, because neither file exists.**

**THIRD, `[LJ-1.547]` WAS NOT A SECOND ATTEMPT AT `domAt` AT ALL.** Its brief
is `# LJ-1.547: assemble the four conjuncts into one InjCode`
(`agents/tasks/LJ-1-547/LJ-1.547.md:1`, main checkout), and it names its own
precondition in terms: "THIS BRIEF ASSUMES `[LJ-1.541]` CAME BACK GO, AND IT
IS THE ONLY THING IT ASSUMES" (`:16`), with the `domAt` row of its own table
marked "`[LJ-1.541]`, assumed GO" (`:27`). **`[LJ-1.541]` had not come back
GO.** So `[LJ-1.547]` spent five attempts assembling four conjuncts of which
one did not exist, and its brief told it to stop at the D-10 in exactly that
case. The brief for THIS task describes it as "five times trying to hold four
conjuncts at once", which is true, and the reason it was holding four is that
it was the assembly task.

**A FOURTH CANDIDATE I CANNOT SETTLE, AND THE CRITIC NAMED IT FIRST.**
`[LJ-1.541]` ran at `concurrency: 2` and `[LJ-1.547]` at `concurrency: 1`
(the same two transition records). Its own critic brief lists "contention from
other concurrent Agda writers on this shared machine"
(`agents/tasks/LJ-1-541/review-LJ-1-541-4.md:18`) beside exponential
elaboration as a candidate. **I ran alone and cannot measure contention**, so
I record it as unsettled rather than dismiss it.

**WHAT I RULED OUT, AND IT WAS MY OWN FIRST HYPOTHESIS.** I suspected the
predecessors had been given `[LJ-1.524]`'s free-`bnd` telescope, which would
make the target FALSE (next section) and no amount of time would close it.
**That is wrong and the surviving brief says so.** `[LJ-1.541]` directed the
bound half at `rank-bound′` from `[LJ-1.529]`
(`agents/tasks/LJ-1-541/LJ-1.541.md:31` and its premise 8 at `:66`), which is
the same bound I used. Its brief also anticipated the satisfaction half
correctly, piece for piece (`:17-30`). **`[LJ-1.541]` was given the right
route and did not finish it; it was not given a false target.**

**A NOTE ON THE BRIEF'S PREMISES 1 TO 3, AND ON WHERE THE RECORD LIVES.**
Premise 1 cites `agents/tasks/LJ-1-541/LJ-1.541.md:1` and premises 2 and 3
cite `dev/pod/transitions/2026-08.jsonl:2996` and `:3003`. **None of the three
resolves in this worktree**: the task directory is absent, and this worktree's
copy of the transitions file has 157 lines, not 3036. **All three resolve in
the main checkout, and I read them there, read-only.** What survives there is
the two briefs and four critic briefs; `agents/tasks/LJ-1-541/runs/` and
`agents/tasks/LJ-1-547/runs/` are both EMPTY, and no probe, report or review
from either task exists anywhere. **So the brief's premise 1 is sound and its
"nothing of `[LJ-1.541]` survived" is right about the WORK, while the two
BRIEFS did survive and are worth reading. The worktree's transitions snapshot
is stale and the next dispatch should not chase it there.**

## D-10, BEFORE ANY AGDA

The brief orders D-10 as the import list. I did that (the floor above). The
D-10 finding is not the import list, it is this.

**THE TARGET IS FALSE AT A FREE `bnd`, AND THAT IS WHY THIS CONJUNCT'S
TELESCOPE IS NOT `[LJ-1.524]`'s.** `[LJ-1.524]` proved `svAt` with `bnd` a
free parameter and said so in terms
(`agents/tasks/LJ-1-524/Probe524.agda:181-186`): `svAt` never reads the bound.
**`domAt` does.** `domAt` is two implications
(`src/L/Coding/Model.lagda.md:278-280`) and the second one says: if `x ∈ a`
then `x` HAS an entry in the carve. The carve is a separation out of `bnd`
(`Probe559.agda:150`), so it can only hold what `bnd` already holds. Take
`bnd` empty: the carve is empty, no `x` has an entry, and the clause then
asserts that `a` has no members. **That is false for every non-empty `a`, not
merely unproved.** So the obligation is stated here over the RE-BASED bound
of `[LJ-1.529]` and not over a free one, and `Bound′.below`
(`Probe559.agda:129-140`) is the fact that closes the gap.

This is the same shape as the D-10 finding recorded at
`archive/dev/JOURNAL-archived.md:1280`.

## W3, THE WIDEST UNMEASURED TERM

The brief made W3 a NUMBER and not a type, and said so. It is answered above
under `THE FLOOR`: `runs/W3.agda`, three runs, `runs/w3-1.out` to
`runs/w3-3.out`, 4.12 s cold and 1.39 s / 1.45 s warm, exit 0 each. It was
written FIRST and typechecked ALONE, before any proof existed.

**THE FLOOR SAID GO.** 1.39 s against a 1800 s timeout is not near the
timeout, so the brief's own stop condition did not fire and I continued.

## WHAT THE OBLIGATION COST

**THE PART NO PREDECESSOR BUILT IS THE WRITING DIRECTION, AND IT IS 19 LINES
OF CODE.**
`Probe559.agda:212-238`. `rankFo-adequate′` (`Probe521.agda:1006-1012`) READS
a satisfaction and returns the pair's shape; nothing in the tree went the
other way. `rankFo` is four existentials over one conjunction
(`Probe521.agda:493-501`) and the four witnesses are named by
`rankFo-adequate′` itself in the order `q`, `m`, `r`, `f`
(`Probe521.agda:1013-1021`). Three of the four are determined at this site:
`q` is the instantiated `Q`, so its equation is `refl`; `m` and `r` are the
member and its rank. **The fourth is `[LJ-1.537]`'s `approx-carve`
(`agents/tasks/LJ-1-537/Probe537.agda:616-620`), whose three components are
exactly the three conjuncts of the innermost body.**

**`[LJ-1.537]` READ THIS ROUTE OFF THE TYPES AND IT WAS RIGHT IN EVERY
DETAIL.** `agents/tasks/LJ-1-537/lj-1.537-report.md:214-247` lists the four
witnesses, names `refl` for the first, `prʟ-fst` for the second, the
hypothesis for the third and `approx-carve` for the fourth, and names
`rank-bound′` for the bound half. That is what I built. **Its own caution was
too pessimistic**: it warned that "the next task should expect the de Bruijn
transcription of `rankFo`'s four existentials to be its real cost"
(`lj-1.537-report.md:246-247`), and the transcription is
`Probe559.agda:232-238`, six lines, and the whole file is 3.99 s.

**THE VERDICT I TOOK FROM THE PREDECESSOR.** `[LJ-1.537]`'s report carries
`verdict: GO` (`lj-1.537-report.md:6`) and pins its type in a separate file
(`agents/tasks/LJ-1-537/runs/Pin.agda`). I took the type from the probe that
typechecked (`Probe537.agda:616-620`) and not from the brief.

**WHAT THE SHAPE RESISTED: one thing, and it was scope, not mathematics.**
`[LJ-1.521]` keeps its de Bruijn shifts `s2` to `s5` `private`
(`Probe521.agda:88-96`), so `P521.s3` is not in scope. That was the only error
in the whole task (`runs/try1.out`, exit 42, `NotInScope`, 2.64 s). Rebuilt in
two lines at `Probe559.agda:89-90`. **Nothing else failed at any point.**

**NOTHING WAS WEAKENED.** Both implications are proved, not one. No hypothesis
was added to the telescope beyond `a` and `oa`. Nothing is postulated (the
whole chain, `Probe521`, `Probe537` and `Probe559`, contains no `postulate`;
the only matches for that word are comments). Nothing lands in `src/`.
`InjCode` is NOT assembled and B9 is untouched. I did not write a
`review-of-*.md`, because this is not a stop.

## THE TYPE IS PINNED

`agents/tasks/LJ-1-559/runs/Pin.agda`, exit 0, 1.51 s (`runs/pin-1.out`).
`[LJ-1.537]`'s discipline. The probe states its conjunct through an
abbreviation, `DomAtOf` (`Probe559.agda:187-188`), and an abbreviation can
drift from the brief. The pin names NO abbreviation of the probe. It does
three things:

1. `slot2` (`runs/Pin.agda:42-45`) takes `InjCode` at the carve and PROJECTS
   its second component, so the type is fixed by `src/L/Cardinal.lagda.md:226`
   itself and this file never writes it.
2. `built` (`runs/Pin.agda:49-51`) writes that same type out in full, with no
   `DomAtOf`, and inhabits it by `domAt-at-carve` and by nothing else.
3. `nonvacuous` (`runs/Pin.agda:56-60`) is below.

**AND IT IS NOT THE VACUOUS ONE.** `domAt` at an empty carve over an empty `a`
is TRUE and says nothing, so the conjunct alone is not evidence that the
coding leg has a table. `carve-holds-the-rank-pair`
(`Probe559.agda:346-350`) states the second sentence: for every member `x` of
`a`, the pair `(x , rank-at′ a oa x xa)` is a member of the carve. That is the
backward implication's own witness, exposed under one name.

## WHAT AN ASSEMBLY COSTS, AND THE ONE OBSTACLE IN ITS WAY

The brief asks whether an assembly of all four conjuncts looks affordable at
the numbers I measured. **Two answers, and they point opposite ways.**

**ON TIME, YES, AND BY A WIDE MARGIN.** Each conjunct probe, own interface
removed, `P521` warm, one process at a time, this machine, this caliber:

| probe | conjunct | cold |
|---|---|---|
| `Probe524` | `svAt` | 8.22 s (`runs/sibling-524.out`) |
| `Probe529` | range clause | 3.35 s (`runs/sibling-529.out`) |
| `Probe531` | rank injective | 1.10 s (`runs/sibling-531.out`) |
| `Probe559` | `domAt` | 4.00 s (`runs/full-1.out`) |

Sum 16.67 s, plus `P521` and `P537` beneath them. The whole four-conjunct
chain from nothing is well under a minute. **Nothing in these numbers explains
a 1800 s timeout, and nothing in them makes assembly unaffordable.**

**ON SHAPE, NOT YET, AND THIS IS THE FINDING.** **The four conjuncts are not
at one carve.** They are at three:

- `[LJ-1.524]`: `fst (rank-graph (ordQ a oa) a bnd)` with `bnd` FREE
  (`Probe524.agda:198-232`).
- `[LJ-1.529]`: the same body at `Bound′.bnd`, where `Bound′` is defined
  inside `Probe529` (`Probe529.agda:101-131`).
- `[LJ-1.559]`: the same body at `Bound′.bnd`, where `Bound′` is defined
  inside `Probe559` (`Probe559.agda:108-140`).
- `[LJ-1.531]` names no carve at all, so it is free of this.

**MY `Bound′` IS CHARACTER FOR CHARACTER `[LJ-1.529]`'s.** I checked it by
diff, not by eye: the two blocks are identical. **That is the problem, not the
solution.** Two identical definitions in two modules are two different names
for one body, and `[LJ-1.524]` MEASURED what happens when one type says one
name and another says the other: the elaborator walks `domAt` or `svAt` down
to `pr (fst x) (fst y) ∈ fst γ₀`, must put the right argument in constructor
form, and unfolds `rank-graph`, `hasSeparationL` and the presentation to do
it. It did not finish in ten minutes, and a second arrangement did not finish
in eight (`Probe524.agda:160-171`). **An assembly that mentions two of these
three carves in one type is the exact shape `[LJ-1.524]` priced at more than
ten minutes, and `[LJ-1.547]`'s `BisName.agda` / `BisBody.agda` say that is
where it was digging when it ran out of time.**

**AND THE ASSEMBLY TASK ALREADY EXISTS, PARKED.** `[LJ-1.547]` is it
(`agents/tasks/LJ-1-547/LJ-1.547.md:1`, main checkout). It reached
`attempt_max` on `sys-timeout-escalate` while its `domAt` row was still
"assumed GO" (`:27`). **That row is now real**, so the task can be re-queued;
but re-queueing it unchanged puts it straight back onto the three-carve
problem above, because nothing about the carves changed when this conjunct
landed.

**THE CURE IS CHEAP AND IT IS MEASURED.** Hoist `Bound′` and `rank-graph`
into ONE module that all four conjunct probes import, so that all four types
say one name. My section 1 and section 2 together are 40 lines of code
(`Probe559.agda:108-168`, 61 lines with their comments) and they are the whole
of what must move. Then
instantiate `[LJ-1.524]`'s free `bnd` at that one bound. **I did not do this,
because AD12 gives this brief one obligation and hoisting touches three other
tasks' files. I name it as the assembly task's W3, and its value is a number:
the four conjunct types in one file, at one carve, with holes, timed.**

## W2, ANSWERED

**The obligation is already at the generic carrier and there is no fixed form
in it.** `domAt-at-carve` quantifies over every `a : S` with `IsOrd (fst a)`
and over nothing else (`Probe559.agda:336-339`); `Write` and `Carve` are
modules in the same two parameters. No instance of `a` is named anywhere in
the file, so there is no second copy for the counting leg to pay for, and
nothing here is written twice for two towers.

**WHERE W2 IS AT RISK IS NOT THIS TERM, IT IS THE BOUND.** `Bound′` is now
written out in full in two probe files, identically. That is the same
mathematics written twice. Probes are not `src/`, so no W2 clause is broken
today, but the previous section says why it must be written ONCE before
assembly, and the reason is a measured price and not tidiness.

## W4, ANSWERED

**No module was retired by this task, so there is nothing to move to
`archive/` and no `dev/ARCHIVE.md` row to write.** The clause's second half
asks me to price the ideal form written fresh today against the chapter I
have. **The ideal form of this leg written fresh today is one carve module
plus four conjunct terms.** What the tree has is four probe files of which
three rebuild the carve or its bound. Priced from this file: the shared part
is 40 code lines (`Probe559.agda:108-168`), the conjunct proper is 70 code
lines (`Probe559.agda:212-339`), and the file is 350 lines of which 160 are
code, 132 are comment and 58 are blank. **So the ideal form saves about 40
code lines per conjunct file and, far more than that, it removes the one shape
that both parked dispatches were bisecting when they ran out of time.**

The archive regime this answer sits under is
`archive/dev/DECISIONS-archived.md:42` (D20): retired code is archived, never
deleted.

## THE IMPORTS OF PREDECESSOR PROBES

**TWO, AND BOTH ARE DECLARED IN THE FILE HEAD** (`Probe559.agda:26-44`, and the import lines are `:75-76`).

`P521` for `rankFo`, `rank-at′`, `swo-rank′`, `rank-at′-val`,
`ord-set-witness` and `rankFo-adequate′`. `P537` for `approx-carve`, which
premise 8 of the brief names and which the coder clause tells me to take from
the probe that typechecked.

The argument for a cross-task probe import is `[LJ-1.524]`'s and `[LJ-1.529]`
repeated it (`Probe529.agda:16-25`): `bedrock.agda-lib:2` lists
`agents/tasks` as an include root, the tree already carries such imports
(`agents/tasks/LJ-1-184/ProbeLJ1184C.agda:29`,
`agents/tasks/LJ-1-224/ProbeGraphSupply.agda:24`), and no rule in `AGENTS.md`,
`dev/pod/instructions/coder.md`, `dev/LESSONS.md`, `dev/pod/rulings.toml` or
`agents/README.md` forbids it.

**THE THREE CONJUNCT PROBES ARE NOT IMPORTED, AS THE BRIEF ORDERS.**
`[LJ-1.529]`'s section 1 is REBUILT here as section 1, exactly as
`[LJ-1.529]` itself rebuilt it from `[LJ-1.490]`. I measured the three of them
(the table above) but no term of `Probe559.agda` names any of them.

## LAWS ANSWERED

- **D-10.** Answered in its own section. The target IS false at a free `bnd`,
  and the five minutes found it.
- **C-22.** The report was written as a skeleton before the first Agda run and
  filled as each number landed.
- **P-l.** Obeyed and it is the reason the file is fast. No type here names a
  transparent presentation of the carve: every type says `G` or
  `Carve.G a oa`. `[LJ-1.524]` measured the other choice at more than ten
  minutes (`Probe524.agda:160-171`).
- **D-26.** Not engaged. The well-founded key is `[LJ-1.521]`'s `swo-rank′`
  and this task neither chose it nor changed it.
- **C-42.** Engaged, and it is the `WHAT AN ASSEMBLY COSTS` section. This task
  produced no refutation, but it did find a shape (one body, three names) and
  C-42's instruction is to report the COUNT before pricing the cure. **The
  count is three carves across four conjunct probes, and I searched all four
  files to get it, not just my own.**

## GATES RUN

**`make check` was NOT run to completion, and I say so plainly:** it is the
gate before a commit, this slot never commits, and its `typecheck` target
builds the whole of `src/`, which this task did not touch. I ran the
individual checks instead, as the Boundary directs. All five pass, exit 0:

    scripts/gate/lint-prose.py --check     clean
    scripts/gate/lint-agda.py --check      clean
    scripts/gate/check-probes.py --check   clean (6532 tracked files,
                                           no probe outside agents/tasks/)
    scripts/gate/check-fences.py --check   clean (102 masters)
    scripts/gate/check-rule-ids.py         clean (56 files, 165 lessons)

**TWO OF THOSE FIVE DO NOT ACTUALLY READ MY FILES, AND A GREEN RESULT FROM
THEM IS NOT EVIDENCE ABOUT THIS TASK.** `lint-prose.py:458` and
`lint-agda.py:400` both drop `agents/` by design, because a brief and a report
are frozen records and a style gate over them can only corrupt the record. So
this probe and this report are outside the prose and Agda style gates. I
checked the one Boundary rule that binds them anyway, by hand: **no em dash
occurs in any file this task wrote**, in any language.

`check-probes` is the gate that DOES bind this task, and it is the one that
matters: the probe is inside `agents/tasks/` and no generated file is
committed.

## WORKING TREE

New, untracked, all inside this task's write scope:

    agents/tasks/LJ-1-559/Probe559.agda
    agents/tasks/LJ-1-559/lj-1.559-report.md
    agents/tasks/LJ-1-559/runs/run.sh
    agents/tasks/LJ-1-559/runs/W3.agda
    agents/tasks/LJ-1-559/runs/Pin.agda
    agents/tasks/LJ-1-559/runs/*.out

No file outside `agents/tasks/LJ-1-559/` is modified. Nothing in `src/` is
touched. No `review-of-*.md` is written. Interface files under `_build/`
changed, and they are generated and never committed.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: **READ AND USED.** Line 142 is the
  measurement the brief's premise 9 cites and the method it orders:
  `| LJ-1.75 | Give each partial only the facts its rows use | 43 of 69; 122.45 s | Better than proportional: 41.6 pc cheaper for a 37.7 pc smaller telescope. Two partials plus composer, 273.88 s |`
  I applied it by rebuilding `[LJ-1.529]`'s 45-line bound instead of importing
  the whole of `Probe529`, and by importing exactly two predecessor probes.
- `archive/dev/JOURNAL-archived.md`: **READ AND USED**, twice. Line 3824 rules
  on this very clause in the satisfaction setting:
  `  by `closedAt C`, `x ∈ C`, and `domAt T C` (load-bearing); `svAt T` is not`
  and its paragraph adds that the blowup predictor is truncation elimination
  count, not formula size, which is consistent with this file: it performs one
  `PT.rec` of its own (`Probe559.agda:291`) and is 3.99 s. Line 1280 is the
  parallel D-10 finding:
  `transcribed target was FALSE (the environment order carved the pair the wrong way round) and the`
- `archive/dev/DECISIONS-archived.md`: **READ AND USED** for the W4 answer.
  Line 42 is D20, the archive regime, which is why the W4 answer says archived
  and never deleted.
- `dev/ARCHIVE.md`: **READ, NOT USED.** Line 1 is
  `# ARCHIVE.md: the archive registry`
  and it is the registry of retired MODULES. This task retired no module, so
  there is no row to write and nothing here bore on the work.
- `archive/dev/JOURNAL.md`: **DECLINED, and measured before declining.** It
  contains zero occurrences of `rankFo`, `carve` or `domAt`. Not read.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`: **READ AND USED.** Line 92:
  `HoTT Book Lemma 3.9.1: if `P` is a mere proposition then `P ≃ ∥P∥`.`
  That is the principle the forward implication runs on. `fwd`
  (`Probe559.agda:291-297`) eliminates `∥ Σ[ y ] Hold x y ∥₁` into
  `⟨ fst x ∈ fst a ⟩` by `PT.rec (snd (fst x ∈ fst a))`, and it is allowed to
  because the target is an hProp by construction. The backward implication
  goes the easy way, into a truncation, and needs nothing from this file.
- `dev/literature/digest.md`: **DECLINED.** Zero occurrences of `domAt` or
  `truncat`; its single `rank` hit is unrelated to the ordinal rank this task
  uses. Not read.
- `dev/literature/devlin-II5.md`: **DECLINED.** Devlin II.5 is set-theoretic
  background for the condensation route. This task builds one object-language
  conjunct out of terms already delivered and reads no set theory. Not read.
- `dev/literature/geology.md`: **DECLINED.** Set-theoretic geology bears on no
  part of this obligation. Not read.
- `dev/literature/terms-2026-08.md`: **DECLINED.** It is a terminology
  dossier, and this task added no term and named nothing new. Not read.
