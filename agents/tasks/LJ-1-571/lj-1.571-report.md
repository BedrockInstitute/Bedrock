# [LJ-1.571] Report: row 2, `SqAt`, and the collection that is not inhabited

## HEAD
task: LJ-1.571
slot: coder
machine: shared
obligation: agents/tasks/LJ-1-571/Probe571.agda::sqat-or-what-it-wants
verdict: GO

This report was written as a skeleton before any Agda and filled as each answer
landed (C-22, `dev/LESSONS.md:2297`). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-571/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. Nothing is postulated and no hole is left, so every reduction in the
probe is a measurement and not a claim. Both files are raw `.agda`, carry no
` ```agda ` fence, count 0 in-fence lines, and the ratio bar cannot fire on
them.

## VERDICT

**GO, ON THE SECOND DISJUNCT AND NOT THE FIRST.** The obligation is inhabited:
`sqat-or-what-it-wants` is at `agents/tasks/LJ-1-571/Probe571.agda:193`. The
program's own meter resolves it: `pass exit=0 3.11s`, `0 UNRESOLVED of 1`,
`probe_red=False` (`agents/tasks/LJ-1-571/runs/witness-1.out:4-5`), and again
after the citation fix (`agents/tasks/LJ-1-571/runs/witness-2.out:4-5`).

**READ THE NEXT SENTENCE BEFORE THE BILL CHANGES ANYWHERE.** The brief says
"A GO TAKES THE BILL FROM FIVE ROWS TO FOUR." **This GO does not.** I did not
inhabit `SqAt`. I built the other disjunct: a term naming precisely the input
row 2 lacks. **The bill stays at FIVE rows. The fifth row got smaller.** It is
written down in the probe itself so nobody can read a discharge into it
(`Probe571.agda:232-234`).

Row 2 was `P550.SqAt`, the BARE ambient square law at every ordinal L-cardinal
(`agents/tasks/LJ-1-550/Probe550.agda:309-310`). Row 2 is now `SqCollectAt`,
which is `src/L/StageBound.lagda.md:44-48`'s own `SqCollect` at every ordinal
L-cardinal (`Probe571.agda:162-163`). Everything else on the path is paid out
of `src/`.

## AMBIENT OR INTERNAL

**AMBIENT, and the answer was never close.**

`SqLaw : SV.S → Type (ℓ-suc ℓ)` (`agents/tasks/LJ-1-550/Probe550.agda:82`).
The binder under the arrow is `SV.S` and every carrier is `⟪ δ ⟫`, the ambient
presentation (`Probe550.agda:83-87`). `SL.S` occurs at exactly one place in the
whole row, `SqAt`'s outer `κ`, and it is spent at once by `fst κ`
(`Probe550.agda:310`). **Nothing under the arrow mentions `isL`, `Lset`, `𝒮ʟ`,
a code, or the satisfaction relation.**

I did not leave that as a reading. Three identity functions are the machine's
word for it, and each elaborates with the body unchanged, so the types are
DEFINITIONALLY equal and not merely equivalent:

| term | `Probe571.agda` | what it settles |
|---|---|---|
| `sqlaw-is-w3` | `:78` | `SqLaw` is W3's unfolding |
| `sqlaw-is-sqfam` / `sqfam-is-sqlaw` | `:85`, `:89` | `SqLaw α` IS `src/`'s own `SqFam α` (`src/L/StageBound.lagda.md:37-42`), both directions |
| `sqlaw-is-pointwise-sq` | `:96` | and its codomain is `src/`'s pointwise `sq` (`src/L/Ordinal/SquareLaw.lagda.md:685-687`) |

**AN ARCHIVED REVIEW REACHED THE SAME PLACE AND SAID IT PLAINLY.**
`archive/dev/JOURNAL.md:941` reads "`⟪δ⟫ × ⟪δ⟫ → ⟪δ⟫` and nothing more. **The
obligation is an INJECTION and not an". The sentence finishes on the next line
with "object-language arithmetic." That is this row, recorded before this
campaign.

**WHAT FOLLOWS FROM IT.** The brief's own branch applies: "If it is ambient, the
existing `L.Ordinal.SquareLaw` may supply it directly and this task is short."
**It does not supply it directly, and the reason is not the carrier.** It is
truncation, and the next section is that measurement.

## ONE CORRECTION TO THE BRIEF'S OWN EVIDENCE

The brief gives `SqAt`'s address as `agents/tasks/LJ-1-550/Probe550.agda:310-311`.
**It is off by one.** `SqAt :` is at `:309` and `SqAt = ...` is at `:310`; line
`:311` is blank and `:312` opens the R4 comment. I cite `:309-310` throughout
this report and in the probe.

**EVERY OTHER PREMISE I RELIED ON CHECKS OUT, AND I CHECKED THEM RATHER THAN
ASSUMING THEM.** Premise 1 (`agents/tasks/LJ-1-564/Probe564.agda:456` reads
"gch-from-five :"), premise 3 (`src/L/StageBound.lagda.md:42` reads
"-- Collection of truncated squares to a truncated family. Not inhabited."),
premise 5 (`src/L/Cardinal.lagda.md:46` reads
"-- The ambient injection type, as the square-law chain carries it.") and
premise 9 (`archive/dev/LJ-dispatch-index.md:100`) are exact at the line given.
Premise 7's line is a SECTION HEADING rather than the claim: the claim itself is
at `agents/tasks/LJ-1-556/lj-1.556-report.md:302-306`, "**THE FIRST PAYABLE
PIECE IS THE `Step` FORMULA FOR `col`, AND IT IS ONE OBLIGATION.**" That is a
pointer and not an error, and I record it only so the next reader is not sent to
a heading.

**PREMISE 5 IS WORTH MORE THAN THE BRIEF SPENT ON IT.** The chapter's own
comment calls the type ambient in so many words, at the very site row 2 runs
through. That is a third independent confirmation of D-10, alongside the
identity functions and `archive/dev/JOURNAL.md:941`.

## THE NOTE AT `StageBound.lagda.md:42`, CHECKED RATHER THAN BELIEVED

The brief ordered me to read around line 42 before believing it, and to say
whether `SqCollect` is what `SqAt` needs at all or whether the note is about a
neighbour.

**THE NOTE IS ACCURATE, IT IS ABOUT THE RIGHT OBJECT, AND IT IS ONE STEP SHORT
OF THE WHOLE STORY.** The square law has THREE strengths on this tree, not two
(`Probe571.agda:113-115`):

| level | type | who has it |
|---|---|---|
| 1 | `(δ : ...) → ∥ sq δ ∥₁`, pointwise truncated | **`src/` DELIVERS IT.** `sq-trunc-closed`, `src/L/SquareLawClosed.lagda.md:325-327` |
| 2 | `∥ SqLaw α ∥₁`, the family, truncated | nobody. Level 1 to level 2 is EXACTLY `SqCollect` |
| 3 | `SqLaw α`, the family, BARE | nobody. This is what `SqAt` asks |

`SqCollect`'s ANTECEDENT is level 1 and its CONSEQUENT is level 2
(`src/L/StageBound.lagda.md:44-48`). So it is the step between them and it is
neither of them. **`SqAt` sits one further step out at level 3.** The note
names one of the two steps that separate `src/` from row 2, and it names the
right one.

**AND THE SECOND STEP IS FREE, WHICH IS THE FINDING.** Section 4 of the probe
is the measurement. `r2` is consumed EXACTLY ONCE in the whole route, at
`r2 κ ordκ` (`agents/tasks/LJ-1-564/Probe564.agda:358-360`), inside
`power-into-succ-at`, at the SAME `κ` that `PowerIntoSuccAt` binds
(`Probe564.agda:328-331`). It is not threaded, not stored, and never used at a
second ordinal. **And the goal there is a proposition**: `PowerIntoSuccAt`
concludes `InjL (𝒫 κ) δ`, and `InjL a b = ∥ Σ[ F ∈ S ] InjCode F a b ∥₁`
(`src/L/GCH.lagda.md:37-38`). So one `PT.rec` spends the truncation and level 2
does the work of level 3.

This is the digest's own checklist step 1, and I did not invent it:
`dev/literature/truncation-and-selection.md:289` reads
"1. **Is the goal a proposition?** Then `PT.rec` applies and there is nothing to".

**SO NOBODY EVER HAS TO PAY LEVEL 3.** Untruncating `∥ SqLaw α ∥₁` would be a
genuine choice principle, because `sq δ` is a Σ carrying an injection and is no
proposition. **That price is off the board, and it was on the board an hour
ago.**

## WHERE THE TRUNCATION ENTERS, WHICH IS THE PART THE NEXT BRIEF NEEDS

`SqCollect` is not inhabited and I did not inhabit it. **But the interesting
fact is that it cannot be dodged by strengthening `src/` upstream, and this is
measured, not guessed.**

The truncation does not enter at `sq-trunc-closed`. It enters at
`LeastCardInjL`, whose predicate is `InjP γ = ∥ Inj γ ∥₁ , squash₁`
(`src/L/Cardinal.lagda.md:66-67`). It is truncated there because the
least-element search wants an hProp-valued predicate.
`dev/literature/truncation-and-selection.md:146` states the constraint in the
general form: "**The constraint the route carries: `P` must be `hProp`-valued.**
So `leastOf`". `SquareLawClosed` then spends that truncation at its descent
case with `PT.map2` and cannot do otherwise
(`src/L/SquareLawClosed.lagda.md:315-319`).

**AND THE DIGEST ALREADY NAMES THE MISSING DATUM.**
`dev/literature/truncation-and-selection.md:323` reads "what is missing is a
well-order on the INJECTIONS." That is the same object `LeastCardInjL` lacks.
**I am not pricing that here and no comparable in this report funds it.**

**A WARNING THE NEXT BRIEF SHOULD NOT SKIP.** The same digest records a
measured refutation at step 4 of its checklist: a canonical pointwise-least
pairing is TOTAL and compiles and is then REFUTED because it is SYMMETRIC
(`dev/literature/truncation-and-selection.md:305-309`). **A route that tries to
make `sq` canonical rather than truncated walks into that refutation.** The
level-2 weakening above avoids it entirely, because it never asks for a
canonical square at all.

## THE C-42 SWEEP

C-42 is in this task's law bundle and it says the next action after a site-level
finding is the sweep, with the COUNT reported before any cure is priced
(`dev/LESSONS.md:3752`). My finding is a weakening rather than a refutation, but
the discipline applies: it is measured at ONE frame and I must not let it
transfer by analogy (`AGENTS.md:45`).

**FOUR SITES IN `src/` CARRY THE BARE `⟪δ⟫ × ⟪δ⟫ → ⟪δ⟫` SHAPE. ONE IS THE
PRODUCER AND THREE ARE CONSUMERS.**

| site | role |
|---|---|
| `src/L/Ordinal/SquareLaw.lagda.md:686` | PRODUCER. `sq`, the definition |
| `src/L/StageBound.lagda.md:39` | consumer. `SqFam`, and the one this row goes through |
| `src/L/BoundedSubset.lagda.md:1389` | consumer. `SqFam` is copied from it |
| `src/L/StageCardinal.lagda.md:18` | consumer, **and it is a MODULE PARAMETER** (`src/L/StageCardinal.lagda.md:15-19`) |

**THE FOURTH IS NOT MEASURED BY THIS TASK.** `L.StageCardinal` takes the bare
square law as a parameter of the whole module, so every definition in it is
under that parameter. My weakening works because ONE outermost consumer sits
inside one `PT.rec` whose goal is a proposition; it says nothing about whether
`StageCardinal`'s own conclusions are propositions. **Anyone who wants the same
cure there must re-measure it there.**

## THE OBLIGATION

```
sqat-or-what-it-wants :
    (zf : ModelL.isZFModel)
  → P550.AmbientCardAtSucc → SqCollectAt → P550.CoHyps
  → P564.StageCountedCoded
  → P558.SuccIntoPower zf
  → GCHStatement zf
```

`agents/tasks/LJ-1-571/Probe571.agda:193-199`. It is `gch-from-five`
(`agents/tasks/LJ-1-564/Probe564.agda:456-463`) with row 2 and only row 2
replaced. Four rows are copied letter for letter.

The chain under it, all of it green:

| term | `Probe571.agda` | what it does |
|---|---|---|
| `sq-pointwise-trunc` | `:126` | LEVEL 1 out of `src/`, not a hypothesis of anybody |
| `sqlaw-trunc-from-collect` | `:136` | LEVEL 1 to LEVEL 2, by `SqCollect` with its antecedent paid |
| `sqat-trunc-from-collect` | `:169` | the same at every ordinal L-cardinal |
| `power-into-succ-at-trunc` | `:176` | `Probe564.agda:351-361` under one `PT.rec` |

**THE WEAKENING IS CHECKED IN BOTH DIRECTIONS, because a weakening that cannot
be checked is a claim.**

- `sqat-gives-collect : P550.SqAt → SqCollectAt` (`Probe571.agda:214`). Nothing
  was strengthened and no new burden was smuggled in.
- `five-rows-recovered` (`Probe571.agda:220-226`) composes the two and its
  signature is `gch-from-five`'s type letter for letter. **So the weakened route
  loses nothing the five-row bill had.**

## DOES IT MEET LJ-1.567

**Three sentences, as the brief asks.** `[LJ-1.567]` is GO and its `col-step`
(`agents/tasks/LJ-1-567/Probe567.agda:259`) is a satisfaction fact about
`pr (fst c) (fst z) ∈ fst f`, an object-language statement whose whole purpose
is to make the collapse definable INSIDE `L`. This row is ambient at every
carrier, as the section above measures at four `file:line`s, and no term on its
path is ever asked to be coded, to be a member of `L`, or to be read by `⊨`.
**They do not meet on this row: `[LJ-1.567]`'s line of work is beside row 2 and
not on its critical path**, and the thing that would put it on the path is not
the square law at all but a well-order on the INJECTIONS
(`dev/literature/truncation-and-selection.md:323`), which is a different object
from `col`.

## W3, THE WIDEST UNMEASURED TERM

The brief names it "`SqLaw`'s own carrier", TYPE ONLY, and says it decides the
whole shape of the task. **It was written FIRST and typechecked ALONE, before
any other Agda of this task**, at `agents/tasks/LJ-1-571/runs/W3.agda`, 46
lines, two types written and NEITHER inhabited (`runs/W3.agda:38`, `:45`).

**GREEN ON THE FIRST RUN, exit 0** (`agents/tasks/LJ-1-571/runs/w3-1.out:22`).

**THE BRIEF ESTIMATED "about 10 lines, under 60 seconds". Measured: 46 lines
and 0.84 s** (`runs/w3-1.out:4`). The line estimate was low because the import
block is 20 of the 46; the time estimate was generous. I report the numbers I
measured and not the numbers the brief guessed.

**IT DID DECIDE THE SHAPE.** The first line of the unfolding is the answer to
D-10, and D-10 is what turned this task from "build a square law" into "find
which of two steps is real".

## THE RUNS

| run | what | result |
|---|---|---|
| `runs/w3-1.out` | W3 ALONE, 46 lines | exit 0, 0.84 s, 272 MB |
| `runs/s2-1.out` | sections 1 and 2, COLD | exit 0, 52.05 s, 2.87 GB |
| `runs/s4-1.out` | sections 3 and 4, the obligation lands | exit 0, 3.83 s, 826 MB |
| `runs/final-1.out` | **EXIT 143, SIGTERM** | see below |
| `runs/final-2.out` | rerun | exit 0, 3.28 s, 806 MB |
| `runs/final-3.out` | own `.agdai` deleted first | exit 0, 3.44 s, 806 MB |
| `runs/final-4.out` | after a comment-only citation fix, `.agdai` deleted | exit 0, 3.27 s, 806 MB |
| `runs/witness-1.out` | the program's obligation meter | pass, exit 0, 3.11 s |
| `runs/witness-2.out` | the same meter after the citation fix | pass, exit 0, 2.83 s |

**NO HEAP EVENT, AND I CHECKED RATHER THAN ASSUMED.** The largest resident set
was 2.87 GB against the 8 GB cap, on the cold run
(`agents/tasks/LJ-1-571/runs/s2-1.out:16`).

**`final-1` EXITED 143 AND I AM REPORTING IT RATHER THAN BURYING IT.** My slot
file says a heap exhaustion is a WALL event, to be reported and never simply
rerun. **This was not one, and here is the evidence.** Exit 143 is signal 15,
an external `Terminated`, not an Agda diagnostic. The peak was 495 MB of the
8 GB cap (`runs/final-1.out:6`), the log holds no heap message and no Agda
error at all, only `Checking LJ-1-571.Probe571` then
`time: command terminated abnormally` (`runs/final-1.out:3-4`), and it died at
1.90 s where the same file takes 3.3 s to pass. **I reran on that basis and I
say so here rather than presenting `final-2` as a first run.** `final-3`
repeats it with the interface deleted, so the green is not a cached artefact.

The cold 52.05 s is NOT this task's price. `LJ-1-564.Probe564` is imported
rather than transcribed, and it carries `LJ-1-550`, `LJ-1-558`, `LJ-1-528`,
`LJ-1-543`, `LJ-1-540` and `LJ-1-544` with it
(`agents/tasks/LJ-1-564/Probe564.agda:40-49`). **This file's own price is 3.44 s.**

## THE ESTIMATE AGAINST THE MEASUREMENT

The brief estimated "about 150 lines in the probe, of which the obligation is
about 35", and added "If the ambient law supplies it, far less, and I would
rather be wrong this way than fund a rebuild."

**Measured: 251 lines, of which 91 are code and 160 are comment or blank.** The
obligation and its whole chain, `sq-pointwise-trunc` through
`sqat-or-what-it-wants`, is about 42 lines of code. **So the code estimate was
close and the file is long because the reasoning is written down.** The brief's
hoped-for outcome, "the ambient law supplies it, finish early", **did not
happen**: the law is ambient but truncated, and that is a different answer from
either branch the brief anticipated.

## WHAT THIS EARNS AND WHAT IT DOES NOT

**EARNED.** Row 2 is strictly smaller. It was "the bare square law at every
ordinal L-cardinal, level 3". It is now "`SqCollect` at every ordinal
L-cardinal, level 1 to level 2", with level 1 paid out of `src/` and level 2 to
level 3 proved unnecessary. The two steps that separated `src/` from row 2 are
now ONE step, and it is a step `src/` already has a name and a written note for.

**NOT EARNED, AND NOBODY SHOULD CLAIM IT.** The bill is still five rows.
`SqCollectAt` is not inhabited in this file and no term of it appears
(`Probe571.agda:232-233`). Whether the set-indexed collection is provable,
refutable, or a new principle to be ruled on is not settled here; the digest's
checklist puts it at step 6, "expect to rule on it, because the literature
neither proves nor refutes a set-indexed instance"
(`dev/literature/truncation-and-selection.md:325-326`).

**THE ONE THING I WOULD PUT IN THE NEXT BRIEF.** The question is no longer
about squares. It is whether `LeastCardInjL` can deliver its injection
untruncated (`src/L/Cardinal.lagda.md:61-67`), because that is the single site
the truncation enters, and the digest says what it would take.

## W2 (from DD4)

The brief carries no generic-carrier instruction and this task writes no
mathematics at a fixed form. Every type in the probe is either copied letter for
letter from a predecessor probe or is `src/`'s own, and the one new abstraction,
the three-level ladder, is stated at a bound `α : SV.S` and instantiated at
`fst κ` rather than written twice (`Probe571.agda:126`, `:136`, `:169`). **No
conflict with W2 arose and there is nothing to report as a stop.**

## ARCHIVE USED

- `archive/dev/JOURNAL.md`. **READ AND USED.** `archive/dev/JOURNAL.md:941`
  reads "`⟪δ⟫ × ⟪δ⟫ → ⟪δ⟫` and nothing more. **The obligation is an INJECTION and not an".
  It is cited in `## AMBIENT OR INTERNAL` as independent confirmation of D-10.
- `archive/dev/LJ-dispatch-index.md`. **READ AND USED**, for premise 9.
  `archive/dev/LJ-dispatch-index.md:100` reads
  "| LJ-1.51 | Discharge the five hypotheses | 2 of 5, plus the sq master | fin-inj and Mext DISCHARGED. SquareLaw lands as a 775-line master. cover and levelIn survive on the hull adequacy |".
  It confirms the 775-line master the brief's premise names, and that `cover`
  and `levelIn` survived, which is why they are still hypotheses of `Tele.At`.
- `archive/dev/JOURNAL-archived.md`. **SEARCHED, NOT USED.** Its 25 hits on the
  square law are older campaign narrative; its "collection" hits are about the
  `hasInfinityL` collection step and the K-collection route at HF, a different
  object from `SqCollect`. Declined.
- `archive/dev/DD-archived.md`. **NOT USED.** Zero hits for the square law or
  `SqCollect`, and the `DD` series is set aside in this form by amendment A7.
  Declined.
- `archive/dev/ORCHESTRATION.md`. **NOT USED.** It is the archived operating
  document; its single square-law hit is not a mathematical fact. Declined.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`. **READ AND USED HEAVILY. It is
  the file this task turned on.** Three citations:
  `:289` reads "1. **Is the goal a proposition?** Then `PT.rec` applies and there is nothing to";
  `:146` reads "**The constraint the route carries: `P` must be `hProp`-valued.** So `leastOf`";
  `:323` reads "what is missing is a well-order on the INJECTIONS."
  The first licenses the level-3 to level-2 collapse, the second explains why the
  truncation enters at `LeastCardInjL`, and the third names the missing datum.
- `dev/literature/devlin-II5.md`. **NOT USED.** It is the Condensation Lemma
  and the GCH in Devlin II.5. This task changed no mathematical target: it
  measured which of two type-level steps is real on an already-stated row. No
  source-text question arose. Declined.
- `dev/literature/level-formula-slot-roles.md`. **NOT USED.** It is about the
  arity of the level-hood formula, an object-language question. D-10 measured
  this row as ambient, so no formula slot is in play here. Declined.
- `dev/literature/digest.md`. **NOT USED.** It pins the orthodox form of the
  rud route. Row 2 is not on the rud route. Declined.
- `dev/literature/terms-2026-08.md`. **NOT USED.** It is a terminology dossier
  for the owner's ruling. This task adds no term and I added no glossary entry.
  Declined.

## FILES

| path | state |
|---|---|
| `agents/tasks/LJ-1-571/Probe571.agda` | NEW, 251 lines, green, no postulate, no hole |
| `agents/tasks/LJ-1-571/lj-1.571-report.md` | NEW, this file |
| `agents/tasks/LJ-1-571/runs/W3.agda` | NEW, 46 lines, green, TYPE ONLY |
| `agents/tasks/LJ-1-571/runs/run.sh` | NEW, the one-process runner |
| `agents/tasks/LJ-1-571/runs/*.out` | NEW, nine run logs |

**NO `review-of-*.md` IS WRITTEN, and that is deliberate.** My slot file says
writing one is how a coder states a NO-GO. This is a GO on the obligation as
the brief's second disjunct defines it, so the file would be wrong and it would
route this return to a critic as a stop it is not.

Nothing was written under `src/`. Nothing was committed. Nothing was pushed.
`scripts/gate/check-probes.py`, `scripts/gate/lint-agda.py` and
`scripts/gate/check-fences.py` are clean on this tree.
