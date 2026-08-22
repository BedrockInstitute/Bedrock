# LJ-1.566 report: assemble `InjCode`, now that all four conjuncts exist

## HEAD
head_slot: coder
machine: shared
verdict: GO

## VERDICT

**GO. `injcode-assembled` is built, with no holes.**
`agents/tasks/LJ-1-566/Probe566.agda:492-500`, exit 0, caliber
`-A64m -I0 -M8g` taken from the pane, one Agda process at a time.
`runs/full-1.out`, `runs/full-2.out`, `runs/full-3.out`, `runs/full-final.out`
and `runs/cold-chain.out`.

    injcode-assembled :
        (a : S) (oa : IsOrd (fst a))
      → InjCode (Carve.G a oa) a (Carve.C a oa)

**THIS IS THE FIRST TERM IN THE TREE THAT IS AN `InjCode`.** The four
conjuncts are supplied together as one value, at one `F`, one `a` and one `b`.

**IT IS PINNED TO `InjCode` AND NOT TO MY TRANSCRIPTION.**
`runs/Pin.agda` projects the four conjuncts BACK OUT of the assembled term by
`InjCode`'s own projections and ascribes each at the type its predecessor was
briefed at; it also forms `∥ Σ[ F ∈ S ] InjCode F a (Carve.C a oa) ∥₁`, which
is the shape `IsCardinalL` quantifies over (`src/L/Cardinal.lagda.md:230-233`).
Exit 0, 1.71 s and 1.88 s over two runs (`runs/pin-1.out`,
`runs/pin-final.out`). It builds no new term.

**BUT THE BRIEF'S CENTRAL PREMISE WAS FALSE, AND THE TASK IS NOT THE TASK THE
BRIEF DESCRIBED.** Two things:

1. **`injAt` did not exist.** The brief's table says `[LJ-1.531]` built it and
   it is GO. `[LJ-1.531]` says "`injAt` IS NOT BUILT"
   (`agents/tasks/LJ-1-531/lj-1.531-report.md:34`). I built it, at
   `Probe566.agda:412-427`. Three conjuncts existed, not four.
2. **The assembly by tuple is refuted, and that is what killed `[LJ-1.547]`.**
   The brief says "the risk is one term's elaboration and not the assembly".
   The opposite is measured below: no two of the three delivered conjuncts can
   be put in one tuple, because their `F`s are three spellings of one carve and
   the elaborator cannot identify any two of them in the time available.

**SO THIS IS A GO THAT COST A REBUILD AND NOT A TUPLE.** The cure is
`[LJ-1.524]`'s measured law, ONE SPELLING, applied to the whole assembly: this
file carries one `rank-graph`, one `ordQ`, one `Bound′` and one `Carve`, and
re-proves the three delivered conjuncts at that one carve using the
predecessors' own proofs, moved and not reinvented. Every section of
`Probe566.agda` names whose proof it is at `file:line`.

**I did not write a `review-of-*.md`, because this is not a stop.** The
obligation is delivered. The false premise is recorded here, in the section the
brief required.

**NOTHING IS POSTULATED. NOTHING LANDED IN `src/`. `InjL` IS NOT FORMED, B10 IS
NOT TOUCHED AND `PowerIntoSucc` IS NOT TOUCHED.** `swo-rank`, the rank
`[LJ-1.497]` refuted, inhabits no term of any file of this task.

## THE FOUR FRAMES

**THEY DO NOT AGREE, AND ONE OF THE FOUR IS NOT A CONJUNCT AT ALL.** The brief's
table (`agents/tasks/LJ-1-566/LJ-1.566.md`, "ALL FOUR NOW EXIST AND ARE
COMMITTED") says `injAt zero` was built by `[LJ-1.531]` and is GO. `[LJ-1.531]`
says the opposite, in its own words: **"`injAt` IS NOT BUILT"**
(`agents/tasks/LJ-1-531/lj-1.531-report.md:34`), and again in the probe head,
`agents/tasks/LJ-1-531/Probe531.agda:52`.

My clause is that a hypothesis taken from a predecessor is the type that
predecessor DELIVERED. The delivered type is `rank-at′-inj`
(`agents/tasks/LJ-1-531/Probe531.agda:185-189`), an injectivity of the rank
FUNCTION. It is not `⟨ (F ∷ a ∷ []) ⊨ injAt zero ⟩` and it names no `F`.

| conjunct | `InjCode` line | delivered term | `F` it was delivered at | `a` | `b` |
|---|---|---|---|---|---|
| `svAt zero` | `src/L/Cardinal.lagda.md:225` | `P524.svAt-at-carve` (`Probe524.agda:263-266`) | `P524.Carve.G a oa bnd` (`:193-194`), **`bnd` a FREE parameter** (`:188`) | `a` | not named |
| `domAt zero (suc zero)` | `:226` | `P559.domAt-at-carve` (`Probe559.agda:336-339`) | `P559.Carve.G a oa` (`:260-261`), over `P559.Bound′` (`:108-137`) | `a` | not named |
| `injAt zero` | `:227` | **NONE** | **none: no `F`, because there is no term** | n/a | n/a |
| range clause | `:228` | `P529.range-clause` (`Probe529.agda:282-285`) | `P529.Carve.G a oa` (`:221-222`), over `P529.Bound′` (`:101-131`) | `a` | `P529.Carve.C a oa` (`:218-219`) |

**THE THREE `F`s THAT EXIST ARE THREE SPELLINGS OF ONE BODY, AND THAT IS THE
WHOLE OF THE DISTANCE.** Each of the three probes REBUILT `rank-graph` rather
than importing a sibling (`Probe524.agda:86`, `Probe529.agda:150`,
`Probe559.agda:146`), and each rebuilt `ordQ` (`Probe524.agda:106-107`, and the
same body in the other two). `[LJ-1.529]` and `[LJ-1.559]` each carry their own
`module Bound′`, and I diffed the two bodies: **they are byte-identical**
(`Probe529.agda:101-131` against `Probe559.agda:108-137`; the only text
`[LJ-1.529]` has that `[LJ-1.559]` does not is the separate `rank-bound′`
wrapper that follows the module). So the three `F`s are equal by unfolding, and
they are equal in no other way.

**AND THAT IS EXACTLY THE SHAPE `[LJ-1.524]` MEASURED AS UNPAYABLE.** Its price
finding is `Probe524.agda:160-171` and it is not a style note:

> MEASURED: with the obligation's type written as
> `SvAtOf (fst (rank-graph (ordQ a oa) a bnd)) a` while the proof produced
> `SvAtOf G a`, the file did not finish in ten minutes ... The SAME proof with
> one name throughout is seconds.

with the reason at `Probe524.agda:172-178`: `_⊨_` recurses on the FORMULA, so
comparing two satisfaction predicates walks down to
`pr (fst x) (fst y) ∈ fst γ₀`, and `_∈_` must put its right argument in
constructor form, which unfolds `rank-graph`, `hasSeparationL` and the
presentation.

**SO THE BRIEF'S ESTIMATE IS WRONG AND I SAY SO BEFORE SPENDING IT**, as the
brief's own D-10 instruction orders. The brief prices "about 200 lines, of which
the obligation is about 30 and the rest re-basing", against a risk it locates in
"one term's elaboration and not the assembly". The re-basing is not the cost and
the assembly is not free: the cost is a conversion between two spellings of the
carve inside a satisfaction predicate, and a predecessor has already measured
that conversion at over ten minutes at ONE site. There are two such sites here
(`svAt` and `domAt`), and a third obligation (`injAt`) that has no term at all.

**WHETHER THE CONVERSION IS PAYABLE IS A MEASUREMENT AND NOT A JUDGEMENT**, so
the next section measures it rather than assuming `[LJ-1.524]`'s number
transfers. A measured cure does not transfer by analogy (`AGENTS.md:45`) and
neither does a measured wall.

## THE FLOOR AND THE FINISH

**THE BRIEF ORDERS TWO NUMBERS, MEASURED. HERE THEY ARE**, both at caliber
`-A64m -I0 -M8g`, one Agda process at a time, and both with the `src/`
interfaces and the predecessor probes already cached, so that the pair is
comparable.

| number | file | seconds | exit | run |
|---|---|---|---|---|
| **THE FLOOR** | `runs/Floor.agda` | **1.67** | 42 | `runs/floor-1.out` |
| **THE FINISH** | `Probe566.agda` | **9.66** | 0 | `runs/full-final.out` |

**THE FLOOR IS THE ASSEMBLED TYPE WITH A HOLE AT EACH CONJUNCT.**
`runs/Floor.agda` carries this file's whole import set, `Bound′`, the carve's
separation, `ordQ`, the four conjunct type aliases, the four `InjCode`
projections and `injcode-in`, then states `injcode-assembled` at its real type
and writes `? ? ? ?` for the four conjuncts. So it prices the imports, the
elaboration of the four conjunct types at one `F`, and the conversion
`injcode-in` performs when it puts four things in a tuple. **Exit 42 is the four
unsolved interaction metas and nothing else** (`runs/floor-1.out`,
`[UnsolvedInteractionMetas]` at `Floor.agda:297.46-53`); the type elaboration
completes.

**SO THE ASSEMBLY ITSELF COSTS 1.67 SECONDS AND THE FOUR PROOFS COST 7.99.**
`runs/full-3.out` is the same measurement taken before the last comment-only
edit and reads 9.72 s, so the finish is stable to within a tenth of a second
across two runs.
The brief located the risk in "one term's elaboration". At the frame this file
built, no term is expensive: the finish is under ten seconds and the widest
single cost is spread across four proofs, none of which is the assembly.

**TWO MORE NUMBERS, because the next brief will want them.**

- **THE WHOLE PROBE CHAIN FROM NOTHING: 14.55 s**, exit 0
  (`runs/cold-chain.out`). `Probe521`, `Probe531`, `Probe537` and `Probe566`
  all re-elaborated from source with only the `src/` interfaces cached.
- **W3, THE FRAME FILE: 16.37 s cold, 1.46 s warm**, exit 0 both
  (`runs/w3-1.out`, `runs/w3-2.out`). The cold number is higher than the whole
  chain above because W3 imports `[LJ-1.524]`, `[LJ-1.529]` and `[LJ-1.559]`,
  which this file does not.

### W3: THE WIDEST UNMEASURED TERM, AND IT REFUTED THE ROUTE THE BRIEF NAMED

The brief names the widest unmeasured term as "whether the four conjuncts share
one `F`", orders it written FIRST and typechecked ALONE, and prices it at about
15 lines. It is `runs/W3.agda`, 56 lines with its head comment, and it is green
at 16.37 s: the four `F`s can be NAMED side by side at one frame.

**NAMING THEM IS NOT IDENTIFYING THEM, AND IDENTIFYING THEM IS THE WALL.**

| run | what it asks | limit | seconds | exit | file |
|---|---|---|---|---|---|
| `runs/Unify.agda` | all three `refl`s together | 540 s | 540.02 | 142 | `runs/unify-1.out` |
| `runs/U1.agda` | `[LJ-1.524]`'s carve `≡` `[LJ-1.529]`'s, at ONE shared bound | 240 s | 240.02 | 142 | `runs/u1.out` |
| `runs/U3.agda` | the two rebuilt BOUNDS alone, `[LJ-1.559]`'s `≡` `[LJ-1.529]`'s | 240 s | 240.00 | 142 | `runs/u3.out` |

**Exit 142 is my own cap and not a heap wall.** Peak resident set was 0.68 to
0.71 GB against a 8 GB caliber (`runs/u1.out`, `runs/u3.out`), and the process
was killed by a `perl` alarm because this machine carries no `timeout(1)`;
`runs/run.sh` is the wrapper. **No run of this task exhausted the heap.**

**`runs/U3.agda` IS THE NARROWEST SITE THERE IS AND IT STILL WALLS.** It is one
`refl` between `P559.Bound′.bnd a oa` and `P529.Bound′.bnd a oa`, and I diffed
those two module bodies: **byte-identical** (`Probe529.agda:101-131` against
`Probe559.agda:108-137`). Two textually identical definitions in two files do
not converge in four minutes.

**`runs/U2.agda` IS WRITTEN AND WAS NOT RUN.** It asks
`P559.Carve.G a oa ≡ P529.Carve.G a oa`, which is strictly harder than `U3`:
`U3`'s comparison is a proper part of it. I stopped after `U1` and `U3` because
a third eight-minute cap buys no new fact, and I record the decline here rather
than leave the file looking measured. **The file is tracked and never deleted;
it is the cheapest way for the next dispatch to check me.**

**WHY, AND `[LJ-1.524]` ALREADY KNEW.** `Probe524.agda:172-178`: `_⊨_` recurses
on the FORMULA, so comparing two satisfaction predicates walks down to
`pr (fst x) (fst y) ∈ fst γ₀`, and `_∈_` on the cumulative hierarchy must put
its right argument in constructor form, which unfolds `rank-graph`,
`hasSeparationL` and the presentation. `[LJ-1.524]` measured that at its own
site at over ten minutes (`Probe524.agda:164-167`) and wrote the law: **"The
SAME proof with one name throughout is seconds."**

**THIS TASK IS THAT LAW'S PRICE, PAID TWICE OVER, AND IT IS THE NUMBER THE
MATHEMATICIAN SHOULD CARRY:**

| the carve is spelled | seconds |
|---|---|
| twice, in one `refl`, at the narrowest site | **> 240, did not finish** |
| once, across four conjuncts and the assembly | **9.66, exit 0** |

**I re-measured it at this site rather than transferring `[LJ-1.524]`'s number**
(`AGENTS.md:45`), and I note that a measured WALL does not transfer by analogy
either: `[LJ-1.524]`'s ten minutes is its number, and mine are the three above.

## WHAT THE STATEMENT COST, AND WHAT RESISTED

**THE SHAPE THAT RESISTED IS NOT A MATHEMATICAL ONE.** No conjunct was hard to
re-prove and no conjunct turned out false. What resisted is the elaborator's
conversion between two names for one carve, and the whole of this task's
overrun is that one fact.

**THE FILE IS 500 LINES AND THE BRIEF PRICED 200.** The estimate was wrong in
the way I said it would be before spending it, and here is where the lines went:

| section | lines | whose work |
|---|---|---|
| head comment, saying why this file rebuilds | 1-73 | mine |
| imports and shifts | 75-117 | `[LJ-1.559]`'s set, plus `L.Coding.Injection` |
| 1. `Bound′` | 119-157 | `[LJ-1.529]`'s (`Probe529.agda:101-131`), moved |
| 2. the carve's separation, both readings | 159-183 | `[LJ-1.559]`'s (`Probe559.agda:146-178`), moved |
| 3. `ordQ`, `adequate-at-witness` | 184-199 | `[LJ-1.524]`'s (`Probe524.agda:106-115`), moved |
| 4. `rank-at′-irr` | 200-224 | `[LJ-1.524]`'s (`Probe524.agda:126-145`), moved |
| 5. four type aliases, four projections, `injcode-in` | 225-266 | the device is `[LJ-1.524]`'s and `[LJ-1.529]`'s, at four components |
| 6. `Write`, the writing direction | 267-299 | `[LJ-1.559]`'s (`Probe559.agda:212-238`), moved |
| 7.0 the shared reading | 338-364 | `[LJ-1.524]`'s (`Probe524.agda:206-228`), moved ONCE |
| 7.1 `svAt` | 366-384 | `[LJ-1.524]`'s (`Probe524.agda:230-255`), moved |
| 7.2 the range clause | 386-400 | `[LJ-1.529]`'s (`Probe529.agda:253-273`), moved |
| **7.3 `injAt`** | **402-427** | **MINE. It did not exist.** |
| 7.4 `domAt` | 429-462 | `[LJ-1.559]`'s (`Probe559.agda:288-330`), moved |
| 8, 9. the four names and the obligation | 464-500 | mine |

**THE ONE ECONOMY THAT ASSEMBLING AT ONE FRAME BUYS, MEASURED IN LINES.**
`sat`, `read`, `arg` and `val` (section 7.0) are carried by `[LJ-1.524]`,
`[LJ-1.529]` AND `[LJ-1.559]` separately, because each was alone in its file.
Here they are written once and spent by all four conjuncts. That is about 40
lines saved against a naive merge, and it is the only place the rebuild is
cheaper than the sum of its parts.

**`[LJ-1.531]` IS THE ONE PREDECESSOR CONJUNCT-TASK THIS FILE STILL IMPORTS,
AND THAT IS NOT AN ACCIDENT.** `rank-at′-inj` (`Probe531.agda:185-189`) names
no carve: it is a statement about `rank-at′` alone. So it survives the rebuild
untouched and saves the 81 code lines `[LJ-1.531]` measured. **A predecessor
whose delivered type does not mention the carve is reusable; one whose type
does is not.** That is the sharpest rule this task found, and section
"WHAT THE NEXT BRIEF SHOULD DO DIFFERENTLY" states it generally.

**`injAt` COST EXACTLY WHAT `[LJ-1.531]` PREDICTED, AND I RECORD THAT THE
PREDICTION HELD.** Its report said "one projection and three path compositions,
over five delivered terms" and marked it REASONING and not measurement
(`lj-1.531-report.md:240-248, 269`). `Probe566.agda:412-424` is three path
compositions (`ranks`, `members`, and the outer `arg ∙ members ∙ sym arg`) over
`read`, `val`, `arg` and `P531.rank-at′-inj`, and one projection: `arg`, which
`[LJ-1.529]` did not expose and `[LJ-1.531]` flagged as the one small surprise
for the next brief (`lj-1.531-report.md:249-254`). **It was the surprise it said
it would be, and it cost one line.**

## WHAT I HAD TO WEAKEN, AND WHAT I COULD NOT CLOSE

**I WEAKENED NOTHING IN THE OBLIGATION.** The four conjuncts are the four
components of `InjCode` at `src/L/Cardinal.lagda.md:224-228`, projected back
out of the assembled term in `runs/Pin.agda` and typechecked there.

**WHAT I DID NOT CLOSE, AND IT IS THE ONE THING A CONSUMER WILL WANT.** The
obligation is stated at `a` an ARBITRARY L-element with `IsOrd (fst a)`, and
`b` is `Carve.C a oa`, the bounding ordinal `boundingOrd` forms from the rank
(`Probe566.agda:140-143`). **`b` IS NOT CHOSEN AND IT IS NOT MINIMAL.** Nothing
in this task says that `C` is the least ordinal admitting a code, and
`IsCardinalL` (`src/L/Cardinal.lagda.md:230-233`) is about the absence of a code
below a cardinal, not about the presence of one. **So this term supplies a code;
it does not yet refute one.** A brief that wants the cardinal must say which of
the two it is asking for.

**I DID NOT TOUCH `InjL`, B10 OR `PowerIntoSucc`**, as the brief orders. AD12
gives this brief one obligation and it has one. `runs/Pin.agda` forms the
truncated existential `∥ Σ[ F ∈ S ] InjCode F a (Carve.C a oa) ∥₁` and stops
there: that is the shape `IsCardinalL` quantifies over, and it is NOT `InjL`
(`src/L/GCH.lagda.md:38`), which is a different truncation at a different
telescope.

## WHAT THE NEXT BRIEF SHOULD DO DIFFERENTLY

**A CONJUNCT DELIVERED AT ITS OWN SPELLING OF A SHARED OBJECT IS NOT A
DELIVERABLE THAT COMPOSES.** Four dispatches each built one conjunct, each
green on its own, and no two of them could be put in a tuple. The work was
real and none of it was wasted, but the FORM in which it was delivered had to
be rebuilt before it could be used, and the rebuild is 500 lines against four
green predecessors totalling more than that.

**THE CHEAP FIX IS ONE LINE IN A BRIEF, AND I PROPOSE IT AS A MEASUREMENT AND
NOT AS A RULE.** When a brief splits one object's conjuncts across dispatches,
it should name ONE file that defines the object and require every conjunct
task to IMPORT that definition rather than rebuild it. `[LJ-1.524]`,
`[LJ-1.529]` and `[LJ-1.559]` each declared the cross-task probe import and each
gave the argument for it (`Probe524.agda:19-31`, `Probe529.agda:16-30`,
`Probe559.agda:26-45`), so the mechanism was already available and already
argued; what was missing was a brief telling them WHICH definition was the
shared one. The measurement that would fund the rule is in this report: a
carve spelled twice does not converge in 240 s, and spelled once the whole
assembly is 9.66 s.

**I DO NOT PROPOSE IT AS A CLAUSE.** My slot file says a rule that binds a
coder and nobody else is proposed with its measurement and the owner rules it.
This one binds the mathematician who writes the briefs, not the coder, so it
goes in this report for the mathematician to weigh and not into
`dev/pod/instructions/coder.md`.

## CLAUSE W2

**THE BRIEF DID NOT STATE W2 AND THE CLAUSE SAYS IT SHOULD HAVE.** W2 requires
the brief to state the rule and the return to answer it; this brief states no
generic-carrier requirement anywhere. I record the omission and answer the
clause anyway.

**THE ANSWER IS THAT THE ONE PIECE OF THIS TASK THAT COULD LIVE AT A GENERIC
CARRIER ALREADY DOES, AND IT IS NOT MINE.** `[LJ-1.531]` wrote the injectivity
at the generic `SWO` (`Probe531.agda:166-170`, `swo-rank′-inj`) and instantiated
it, calling that clause W2 explicitly. This file consumes the instantiated form
`P531.rank-at′-inj` and adds no new mathematics at a carrier.

**MY OWN NEW TERM, `inj` (`Probe566.agda:412-424`), IS NOT GENERIC AND CANNOT
BE.** Its type mentions `Hold`, which mentions `G`, which is the carve, and the
carve is one object and not a family. There is no carrier to abstract over, and
abstracting over the carve is exactly the thing W3 measured as unpayable: a
`Carve`-parameterised statement would put a second spelling in scope at every
use site. **So W2 is satisfied vacuously here, and section 7.0 is the sharing
that a generic carrier would otherwise have bought**: one reading, four
consumers.

## CLAUSE W4

**NO MODULE RETIRED AND NOTHING WAS DELETED.** This task adds files under
`agents/tasks/LJ-1-566/` and changes nothing else; `git status --porcelain` is
exactly `?? agents/tasks/LJ-1-566/`.

**A QUESTION W4 MAKES ME ASK, AND I DO NOT ANSWER IT BECAUSE IT IS NOT MINE.**
Sections 1, 2, 3, 4, 6, 7.0, 7.1, 7.2 and 7.4 of `Probe566.agda` now carry, at
one frame, what `[LJ-1.524]`, `[LJ-1.529]` and `[LJ-1.559]` each carry at their
own. Those three probes are not retired by this: a probe is tracked and never
deleted, they are the evidence for the three verdicts this file rests on, and
`runs/U1.agda` and `runs/U3.agda` cite them as the measurement's subjects. **But
if a later task wants "the carve", there are now four files that define it and
this report says which one composes.** Whether that is a retirement question is
the mathematician's call and not mine.

## THE GATES I RAN

**FOUR INDIVIDUAL CHECKS, ALL EXIT 0**, run while the task was live as the
Boundary asks:

    check-probes: clean (6652 tracked files, no probe outside agents/tasks/
                         and no generated file)
    lint-agda:    exit 0, no output
    lint-prose:   exit 0, no output
    check-fences: clean (102 masters, run threshold 3)

`git status --porcelain` is exactly `?? agents/tasks/LJ-1-566/` and nothing
else. **I did not commit and I did not push.**

**THIS WORKTREE HAS NO `.venv`, AND `[LJ-1.529]` AND `[LJ-1.531]` EACH REPORTED
THE SAME FROM THEIR OWN** (`agents/tasks/LJ-1-531/lj-1.531-report.md:286-293`).
`ls .venv` returns "No such file or directory", so `make check` and every `make`
target that calls `.venv/bin/python` fail before they start. I ran the four
checkers with the system `python3` instead. **`AGENTS.md:75` says `make check`
is the gate before any commit; I am not committing, and the program that does
must run it from a tree that has the virtualenv.** I report the deviation
rather than assert a gate I did not run.

## THE RATIO BAR

**IT CANNOT FIRE ON THIS TASK AND THE COUNT IS 0.** My write scope is one raw
`.agda` probe, this report, the `runs/` directory and a `review-of-*.md` I did
not write. No `.lagda.md` master is in scope, so the in-fence line count of the
scope is 0, exactly as my role block states.

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md`, READ.** The line I read is
  `archive/dev/LJ-dispatch-index.md:142`, and it reads:

  > | LJ-1.75 | Give each partial only the facts its rows use | 43 of 69; 122.45 s | Better than proportional: 41.6 pc cheaper for a 37.7 pc smaller telescope. Two partials plus composer, 273.88 s |

  The brief cites this row for the import-trimming cure and says the price is
  old and nothing may be funded against it. **I took the method and not the
  number, and I report that the method did NOT apply here.** Trimming imports
  was not this task's lever: `runs/W3.agda` measures the import floor of the
  three predecessor probes at 1.46 s warm, so no trimming could reach the
  240 s wall. What trimming DID buy is stated in the file head
  (`Probe566.agda:44-58`): dropping `P524`, `P529` and `P559` entirely, not to
  save load time, but because importing them reintroduces the comparison that
  walls.
- **`archive/dev/JOURNAL.md`, DECLINED, not read.** It is the campaign
  narrative. This task's questions were all answerable from four predecessor
  probes and their reports, which are the primary evidence, and my clause tells
  me to take the type from the probe that typechecked and the verdict from the
  report. A journal entry is neither.
- **`archive/dev/JOURNAL-archived.md`, DECLINED, not read.** Same reason, and
  it is the older half of the same document.
- **`archive/dev/ORCHESTRATION.md`, DECLINED, not read.** It is the archived
  operating document for the loop, superseded by the program
  (`dev/memos/LJ-4-pod-program-design.md`). Nothing in it bears on whether two
  spellings of a carve converge.
- **`dev/ARCHIVE.md`, DECLINED, not used.** It is W4's record of retired
  modules. This task retires no module and deletes nothing, so it has no row to
  write there; the "CLAUSE W4" section above says so and says what question it
  leaves open for the mathematician.

## LITERATURE USED

- **`dev/literature/truncation-and-selection.md`, READ.** The line I read is
  `dev/literature/truncation-and-selection.md:146`, and it reads:

  > **The constraint the route carries: `P` must be `hProp`-valued.** So `leastOf`

  I read it because premise 9 of the brief says `InjL` is a truncated
  `InjCode`, and `runs/Pin.agda` forms a truncated existential of the assembled
  code. **It confirmed that stopping where I stopped is right:** the truncation
  in `Pin.agda` is introduced and never eliminated, so the `hProp` constraint
  this file records is not yet paid. A consumer that wants the code BACK out of
  `∥ Σ[ F ∈ S ] InjCode F a b ∥₁` owes that constraint, and this task does not
  discharge it.
- **`dev/literature/devlin-II5.md`, DECLINED, not used.** It is the
  Condensation Lemma and the GCH in `L`, read against DD4 and D-26. This task
  states no new mathematics: it assembles four conjuncts of a definition that
  is already in the tree at `src/L/Cardinal.lagda.md:223-228`. No step here
  needed a source.
- **`dev/literature/digest.md`, DECLINED, not used.** It pins the orthodox
  form of the rud route. This task touches no tower and no route question.
- **`dev/literature/geology.md`, DECLINED, not used.** Set-theoretic geology,
  for `[L6]`. Not this leg and not this campaign.
- **`dev/literature/primary-sources.md`, DECLINED, not used.** The Jensen,
  Devlin and Jech fetch round. Same reason as `devlin-II5.md`: nothing in this
  task is a mathematical claim needing a citation.

## THE FILES THIS TASK LEAVES

| file | what it is | exit |
|---|---|---|
| `Probe566.agda` | the obligation, 500 lines | 0 |
| `runs/W3.agda` | W3: the four `F`s side by side, type only | 0 |
| `runs/Unify.agda` | the three `refl`s together | 142, capped |
| `runs/U1.agda` | `[LJ-1.524]`'s carve against `[LJ-1.529]`'s | 142, capped |
| `runs/U2.agda` | `[LJ-1.559]`'s carve against `[LJ-1.529]`'s | **written, NOT RUN** |
| `runs/U3.agda` | the two rebuilt bounds alone | 142, capped |
| `runs/Floor.agda` | the assembled type with four holes | 42, the holes |
| `runs/Pin.agda` | the four conjuncts projected back out | 0 |
| `runs/run.sh` | the wrapper; the caliber is read, never set | |
| `runs/*.out` | every run above, with its caliber and its clock | |

**`runs/run.sh` NEVER SETS `GHCRTS`.** It echoes the pane's value into each
`.out` file so that every number in this report can be checked against the
caliber it was taken at, and every `.out` file carries the line
`GHCRTS=[-A64m -I0 -M8g]`. **One Agda process at a time, throughout.**
