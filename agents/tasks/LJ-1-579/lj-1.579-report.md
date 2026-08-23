# LJ-1.579 report: StageHigh once more, in a frame that fits under the cap

## HEAD
head_slot: coder
machine: shared
verdict: NO-GO

## VERDICT

**NO-GO on the obligation, AND THE ONE STATEMENT LEFT IS SMALLER THAN THE ONE
`[LJ-1.565]` LEFT.** `agents/tasks/LJ-1-579/Probe579.agda::stage-high` is not
inhabited and no postulate stands in for it.
`agents/tasks/LJ-1-579/review-of-stage-high.md` states the stop.

**ONE CAVEAT ON EVERY NUMBER BELOW, AND IT IS MINE TO DECLARE.** The head is
`machine: shared` and it was shared in fact: `ps` showed a SECOND Agda process
on this machine throughout the later runs, `agents/tasks/LJ-1-572/`, not mine
and not startable by me. **I started ONE Agda process at a time and never a
second.** The floor numbers and `runs/ctla-0.time` were taken before it
appeared; the 168 s and 220 s figures were taken beside it. **Treat the large
numbers as upper bounds.**

**THE PROBE IS GREEN AND IT CARRIES ELEVEN SECTIONS.** 451 lines, exit 0 on
each of THREE cold runs of the delivered file, at caliber `-A64m -I0 -M8g`
taken from the pane, one Agda process at a time.

| run | seconds | peak RSS | of the 8 GiB cap |
|---|---|---|---|
| `runs/full-t1.time` | 188.80 | 1,658,306,560 B | 19.31 % |
| `runs/full-t2.time` | **213.76** median | 1,658,273,792 B | 19.30 % |
| `runs/full-t3.time` | 218.52 | 1,658,306,560 B | 19.31 % |

**NOTHING WALLED IN THIS TASK AND NOTHING CAME NEAR THE CAP.** The interface
was removed before each run, and the file's MD5 was checked to be
`367fbe6bd329edc8888e864027b3d33f` before the first run and after the last, so
all three timed the SAME text that is delivered.

`Probe579.agda:445-447`:

    stage-high-from-definable-ih : LimitDefinableIH → StageHigh
    stage-high-from-definable-ih d =
      reduction (allH→all (closingIH (definable→limit-ih d)))

| what | where | price alone |
|---|---|---|
| the FLOOR, measured before any other Agda | `runs/W3.agda` | 1.94 s warm, **6.38 %** of the cap |
| the obligation is a BOUND and existence is FREE | `Probe579.agda:145-159` | 2.23 s (`runs/ctla-0.time`) |
| `[LJ-1.565]`'s chain, rebuilt and re-measured here | `:287-288` | 27.46 s, 7.07 % (`runs/Control579e.agda`, `runs/ctle-0.time`) |
| `[LJ-1.560]`'s reflection INSTANTIATED at this site | `:313-320` | **168.23 s, 17.4 %** (`runs/ctlb-1.time`) |
| at a limit the table is INSIDE the stage | `:360-380` | 12.78 s (`runs/ctld-0.time`) |
| and definability there pays the whole limit case | `:382-398` | 12.61 s (`runs/ctlc-1.time`) |

**THE ONE SENTENCE FOR THE NEXT BRIEF.** The limit case does not have to find a
bound. **The table already sits inside `Lset γ`, and what is missing is a
FORMULA that defines it there, with the tables below γ available to use.** That
is a different question from the one `[LJ-1.565]` recorded, it lands two stages
under budget, and it is the mathematician's to answer.

**AND THE RESIDUE CARRIES ITS INDUCTION HYPOTHESIS NOW.** `[LJ-1.565]`'s
`closing` discards the hypothesis at the limit case
(`../LJ-1-565/agents/tasks/LJ-1-565/Probe565.agda:307-308`), so its residue is
stronger than the proof needs. `dev/literature/devlin-II5.md:218-222` names the
form the source actually uses, and section 11 is the residue restated in it:
`HierBelowLimitIH` (`Probe579.agda:251-254`) and `LimitDefinableIH` (`:430-433`).
**One induction, not two**: the old form is derived from the new one at
`:279-280`, so nothing `[LJ-1.565]` proved is lost and nothing is paid twice.

## THE BRIEF'S PREMISE 1 IS WRONG, AND IT CHANGES THE TASK

**PREMISE 1 READS "`[LJ-1.565]` parked at the heap wall. Basis:
`dev/pod/transitions/2026-08.jsonl:3169`". THAT FILE HAS 157 LINES.** The
citation resolves to nothing. `grep -n "LJ-1.565" dev/pod/transitions/2026-08
.jsonl` returns no line either, so nothing in this worktree records that park.

**AND THE BRIEF'S "`[LJ-1.565]` LEFT A PARK AND NO REPORT" IS WRONG. IT LEFT
BOTH.** That task ran in a sibling worktree and its directory is untracked
there, so it is invisible from here unless you look:

| what | where |
|---|---|
| its report, verdict NO-GO | `../LJ-1-565/agents/tasks/LJ-1-565/lj-1.565-report.md:1-7` |
| its stop | `../LJ-1-565/agents/tasks/LJ-1-565/review-of-stage-high.md:1-9` |
| `stage-high-from-limit`, green | `../LJ-1-565/agents/tasks/LJ-1-565/Probe565.agda:327-328` |
| **it destroyed part of its own attempt 1's record** | its report, `## THE RECORD I DAMAGED` |

**WHAT THAT CHANGED HERE.** Nothing in that directory is importable from this
worktree, so sections 4 to 7 of this probe REBUILD its chain rather than cite
it, and every number in this report is measured on this pane. **The design and
the two cures are that task's and the credit is its own.**

**THE METHOD NOTE, AND IT IS THE SECOND TIME THIS CHAIN HAS PAID FOR IT.**
`[LJ-1.562]` had to say that a predecessor's W3 answered a question its report
never mentioned. Here a whole predecessor task's report was invisible to the
brief because it sits in another worktree. **A brief that says a task left
nothing should be checked against `ls ../<CODE>/agents/tasks/<CODE>/` before it
is believed.**

## THE FLOOR

**MEASURED FIRST, BEFORE ANY OTHER AGDA, AT CALIBER `-A64m -I0 -M8g` TAKEN
FROM THE PANE, ONE AGDA PROCESS AT A TIME.**
`agents/tasks/LJ-1-579/runs/W3.agda`, 44 lines, exit 0 on the FIRST run.

**A HOLE IS NOT AVAILABLE UNDER `--safe` and I did not drop the flag to buy
one**, because a number measured under a different flag set is not comparable
with the probe's. The floor is therefore the obligation's TYPE, FORMED, in the
trimmed frame. That is what an empty body costs.

| what | seconds | peak RSS | of the 8 GiB cap | run |
|---|---|---|---|---|
| cold, `[LJ-1.536]` and `[LJ-1.520]` rebuilt in the same process | **13.03** | **733,331,456 B** | **8.54 %** | `runs/w3-0.time` |
| warm, their interfaces present | **1.94** median of 1.94/1.93/1.95 | **547,700,736 B** | **6.38 %** | `runs/w3-t1.time`, `w3-t2.time`, `w3-t3.time` |

**THE FLOOR IS NOT NEAR THE CAP AND THE FRAME IS NOT THE OBSTACLE.** The brief
ordered: "If the floor is already near the cap, the obligation cannot be met in
this frame and you say so at once." It is not. At 6.38 percent warm, more than
nine tenths of the cap is left for the term.

**THE TRIMMED FRAME IS THREE IMPORTS**, and `StageHigh` is IMPORTED from
`[LJ-1.536]`, never restated (`runs/W3.agda:23-30`):

    Base.Prelude, Base.Classical (LEM), LJ-1-536.Probe536 (StageHigh; HierBelowAll; reduction)

**AND THE CHEAPEST TERM AT THAT TYPE IS ALREADY GREEN**, re-ascribed and not
restated (`runs/W3.agda:43-44`):

    floor-term : HierBelowAll → Obligation
    floor-term = reduction

## WHAT ACTUALLY BLOCKED IT

**THE OBLIGATION IS AN ORDINAL BOUND, AND THREE DISPATCHES HAVE BEEN SPENT
TREATING IT AS AN EXISTENCE.** `hierL γ` is an element of `S`, so it carries
`isL`, and `stage` (`src/L/Stage.lagda.md:180-193`) turns that into the LEAST
stage that holds it, with the membership and the minimality both projected out.
`Probe579.agda:145-150` is that, with no hypothesis, no induction, no limit
case and no reflection; and `:152-159` pins the obligation against that stage
from both sides, the bound buying `HierBelow` through `Lset-mono` and
`stage-earliest` refusing anything below it. **So what blocks `StageHigh` is
not that the table is hard to place. It is placed already. It is that the
place has to be under `step 3 γ`**, and `[LJ-1.560]`'s reflection certifies
`⟨ γ ∈ β ⟩`, a stage ABOVE the ordinal handed to it (`Probe579.agda:313-320`,
the certificate at `:317`). That is the wrong direction, and the type says so
without an argument.

## D-10, BEFORE ANY AGDA

The brief orders the floor first and I took it as the D-10: **is the target
true in this frame, or is the frame already spent?** The answer is in
`## THE FLOOR` and it is 6.38 percent.

**THE SECOND D-10 QUESTION IS THE ONE THAT PAID.** Before writing the chain I
asked what shape the obligation has, and the answer changed the task: it is a
bound and not an existence (`## WHAT ACTUALLY BLOCKED IT`). `[LJ-1.560]`'s
route was ordered tried by the brief, and this is why it cannot land: it
produces exactly the thing the tree already gives away.

**AND THE THIRD IS THE TARGET'S TRUTH AT THE LIMIT.** `[LJ-1.565]` recorded the
residue as an unbounded search. **The search is not what is unbounded.** At a
limit the whole table is inside `Lset γ` already (`Probe579.agda:360-380`), so
nothing has to be searched for. What is missing is a formula, and that is a
smaller and a different target. **A residue recorded under the wall protocol
names a TARGET, and a target can be re-priced.**

## W3, THE WIDEST UNMEASURED TERM

**THE BRIEF NAMES THE FLOOR ITSELF AND IT IS `runs/W3.agda`, WRITTEN FIRST AND
ALONE, BEFORE ANY OTHER AGDA OF THIS TASK.** 44 lines, exit 0 on the FIRST run.
The numbers are in `## THE FLOOR`.

**THE BRIEF ESTIMATED ABOUT 15 LINES AND DID NOT ESTIMATE THE NUMBERS, WHICH
WAS RIGHT.** The file is 44 lines because it carries the reason a hole was not
used, not because the term grew.

**WHAT IT SETTLED.** Three imports are enough to STATE the obligation, and
`[LJ-1.536]`'s green `reduction` is already a term at that type up to one
hypothesis (`runs/W3.agda:43-44`). So no part of the difficulty is in reaching
the statement.

## WHAT IS DELIVERED

### The floor, and it is the brief's first order

`runs/W3.agda`. See `## THE FLOOR`.

### That the obligation is a bound, not an existence

`Probe579.agda:145-159`, three rows, and `runs/Control579a.agda` is the three
alone at 2.23 s, exit 0 on its first run (`runs/ctla-0.time`).

    hier-somewhere : (γ : V ℓ) (oγ : IsOrd γ)
                   → Σ[ σ ∈ V ℓ ] (IsOrd σ × ⟨ hset γ oγ ∈ Lset σ ⟩)
    bound→hier     : ⟨ hstage γ oγ ∈ step 3 γ ⟩ → HierBelow γ oγ
    hier→bound     : HierBelow γ oγ → ⟨ step 3 γ ∈ hstage γ oγ ⟩ → Empty.⊥

### `[LJ-1.565]`'s chain, rebuilt in this worktree and re-measured

`Probe579.agda:167-288`. A MEASURED CURE DOES NOT TRANSFER BY ANALOGY
(`AGENTS.md:45`), and those two cures were measured in another worktree, so
they were re-measured at their own site here. **They hold.** The whole chain,
with sections 1 to 7 only, is exit 0 at **27.46 s and 607,617,024 B**, 7.07
percent of the cap, against that task's 26.92 s and 612 MB. **The frame fits
under the cap and it always did.**

**AND THAT NUMBER HAS A FILE THAT STILL MEASURES IT.** The probe grew after
`runs/full-0.time` was taken, so the state that run measured is preserved
verbatim as `runs/Control579e.agda` and re-run there
(`runs/ctle-0.time`). **A predecessor lost its evidence by overwriting it and I
am not repeating that.**

### `[LJ-1.560]`'s reflection, instantiated, and priced for the first time

`Probe579.agda:313-320`. The brief: "Try it here: nobody has."

    level-reflected : {n : ℕ} (w b : Fin n) (γ : V ℓ) (oγ : IsOrd γ)
      → Σ[ β ∈ V ℓ ] Σ[ oβ ∈ IsOrd β ]
          ( ⟨ γ ∈ β ⟩ × ((ρ : S ^ n) → Below β ρ → …) )
    level-reflected w b γ oγ = mkReflect (fst (levelFo-Σ₁ w b)) γ oγ

**IT INSTANTIATES, AND ON THE Σ₁ FORMULA `[LJ-1.536]` REFUTED AT `AtStage`,
WITH NO GRADE HYPOTHESIS AT ALL.** `runs/Control579b.agda` is that row alone:
exit 0, **168.23 s and 1,494,056,960 B, 17.4 percent of the cap**
(`runs/ctlb-1.time`). **No predecessor had a number for this.**

**AND IT DOES NOT REACH THE OBLIGATION.** See `## WHAT ACTUALLY BLOCKED IT`.
`LevelAtGamma` (`Probe579.agda:326-331`) is stated and not inhabited, to name
the sentence that would do instead.

### The limit case, re-priced, and it is the finding

**AT A LIMIT THE TABLE IS A SUBSET OF THE STAGE.** `Probe579.agda:360-380`,
exit 0 on its first run at 12.78 s (`runs/Control579d.agda`,
`runs/ctld-0.time`):

    hier-sub : (γ : V ℓ) (h : ⟨ isL γ ⟩) (o : IsOrd γ) → IsLimit γ
             → (z : V ℓ) → ⟨ z ∈ fst (hierL γ h o) ⟩ → ⟨ z ∈ Lset γ ⟩

Every member is `pr c (Lset c)` for c ∈ γ (`src/L/Hierarchy.lagda.md:497-502`),
that pair lies in `Lset (step 3 c)` (`agents/tasks/LJ-1-536/Probe536.agda
:163-164`), and a limit is closed under the successor three times over.

**AND DEFINABILITY OVER THAT STAGE PAYS THE WHOLE CASE.**
`Probe579.agda:382-398`, 12.61 s alone (`runs/Control579c.agda`,
`runs/ctlc-1.time`):

    LimitDefinable = (γ : V ℓ) (h : ⟨ isL γ ⟩) (o : IsOrd γ) → IsLimit γ
                   → Door (Lset γ) (fst (hierL γ h o))
    definable→limit : LimitDefinable → HierBelowLimitH

`Door` is `𝒟ₒ-intro`'s own premise (`agents/tasks/LJ-1-536/Probe536.agda
:76-80`) and that door asks for a formula at `⟪ Lset γ ⟫` and nothing else,
which is `[LJ-1.565]`'s `door-free` finding.

**IT LANDS AT `sucV γ` AND THE OBLIGATION ALLOWS `step 3 γ`. DEVLIN'S THREE IS
SLACK AT THE LIMIT**, by two stages, and no predecessor reported that.

### The obligation, from one statement

`Probe579.agda:412-413` and `:445-447`. `stage-high` itself is NOT written and no postulate
stands in for it.

## FOR THE NEXT BRIEF

**1. THE TASK IS NOW A FORMULA, AND IT IS ONE OBLIGATION.** Exhibit
`φ : Formula ⟪ Lset γ ⟫ 1` with `DefOf.defSet (Lset γ) φ ≡ fst (hierL γ h o)`
at a limit γ. That is `LimitDefinable` (`Probe579.agda:382-384`), and it may USE the tables
below γ, which is `LimitDefinableIH` (`:430-433`). Either one becomes
`StageHigh` in one line (`:412-413`, `:445-447`).

**2. WHAT THE TREE HAS AND WHAT IT DOES NOT.** It has the level formula at the
CLASS carrier and BOTH directions of its correctness there:
`Lset-defines` (`src/L/Hierarchy.lagda.md:646-653`) and `Lset-only` (`:334`).
**It does not have that formula's correctness read inside `Lset γ`.**
`AtStage` refuses it for want of a `Δ₀` grade `[LJ-1.536]` refuted
(`agents/tasks/LJ-1-536/Probe536.agda:115-116`), and `mkReflect` gives it at a
DIFFERENT stage (this task, `:313-320`). **Neither is the one needed.**
`[LJ-1.536]` reports `AtStage` as the tree's only external-to-inner bridge
(its report, `## The second door, which no predecessor named`) and I found no
third, **but I did not run an exhaustive sweep for one and I do not claim the
list is closed.**

**3. DO NOT FUND ANOTHER "BOUND THE SEARCH" TASK AT THIS SITE.** The bound is
free (`:145-150`) and reflection's output is the free thing. That is measured,
not argued.

**4. THE 17.4 PERCENT IS THE NUMBER TO PLAN THE NEXT FRAME AGAINST.** Importing
`[LJ-1.520]`'s level formula and `L.ReflectFo` together costs 168.23 s and
1.49 GB before any new term. The whole probe with it is 219.87 s and 1.66 GB.
**A task that needs the level formula AND the full chain starts at one fifth of
the cap.**

**5. ONE THING I DID NOT MEASURE AND DO NOT CLAIM.** Whether `LimitDefinable`
is TRUE. `hier-sub` is a subset fact and nothing more. I did not attempt the
formula and I have no evidence about its cost.

## THE RUNS, AND WHAT EACH ONE MEASURED

**EVERY `.time` IN `runs/` IS LISTED, BECAUSE A `.time` WHOSE FILE HAS MOVED ON
IS A TRAP.** `[LJ-1.565]` lost part of its predecessor's record that way
(its report, `## THE RECORD I DAMAGED`).

| run | what it measured | still reproducible from |
|---|---|---|
| `w3-0.time` | the floor, cold | `runs/W3.agda`, unchanged |
| `w3-t1..t3.time` | the floor, warm | `runs/W3.agda`, unchanged |
| `ctla-0.time` | the three bound rows alone | `runs/Control579a.agda` |
| `ctlb-0.time` | the reflection row, FAILED, universe level | `runs/Control579b.agda` before its one-line fix |
| `ctlb-1.time` | the reflection row alone, green | `runs/Control579b.agda` |
| `ctlc-0.time` | the limit reduction, FAILED, wrong `self∈sucV` argument | `runs/Control579c.agda` before its one-line fix |
| `ctlc-1.time` | the limit reduction alone, green | `runs/Control579c.agda` |
| `ctld-0.time` | the subset row alone | `runs/Control579d.agda` |
| `ctle-0.time` | the chain, sections 1 to 7 | `runs/Control579e.agda` |
| `full-0.time` | the probe when it held sections 1 to 7 | **preserved as `runs/Control579e.agda`** |
| `full-1.time` | the probe when it held sections 1 to 10, before section 11 | **NO PRESERVED FILE. Do not cite it.** 219.87 s, 1,657,372,672 B |
| `full-t1..t3.time` | **the delivered probe**, MD5 `367fbe6bd329edc8888e864027b3d33f` | `Probe579.agda` |

**TWO RUNS RECORD A FAILURE AND THEY ARE KEPT.** `ctlb-0` and `ctlc-0` are the
two rows that did not compile first time, both for a reason that was not
mathematical: a universe level and a wrong argument to `self∈sucV`. Neither
cost a rebuild of anything else.

## C-42, THE SWEEP

**THE LAW.** A finding measures ONE site and says nothing about how far the
shape extends, so the count comes before any cure
(`dev/LESSONS.md:3752`).

**THE SHAPE I FOUND IS "an obligation written as membership in a stage at a
FIXED FINITE OFFSET", which is what makes it a bound rather than an
existence.** Its spelling in this tree is `∈ Lset (step n …)`.

**THE COUNT IS THREE FILES AND TWELVE ROWS, AND ALL THREE ARE THIS LEG.**

| where | rows |
|---|---|
| `agents/tasks/LJ-1-519/Probe519.agda` | 3 |
| `agents/tasks/LJ-1-536/Probe536.agda` | 5 |
| `agents/tasks/LJ-1-579/Probe579.agda` | 4 |
| **`src/`** | **0** |

**SO THE SHAPE DOES NOT EXTEND PAST THIS LEG AND NOTHING IN `src/` CARRIES IT.**
No cure has to be priced anywhere else, and that is the useful half of the
answer.

**AND THE COUNTER-SWEEP SAYS THE TREE ALREADY KNEW THE CURE.** `stage`,
`stage-mem` and `stage-earliest` (`src/L/Stage.lagda.md:180-193`) are used in
**11 files under `src/`** and in **31 task probes**. This leg is the exception
that did not reach for them: of the probes carrying an `∈ Lset (step n …)`
obligation, `[LJ-1.519]` and `[LJ-1.536]` name no part of `L.Stage`, and
neither does `[LJ-1.565]`'s
(`../LJ-1-565/agents/tasks/LJ-1-565/Probe565.agda`, zero hits for `L.Stage`,
`stage-mem` and `stage-earliest`). **`[LJ-1.541]` and `[LJ-1.547]` LEFT NO
PROBE TO CHECK**: neither `agents/tasks/LJ-1-541/` nor
`agents/tasks/LJ-1-547/` exists here or in a sibling worktree, which confirms
the brief's premise 10 from a second place.

**WHAT THE COUNT DOES NOT SAY.** It is a count of one spelling. A site that
writes the same bound another way would not appear in it, and I did not search
for other spellings.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`. **READ.** Line 142 reads:
  `| LJ-1.75 | Give each partial only the facts its rows use | 43 of 69; 122.45 s | Better than proportional: 41.6 pc cheaper for a 37.7 pc smaller telescope. Two partials plus composer, 273.88 s |`
  The brief cites this line for `[LJ-1.75]`'s trimming cure and warns that
  nothing may be funded against it. **THE METHOD WAS USED AND THE PRICE WAS
  NOT**: `runs/W3.agda` is the smallest import set that states the obligation,
  three imports, and its own number was measured here.
- `archive/dev/JOURNAL-archived.md`. **NOT READ.** Declined. This task's
  predecessors are all live tasks under `agents/tasks/` and a sibling worktree,
  and their reports are the evidence. A journal would only be history.
- `archive/dev/JOURNAL.md`. **NOT READ.** Declined, same reason.
- `archive/dev/DECISIONS-archived.md`. **NOT READ.** Declined. The brief names
  AD12 and clause W2, and both live in `dev/memos/LJ-4-pod-program-design.md`;
  the archived `D<n>` series is not in force.
- `archive/dev/ORCHESTRATION.md`. **NOT READ.** Declined. It is archived and
  this task turns on Agda evidence, not on how the loop is operated.

## LITERATURE USED

- `dev/literature/devlin-II5.md`. **READ, AND IT CHANGED THE DELIVERABLE.**
  Line 217 is the line `[LJ-1.565]`'s stop cites for the limit case, and it
  reads:
  `   Strength: the existential over z is UNBOUNDED at the ambient level.`
  **THAT IS ABOUT ITEM 1, THE AMBIENT FORM. ITEM 2, AT LINE 218, IS THE ONE
  THE LIMIT CASE ACTUALLY USES**, and it reads:
  `2. Uniform Δ₁ at limit α > ω (`dev2.txt:674-686`, 2.6-2.7): for γ < α,`
  with lines 220 to 222 naming its hypothesis: the forward half needs the
  witnessing z inside L_α, "that is 2.6(ii), the sequence (L_δ | δ ≤ γ) ∈ L_α
  for γ < α". **THAT IS THE INDUCTION HYPOTHESIS**, and section 11 of the probe
  is the residue restated with it, which no predecessor did.
- `dev/literature/truncation-and-selection.md`. **NOT READ.** Declined.
  Nothing in this task truncates or selects; the one `PT.rec` is at an `hProp`
  target and needs no choice.
- `dev/literature/digest.md`. **NOT READ.** Declined, a summary of the others.
- `dev/literature/geology.md`. **NOT READ.** Declined. Set-theoretic geology
  is not this site.
- `dev/literature/terms-2026-08.md`. **NOT READ.** Declined. This task adds no
  term to `dev/glossary.toml` and proposes none.
