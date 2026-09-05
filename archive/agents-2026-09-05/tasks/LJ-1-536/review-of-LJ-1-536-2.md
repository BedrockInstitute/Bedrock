# LJ-1.536: adversarial review of LJ-1.536#2

## HEAD
head_slot: mathematician_adversarial
machine: shared
verdict: upheld
attacked: agents/tasks/LJ-1-536/review-of-LJ-1-536-1.md
instance: LJ-1.536#2, role coder_adversarial, model grok-4.6, effort high, heads_sha256 d5caf66f

## WHICH RETURN IS NUMBER 2

The return under attack is `agents/tasks/LJ-1-536/review-of-LJ-1-536-1.md`.
Its brief `agents/tasks/LJ-1-536/review-LJ-1-536-1.md:11` says `Attack the
return of LJ-1.536#1`. Number 1 is the coder pair
`agents/tasks/LJ-1-536/lj-1.536-report.md` and
`agents/tasks/LJ-1-536/review-of-StageHigh.md`. This brief says
`Attack the return of LJ-1.536#2`. The second return in the
directory is that critic file. This dispatch did not write it.

The critic file's HEAD at `review-of-LJ-1-536-1.md:6` reads
`verdict: upheld`. It upheld the coder's NO-GO. This review upholds
that upholding.

A prior dispatch of this same brief already wrote this path
(`dev/pod/transitions/2026-08.jsonl` seq 2856, pid 32880, role
`coder_adversarial`). This dispatch is seq 3013, role
`mathematician_adversarial`. It overwrites the path. It still
attacks the critic file, not that prior file.

## THE RECORD

The worktree copy of `dev/pod/transitions/2026-08.jsonl` ends at seq
158, task `LJ-1.399` (`dev/pod/transitions/2026-08.jsonl:158`). A
search of that copy for `LJ-1.536` returns no row. The live record
is the main tree copy
`/Users/alsg/Agentic/Bedrock/dev/pod/transitions/2026-08.jsonl`.
Every transition cite below names that file. The six facts of the
run under attack also sit in this checkout at
`agents/tasks/LJ-1-536/runs/accept-4.out`, newest last, as this
brief ordered.

- Seq 2620 dispatches the coder: model `claude-opus-5`, effort
  `xhigh`, `heads_sha256` `d5caf66f`, `obl_before` 1, `tier` wide,
  pid 51064.
- Seq 2722 returns it (`why` `pid dead`).
- Seq 2725 records the coder harvest and matches
  `task-lj-1-536-heap-wall-escalate`. The six facts agree with
  `runs/accept-1.out`: `exit_code` 251, `error_class` `heap_wall`,
  `heap_wall` true, `lines` 0, `obligations_delta` -1,
  `obligations_open` 0, `seconds` 697.19, caliber `-A64m -I0 -M8g`,
  `concurrency` 4. `runs/accept-1.out:16` reads
  `run agents/tasks/LJ-1-536/Probe536.agda rc 0 seconds 1.97`.
  `runs/accept-1.out:20` reads
  `run agents/tasks/LJ-1-536/runs/Control536d.agda rc 251 seconds 697.19`.
  `runs/accept-1.out:23` reads `# obligations delta -1`.
  `runs/accept-1.out:26` reads `# exit 251`.
- Seq 2727 dispatches the first critic: model `grok-4.6`, effort
  `high`, brief `review-LJ-1-536-1.md`, `obl_before` 0, pid 13954.
- Seq 2754 returns that dispatch. Seq 2757 harvests it onto
  `runs/accept-2.out`: `Control536d.agda rc 251 seconds 781.54`
  (`accept-2.out:20`), `obligations_delta` 0 (`accept-2.out:23`),
  `heap_wall` true, `concurrency` 4.
- Seq 2779 re-dispatches the same review brief as attempt 2, pid
  49482. Seq 2792 returns it. Seq 2796 harvests it onto
  `runs/accept-3.out` and again matches
  `task-lj-1-536-heap-wall-escalate`.
- Seq 2856 is the prior dispatch of this brief, pid 32880, role
  `coder_adversarial`, run `accept-3.out`. Seq 2897 harvests it onto
  `runs/accept-4.out`.
- Seq 3013 is this dispatch: attempt 3, brief
  `review-LJ-1-536-2.md`, model `grok-4.6`, effort `high`,
  `heads_sha256` `d5caf66f`, role `mathematician_adversarial`, run
  `accept-4.out`, pid 28961.

The newest accept arm, `runs/accept-4.out`, is the run this review
attacks. It started 2026-08-23 00:26:30. `accept-4.out:5` is
`# GHCRTS -A64m -I0 -M8g`. `accept-4.out:7` is `# agda slots during 3`.
`accept-4.out:16` is `Probe536.agda rc 0 seconds 2.0`.
`accept-4.out:20` is `Control536d.agda rc 251 seconds 638.45`.
`accept-4.out:23` is `# obligations delta 0`. `accept-4.out:26` is
`# exit 251`. The JSON facts at the foot repeat `heap_wall` true,
`obligations_open` 0, `concurrency` 3. The changed-files list
includes `review-of-LJ-1-536-1.md`. The predecessor could not have
read this file. This review did.

The worktree `.pod` file records `heads=d5caf66f`
(`agents/tasks/LJ-1-536/.pod:1`). The instance in the record and the
worktree on disk are the same one.

I did not set `GHCRTS`. I did not start an Agda process. The numbers
below are the recorded runs and the files they name. A heap
exhaustion is a WALL event. `Control536d.agda` walled under harvest
four times (`accept-1.out:20`, `accept-2.out:20`, `accept-3.out:20`,
`accept-4.out:20`). I do not rerun it.

## THE INVARIANT

The author of the NO-GO is the coder head, model `claude-opus-5`,
pid 51064 (seq 2620). The author of the return under attack is the
attempt-2 critic, model `grok-4.6`, pid 49482 (seq 2779). This
critic is seq 3013, pid 28961, role `mathematician_adversarial`,
model `grok-4.6`. This dispatch authored neither the coder pair nor
`review-of-LJ-1-536-1.md`.

This critic and the predecessor share the model `grok-4.6`. They do
not share the slot. DD25 pairs an author slot with its critic
(`archive/dev/DD-archived.md:35`). The author of the work under the
NO-GO is the coder head, which no link in this chain shares. The
program seated this dispatch at seq 3013. The critic is not the
author of the NO-GO.

## QUESTION 1. DOES THE PREDECESSOR'S VERDICT LINE MATCH ITS OWN BODY

It does. The 375/376 defect class is absent.

The line at `agents/tasks/LJ-1-536/review-of-LJ-1-536-1.md:6` reads
`verdict: upheld`. The body supports that line at every joint this
review could re-open.

- Its own Question 1 closes on the coder's NO-GO. The coder line at
  `lj-1.536-report.md:3` reads `VERDICT: NO-GO, AND IT IS A NO-GO AT
  THE DOOR.` The stop file at `review-of-StageHigh.md:3` reads
  `**NO-GO.**` Both say `StageHigh` is stated and not inhabited.
  That is still true today. `StageHigh` stands at
  `Probe536.agda:350-352` as a `Type`. No constructor, no hole, and
  no `postulate` inhabits it. A search of that file for `postulate`
  returns one comment at `:345` and no declaration. The delivered
  term `reduction` at `:357-358` has type `HierBelowAll → StageHigh`.
  A function from an undischarged hypothesis is not an inhabitant of
  `StageHigh`.
- Its own Question 2 names five loose addresses in the coder and
  says none of them reach the NO-GO. Each of those five still opens
  at the line this review checked (Question 2 below). The body does
  not promote any of them into an overturn.
- Its own Question 3 finds the four-route table complete, the word
  `door` overclaimed against `𝒟ₒ-intro`, and `successor-step`
  missing as a green term. The close of that question is that none
  of those gaps inhabit `StageHigh`.
- The four DD25 questions (written there under a `SECTION 6.6`
  heading at `review-of-LJ-1-536-1.md:244-334`) restate the same
  close: the NO-GO is correct on the numbers, the qualifier `AT THE
  DOOR` is stronger than `𝒟ₒ-intro` needs, and no cheap cure
  inhabits the obligation.

The predecessor's line is `upheld`, not a restatement of `NO-GO`.
The body never says `overturned`. It never treats the meter closing
(`obligations_delta` -1 on `accept-1.out:23`) as a GO. That is not
a line against body. It is the predecessor naming a harvest fact
and leaving the mathematical verdict in place.

The qualifier `AT THE DOOR` on the coder line is the one place the
predecessor spends a correction. That correction is in the body,
and the line `upheld` still holds, because the predecessor priced
the qualifier as not load-bearing for GO versus NO-GO. This review
re-derived that price (Question 3) and agrees.

## QUESTION 2. IS EVERY LOAD-BEARING CLAIM BACKED BY A FILE:LINE THAT RESOLVES TODAY

Two classes. The first is the predecessor's own load-bearing
claims. They resolve. The second is a small reporting looseness of
the same kind the predecessor named in the coder. None of it reaches
`upheld`.

**CLEAN, re-opened this session, not taken from the predecessor's
list.**

The obligation and the residue.

- `Probe536.agda:350-352` (`StageHigh` as a `Type`).
- `:357-358` (`reduction : HierBelowAll → StageHigh`).
- `:362-364` (`reduction-at`).
- `:186-187` (`HierBelow`).
- `:297` (`module Adjoin`).
- `:366-387` (the unwritten `successor-step`, comments only).
- `:408-409` (`HierBelowLimit`, stated and not inhabited).
- `.pod-state/witness/Witness-LJ-1-536-345734cd.agda:28` is
  `witness = Target.StageHigh`. The name exists. The type is empty
  of a term.

The door split, which is the predecessor's main correction.

- `src/L/Constructible.lagda.md:301-304` (`𝒟ₒ-intro` wants
  `∥ Σ[ φ ∈ Formula ⟪ A ⟫ 1 ] (DefOf.defSet A φ ≡ x) ∥₁` and names
  no `Δ₀`).
- `:319` (`Lset-in`).
- `:211-213` (`opaque` on `𝒟ₒ`). `:221-223` (`opaque` on `Lset`).
  The predecessor's defect table against the coder at
  `review-of-LJ-1-536-1.md:164` still holds: the coder cited `:211`
  and `:221` together for `Lset`.
- `:396-397` (`Lset→isL`). The predecessor cited `:395-396` at
  `review-of-LJ-1-536-1.md:92-93`. Line 395 is the fence. The name
  is at `:396`.
- `src/L/Definability.lagda.md:111-112` (`defSet`). `:146-147`
  (`defSet-mem`, inner satisfaction).
- `src/L/Axioms/Separation.lagda.md:119` (`module AtStage`).
  `:150-153` (`satBridge` takes `Δ₀`). `:198-199` (`carve∈𝒟ₒ`
  takes any `Formula ⟪ Lset σ ⟫ 1` and sends it to `𝒟ₒ` with
  `refl`, no `Δ₀`). `:205-206` and `:219-230` (`carveOut` /
  `imageIn` / `imageOut`, these do demand `Δ₀` and `BoundedFo
  Below`).
- `src/FOL/LevyHierarchy.lagda.md:47-57` (`Δ₀`; no constructor for
  unbounded `∃̇`).
- `Probe536.agda:76-80` (`Door` ascribed to `𝒟ₒ-intro`).
- `:115-116` (`no-Δ₀-levelFo`).
- `:159-161` (`Lset∈suc`, `𝒟ₒ-intro` on `⊤̇`).
- `:278-280` (`adjoin∈` calls `𝒟ₒ-intro` on a formula written over
  the stage).
- `runs/W3.agda:65-66` (`door`). `:94-95` (`no-Δ₀-levelFo`).
  `:115-116` (`b-carve∈ = carve∈𝒟ₒ`). `:130-140` (`b-in` / `b-out`
  take `Δ₀`). `:153-157` (`adjoin`, `Δ₀-adjoin`).
- `agents/tasks/LJ-1-520/Probe520.agda:163-165` (`levelFo` is
  thirteen `∃̇` at `:164`). `:171-172` (`levelFo-Σ₁`).
- `agents/tasks/LJ-1-520/runs/CountCheck.agda:18-19` (`countFo … ≡ 0`
  by `refl`).
- `src/FOL/Manipulation/Relabelling.lagda.md:117-118` (`embed`).
- `src/FOL/Count.lagda.md:598` (`erase`). The predecessor's defect
  table against the coder at `review-of-LJ-1-536-1.md:165` still
  holds.
- `src/FOL/Manipulation/Bounding.lagda.md:67` (`BoundedFo`).

The four routes.

- `agents/tasks/LJ-1-519/Probe519.agda:148-150` (`HierInStageLimit`).
  `:200-202` (`steps-stay` takes `n : ℕ`). `:208-210`
  (`stage-below` likewise). `:218-220` (`StageHigh`). `:235`
  (`reduction : StageHigh → StageLow → HierInStageLimit`). `:239`
  and `:241` (the `n = 5` spends). `:243` (the `n = 4` spend).
- `agents/tasks/LJ-1-532/Probe532.agda:274-277` (`HierInK`).
  `:346-349` (`hier-is-approx`).
- `agents/tasks/LJ-1-494/lj-1.494-report.md:66-67` (the tree does
  not bound `hierL δ` by `α`).
- `agents/tasks/LJ-1-532/lj-1.532-report.md:45` (the `K`-is-a-level
  gap stays open).

The 494 census, re-opened in `src/` this session. A search of
`src/` for `fst (hierL` returns no match. `hierL` is defined at
`src/L/Hierarchy.lagda.md:621-622` and specified at `:624-626`. No
master states `⟨ fst (hierL …) ∈ Lset … ⟩`. The predecessor cited
the 494 report and did not re-run the search. The gap is still
there. If that membership had landed, `reduction` at
`Probe536.agda:357-358` would inhabit `StageHigh` without
`successor-step`. It has not landed.

The AtStage name collision, which the predecessor named.

- `agents/tasks/LJ-1-230/ProbeLJ1230A.agda:38` and
  `agents/tasks/LJ-1-494/Probe494.agda:24` import `L.Hull.AtStage`.
- `lj-1.230-report.md:189` and `lj-1.494-report.md:246` write that
  name.
- A search of `LJ-1-517`, `LJ-1-530` and `LJ-1-532` for
  `Axioms.Separation` returns no match.

The walls and the green times, which the predecessor used as numbers.

- `runs/full-t1.time:1` is `12.45 real`. `runs/full-t2.time:1` is
  `12.20 real`. `runs/full-t3.time:1` is `12.56 real`. The median of
  those three is 12.45 s. `runs/full-t2.out:1` starts
  `Checking LJ-1-536.Probe536`. The predecessor's defect table at
  `review-of-LJ-1-536-1.md:163` still holds: the coder cited
  `full-t2.out` as if it were the median clock.
- `runs/w3-t1.time:1`, `runs/w3-t2.time:1` and `runs/w3-t3.time:1`
  each read `1.82 real`. `runs/w3-0.out:1` starts
  `Checking LJ-1-536.runs.W3`. `runs/w3-0.time:1` is `2.05 real`,
  rss `608141312`.
- `runs/ctl-0.time:1` is `1.00 real`, rss `298909696`.
  `runs/ctlb-0.time:1` is `11.07 real`. `runs/ctlc-0.time:1` is
  `11.20 real`. `runs/full-3.time:1` is `11.13 real`.
- `runs/ctle-0.time:1` is `425.73 real`, rss `371900416`.
  `runs/ctlf-0.time:1` is `417.18 real`, rss `350928896`.
  417.18 / 425.73 is 0.9799, so the predecessor's "98 percent is
  `sucV`" arithmetic at `review-of-LJ-1-536-1.md:251-252` holds on
  those two files.
- `runs/Control536e.agda:32-33` (`step-conv α x p = p`).
- `runs/Control536f.agda:29-30` (`step-only α = refl`).
- `runs/Control536d.agda:135-136` (`step-conv`), `:140-144`
  (`seq-conv`), `:147-148` (`target-only`).
- `runs/full-1.time:1-3` is `agda: Heap exhausted` at 8192 MB.
  `runs/full-2.time:1-3` is the same class. `runs/ctld-0.time:1-3`
  is the same class. `runs/ctld-0.time:4` is `699.49 real`.
- Line counts by `wc -l`: Probe536 409, W3 163, Control536 153,
  Control536b 158, Control536c 271, Control536d 148, Control536e 33,
  Control536f 30. These match the coder's cost table at
  `lj-1.536-report.md:277-285` and the predecessor's re-count at
  `review-of-LJ-1-536-1.md:142-145`.

The harvest rows the predecessor named.

- `dev/pod/table.toml:14932-14945` (`task-lj-1-536-go`:
  `exit_code = 0`, `obligations_delta_max = -1`,
  `heap_wall = false`).
- `:14964-14978` (`task-lj-1-536-stop-stated`:
  `obligations_delta_min = 0` at `:14976`).
- `:15013-15024` (`task-lj-1-536-heap-wall-escalate`:
  `heap_wall = true`).
- `:4278-4292` (`sys-critic-upheld-no-go`: `exit_code = 0`,
  `heap_wall = false`, `obligations_open_min = 1` at `:4292`).
- `scripts/pod/accept.py:20-22` (conjunct 1 stops at the first
  failing target).
- `dev/pod/heads.toml:291` (wide caliber `-A64m -I0 -M8g`).
- `dev/LESSONS.md:2357` (heading of law P-l).
- `src/L/Ordinal/Stages.lagda.md:434` (`ord∈Lset-suc`).
- `src/L/Axioms/Basic.lagda.md:596-599` (`pr∈Lset-suc`).
- `src/L/Hierarchy.lagda.md:621-626` (`hierL`, `hierL-spec`).
- `dev/pod/audit-2026-08-20.md:34` is the heading of F1. `:40-41`
  is the brief/result split. The predecessor's defect table against
  the coder at `review-of-LJ-1-536-1.md:167` still holds.
- `dev/literature/devlin-II5.md:217` and `:222` hold the two
  quoted sentences. See LITERATURE USED.

**THE DEFECTS, all in the predecessor, none load-bearing for
`upheld`.**

| claim | cited | actual |
|---|---|---|
| stop-stated needs `obligations_delta_min = 0` | `table.toml:14975-14976` at `review-of-LJ-1-536-1.md:297-298` | `:14976` is that field. `:14975` is `exit_code = 0` |
| `Lset→isL` | `Constructible.lagda.md:395-396` at `review-of-LJ-1-536-1.md:92-93` | `:396-397` is the name. `:395` is the fence |
| `ctld-0.time` wall clock | `:1-3` at `review-of-LJ-1-536-1.md:153-154` | `:1-3` is the heap message. `:4` is `699.49 real` |
| four questions written as `SECTION 6.6` | `review-of-LJ-1-536-1.md:244` | the three questions of the design memo sit at `dev/memos/LJ-4-pod-program-design.md:2853-2858`. The four sit at `archive/dev/DD-archived.md:35`. The live slot file `dev/pod/instructions/coder_adversarial.md:11` still names the four as section 6.6's, which is the file that dispatch cat'd to the predecessor. This is a heading mismatch against the design memo, not a verdict split |
| ARCHIVE USED declined `archive/dev/DD-archived.md` | `review-of-LJ-1-536-1.md:342-343` | the predecessor used DD25's four questions in the body. The decline is of the file, not of the ruling |

The predecessor could not cite `runs/accept-4.out`. That file is new
to this review. It does not contradict the predecessor. It confirms
the harvest prediction at `review-of-LJ-1-536-1.md:268-279` and
`:330-334`: conjunct 1 still dies on `Control536d.agda`,
`heap_wall` is still true, `obligations_open` is still 0, and
`sys-critic-upheld-no-go` still cannot match. The only new facts are
`concurrency` 3 (`accept-4.out:7`) and `Control536d` at 638.45 s
(`accept-4.out:20`). The caliber is the same.

## QUESTION 3. IS THE PREDECESSOR'S ENUMERATION COMPLETE

The predecessor's enumeration of the coder is complete on every item
that carries the NO-GO. Two gaps sit beside that close. Neither
inhabits `StageHigh`. Neither turns `upheld` into `overturned`.

**Complete.** The four routes the brief demanded
(`LJ-1.536.md:103-107`) are all in the coder's
`## WHAT THE FOUR ROUTES GET` and all in the predecessor's Question 3
at `review-of-LJ-1-536-1.md:183-188`. Furthest is still row six,
because nothing in the probe speaks about `K`
(`lj-1.532-report.md:45`). The door split is named, with
`carve∈𝒟ₒ` (`Separation.lagda.md:198-199`), `W3.agda:115-116`, and
`Probe536.agda:278-280` as the three facts that use `𝒟ₒ-intro` and
not the `Δ₀` bridge. The residue list names `HierBelowLimit`
(`Probe536.agda:408-409`) and the unwritten `successor-step`
(`:366-387`). W2 is present as `AdjoinAt` (`:189`) and `Adjoin`
(`:297`) and is unnamed in the coder, as the predecessor said. W3
named the term (the formula at `𝒟ₒ-intro`) and the probe
(`runs/W3.agda`). The predecessor asked whether those names exist,
which is what A21 asks of a review of this shape. W4 has no retired
module. C-42's sweep was not due. W8 is not a literature NO-GO:
Devlin leaves the details to the reader. That is a missing proof,
not an axiom this tree cannot meet.

**Complete, and confirmed after the predecessor returned.** The
process cure the predecessor named at
`review-of-LJ-1-536-1.md:317-322` is still the only harvest cure:
do not leave `Control536d.agda` as a live module in `runs/`. This
review cannot move that file. The write scope is this file only.
`accept-4.out:20` is the measurement that the cure was not applied.

**Incomplete, and it strengthens the NO-GO rather than reopening
it.** The predecessor's door analysis is about `AtStage`'s `Δ₀`
path versus `𝒟ₒ-intro`. It does not separately name that
`levelFo` (`Probe520.agda:163-164`) is a level-hood formula, while
`𝒟ₒ-intro` for this obligation wants a formula whose `defSet` is
the sequence (`Constructible.lagda.md:301-304`,
`Probe536.agda:76-80`). That is a second adjacency, of target class,
beside the ambient-versus-inner adjacency the predecessor kept. The
brief's D-10 stop (`LJ-1.536.md:77-84`) still fires on either
reading. The predecessor's close does not need the second reading
and did not take it.

**Incomplete, not a miss of a cure.** The predecessor said there is
no cheap inhabitant of `StageHigh`
(`review-of-LJ-1-536-1.md:310-314`). This review agrees. Applying
the graded formula, after `embed`, as a `Formula ⟪ Lset (step 4 γ) ⟫ 1`
and proving `defSet` equals the sequence is the original obligation.
The brief forbade that path once D-10 found adjacency
(`LJ-1.536.md:82-84`, `:123-124`). An inner unbounded existential
written over the stage, which `𝒟ₒ-intro` admits
(`review-of-StageHigh.md:29-32`), is the next brief's obligation,
already named by the coder at `lj-1.536-report.md:300-307` and kept
by the predecessor. It is not a term this return missed.

**Not missing.** The predecessor's `upheld` does not claim that
`sys-critic-upheld-no-go` will match. It says the opposite at
`review-of-LJ-1-536-1.md:330-334`. `accept-4.out` is that sentence
measured.

The four questions of DD25 (`archive/dev/DD-archived.md:35`), used
here as the lens and not as a second verdict, give the same close.
The predecessor's `upheld` is correct on its own numbers. The
measurement is sound on the files that stayed green and on the files
that died. The coder's brief caused the NO-GO framing
(`LJ-1.536.md:77-84`, `:136-138`). This review brief caused a
second attack on a harvest that could not close, not a different
mathematical outcome. There is no missed inhabitant of `StageHigh`.

`sys-critic-upheld-no-go` at `dev/pod/table.toml:4278-4292` still
needs `obligations_open_min = 1` and `heap_wall = false`. The
predecessor left `obligations_open` at 0. Harvest still re-enters
`Control536d.agda`. An upheld review with exit 0 will not match that
row on those two facts. That is a harvest fact. It does not change
the mathematical NO-GO, and it does not change this upholding.

## ARCHIVE USED

- `archive/dev/JOURNAL.md`: not read, declined. This review attacks
  a live critic return. It does not need a history file.
- `archive/dev/ORCHESTRATION.md`: not read, declined. The live
  review rule is `dev/memos/LJ-4-pod-program-design.md` section 6.6
  for the three questions this file writes.
- `archive/dev/DD-archived.md`: READ. Line 35 is DD25, and it is
  the home of the four questions used as the lens:

  > is the refusal correct on its own numbers; is the measurement sound; did the BRIEF cause the outcome; and is there a cure the return missed.

  The predecessor's `upheld` is a review that agrees, which that
  same line calls a real result.
- `archive/dev/PLAN-archived.md`: not read, declined. The standing
  direction and the work brief already name the live plan.
- `dev/ARCHIVE.md`: not read, declined. Neither the coder nor the
  predecessor retired a module. Clause W4 has no row here.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: READ. The predecessor's D-10
  reading of the two strengths is the reading this file holds.
  `dev/literature/devlin-II5.md:217`:

  > Strength: the existential over z is UNBOUNDED at the ambient level.

  and `dev/literature/devlin-II5.md:222`:

  > γ < α. Strength: the Σ₁ form is "witnessed inside the carrier", not

  The adjacency claim (ambient `Σ₁` versus witness inside the
  carrier) stands. The "refuted at the door" claim still does not
  follow from these lines, because the door `𝒟ₒ-intro` admits an
  inner reading of an unbounded existential
  (`Constructible.lagda.md:301-304`, `Separation.lagda.md:198-199`).
  That is the predecessor's correction, re-derived here, and it does
  not inhabit `StageHigh`.
- `dev/literature/BIBLIOGRAPHY.md`: not read, declined. No
  bibliographic identity is under attack.
- `dev/literature/digest.md`: not read, declined. `devlin-II5.md`
  is the chapter digest this review needed.
- `dev/literature/geology.md`: not read, declined. Nothing here is
  about ground models.
- `dev/literature/devlin-errata.md`: not read, declined. No erratum
  is cited by the return under attack and none is spent by this
  review.
