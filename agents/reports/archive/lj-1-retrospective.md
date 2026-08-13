# LJ-1 retrospective: the process audit

Status: COMPLETE. Written by a read-only auditing agent, 2026-08-11.
Scope: the orchestrator's process in phase LJ-1, not the mathematics.
Corpus read whole: 39 briefs (`_build/briefs/LJ-1.*.md`), all 11 reviews,
6 reports in full and the rest through PLAN section 11 and the reviews'
quotations, `dev/JOURNAL.md`, the 11 new LESSONS entries, `dev/PLAN.md`,
`dev/ORCHESTRATION.md`, and `git log` on `two-tower-bridge`.
I ran no Agda. Every rate below is a recorded figure and D-10 applies to it.

One correction to the task statement first. **The phase had SEVEN overturns
and two upholds, plus one split, not six and four.** The verdict lines:
OVERTURN at `_build/lj-1.15-review.md:5`, `lj-1.16-review.md:5`,
`lj-1.17-review.md:8`, `lj-1.32-review.md:12`, `lj-1.33-review.md:8`,
`lj-1.34-review.md:8`, `lj-1.41-review.md:9`. UPHOLD at
`lj-1.27-review.md:8` and `lj-1.38-review.md:12`. Split at
`lj-1.6-review.md:8`: the stop upheld, the reason and the price overturned.
PLAN section 11 carries the same seven OVERTURN cells
(`dev/PLAN.md:454,456,465,467,470,472,474,488`). The orchestrator's own
summary miscounts its own record. That miscount is itself a finding: the
task-index verdict cells are correct, and nothing reads them back.

## 1. THE FIVE CHANGES

Ranked by expected value. Each is an instruction for tomorrow.

### Change 1. Classify the deciding claim of every negative verdict. An inference-based negative sets no verdict until the inference is machine-checked.

**Instruction.** At every audit of a negative return, extract the ONE claim
the verdict rests on. Write its class: MEASURED or INFERRED. Treat an
INFERRED negative as an open question, not a verdict. Require the return
template to carry this line. Give the DD25 reviewer the claim as its first
target.

**Evidence.** The class separates all ten DD25 fires with no exception.
Section 2 gives the table. Seven negatives rested on an inference and all
seven were overturned. Two rested on a machine-checked claim and both were
upheld (`lj-1.27-review.md:5-23`, `lj-1.38-review.md:49-142`). The split
case separates inside one return: the machine-checkable half was upheld and
the inferred half overturned (`lj-1.6-review.md:8-45`).

**Cost it saves.** Seven wrong verdicts in 39 dispatches. Each cost one
maximum-effort review, and each, acted on, mispriced a route by 3x to 61x
or stopped the phase (section 3). C-34 and C-36 are special cases of this
rule; this is the general form with the enforcement point at the audit.

### Change 2. Dispose of every uncertainty item at the audit. A block with an undisposed semantic uncertainty is STAGED, never DELIVERED.

**Instruction.** At every return, read the report's WHAT I AM NOT SURE OF
section as an obligation list. For each item: discharge it, register it as
an owed row, or accept it with a written reason. Do this before the commit.
Record DELIVERED only when no semantic item stays open. Use STAGED
otherwise, in the PLAN row.

**Evidence.** The phase's worst defect announced itself twice and nobody
consumed the announcement. `_build/lj-1.5-report.md:210-213`: "The
matrix-to-clause link is unproven. Nothing shows the bounded matrix says
what the delivered `existClauseAt` says." That is the exact defect
`[LJ-1.41-R]` found six dispatches later
(`lj-1.41-review.md:329-353`). `_build/lj-1.37-report.md:229-235` flagged
the atom-slot disagreement and said "I could not unfold the private body to
settle it"; the orchestrator committed DELIVERED over it (`92e8b8b`) and
then carried the unsettled claim into the next brief as a found fact
(`lj-1.38-review.md:203-227`). `_build/lj-1.36-report.md:56-62` warned that
eight rows have no public whole-row reader, which is why no comparison ever
ran; it was read as a cost, not a warning.

**Cost it saves.** 968 of 2,141 in-fence lines re-opened, one build
dispatch, one review, and at least two repair dispatches (C-35,
`dev/LESSONS.md:3094-3134`). The audit step costs minutes.

### Change 3. Put raw measurements in briefs. Never a derived verdict table. Mark every derived figure DERIVED with its inputs.

**Instruction.** A brief may state a measured number with its `file:line`.
A brief must not state a conclusion computed from measurements as a
starting fact. Delete the pattern "the numbers are corrected, start from
these". Give the inputs and ask the agent to derive.

**Evidence.** `[LJ-1.17]`'s brief handed a pre-computed FAIL table with a
wrong denominator and a cross-paired band, said "I verified both myself",
and the agent propagated it verbatim into a NO-SHAPE-FITS verdict
(`lj-1.17-review.md:346-357`). The same error stood in the ledger, the
brief and the return at once (C-31, `dev/LESSONS.md:1878-1881`).
`[LJ-1.38]`'s brief carried `[LJ-1.37]`'s unverified machine-quirk claim as
fact and the agent spent its atom section refuting it
(`lj-1.38-review.md:203-227`). `[LJ-1.16]`'s brief pre-computed the
refusal's headline, "about seventeen times", and the return reported 17 to
23 (`lj-1.16-review.md:427-429`).

**Cost it saves.** At least two overturned verdicts and one three-site
ledger error. The brief is the highest-gain contamination channel the
phase had (section 2).

### Change 4. Derive every gate threshold from the booked band, show the derivation in the brief, and confirm the gate can return both verdicts.

**Instruction.** Before dispatching a gate, compute the per-unit figure the
booked row implies. Set the gate from that figure. Write the derivation
into the brief. If one disjunct of the NO-GO condition is already failed by
the standing record, the gate cannot return GO: do not dispatch it.

**Evidence.** `[LJ-1.15]`'s 40-line gate sat below a band whose top allows
133 lines per clause, and its 100-line gate sat 4x to 7x below the
archive's own price for the same object; both halves of the NO-GO trace to
the gates (`lj-1.15-review.md:325-339`). The orchestrator already admitted
this pattern in a later brief: "Two probes this phase were sent with gates
I set below the band they were meant to test"
(`_build/briefs/LJ-1.19.md:63-66`). The admission has no law and no
checklist step; this change gives it one.

**Cost it saves.** One manufactured NO-GO plus one review per occurrence.
Two occurrences in this phase.

### Change 5. After any cure lands, re-run every gate probe in its import cone before quoting a figure or dispatching against it.

**Instruction.** Keep, beside each standing gate figure, the probe file and
the cone it depends on. When a commit touches that cone, mark the figure
STALE and re-run the probe before the next dispatch that reads it. C-32
states the law; this makes the list mechanical instead of remembered.

**Evidence.** `[LJ-1.31]`'s cure cut the unchanged gate probe from 32.07 s
to 18.95 s, a GO, and nobody re-ran it; the phase stayed stopped, the
orchestrator quoted the stale figure three times, and `[LJ-1.32]` spent a
whole dispatch measuring walls behind an open gate
(`lj-1.32-review.md:22-38`; C-32, `dev/LESSONS.md:2956-2963`). A finished
green probe sat one command away for the whole dispatch
(`dev/LESSONS.md:2965-2969`).

**Cost it saves.** One dispatch plus the compounding of a stale figure into
every downstream document.

**A sixth change, below the cut but cheap.** Register every review
recommendation as an owed row. `[LJ-1.6-R]` recommended naming
`src/ProbeTowerInd2.agda` and the T85 report in the next SCOPE (read)
(`lj-1.6-review.md:463-467`); the `[LJ-1.17]` brief dropped it and paid
error 2 (`lj-1.17-review.md:370-375`). Meanwhile the same review's WRONG
recommendation, the non-initial transfer, DID propagate into the ledger
(`lj-1.17-review.md:399-404`). The channel selects at random because it is
memory.

## 2. WHAT PREDICTS A WRONG VERDICT

Two predictors, tested on all ten fires. The sample is ten reviews from one
36-hour phase with one brief author, so treat the rates as this phase's,
not as constants.

### Predictor A: the class of the verdict-deciding claim. Ten of ten.

| fire | deciding claim | class | verdict |
|---|---|---|---|
| LJ-1.6 stop | the carrier is a quotient and the count does not factor | machine-checkable, TRUE | UPHELD (`lj-1.6-review.md:10-14`) |
| LJ-1.6 price | descent costs 250-450 lines | inferred, archive unread | OVERTURNED: 52 measured (`lj-1.6-review.md:22-24,107-126`) |
| LJ-1.15 | 155 lines is 4x the allowance | inferred from a mis-set gate | OVERTURN (`lj-1.15-review.md:9-14`) |
| LJ-1.16 | the shape costs 1.0-3.0k lines | inferred, price transferred from another object | OVERTURN (`lj-1.16-review.md:339-362`) |
| LJ-1.17 | the wing fails DD24 with the port | inferred, wrong denominator | OVERTURN (`lj-1.17-review.md:14-19`) |
| LJ-1.27 | the block runs 0.113 s/line at the named target | MEASURED at the site | UPHOLD (`lj-1.27-review.md:9-13`) |
| LJ-1.32 | route A stays closed | inferred from a stale gate figure | OVERTURN (`lj-1.32-review.md:22-38`) |
| LJ-1.33 | leg D costs 0.334 s/line | inferred: the rate belongs to one proof shape | OVERTURN (`lj-1.33-review.md:8-16`) |
| LJ-1.34 | no cheap shape exists | inferred: the named cure was never built | OVERTURN (`lj-1.34-review.md:8-13,144-157`) |
| LJ-1.38 | the delivered rows are vacuous | machine-checkable, TRUE and worse | UPHOLD (`lj-1.38-review.md:49-142`) |
| LJ-1.41 | no Delta-0 witness can exist | inferred from a failed coercion | OVERTURN (`lj-1.41-review.md:120-160`) |

Every overturn kept the measurement and killed the inference. The reviews
say so explicitly: "The measurement stands. The conclusion does not"
(`lj-1.32-review.md:12`), "KEEP THE MEASUREMENT" (`lj-1.17-review.md:8`).
The orchestrator's memo says "several" overturns were of returns that
measured correctly; the true count is all seven.

### Predictor B: brief contamination. Six of seven overturns, absent from the clean uphold.

Per case, with the mechanism:

- **LJ-1.15.** Gates below the band; SCOPE (read) omitted the three
  chapters that hold the answer (`lj-1.15-review.md:325-347`).
- **LJ-1.16.** Four mechanisms: the wrong face of a delivered module named
  ("the inverse may be most of this"), refusal named as "a full
  deliverable", the headline pre-computed at "seventeen times", and a
  three-slot return template with no place for a fourth shape
  (`lj-1.16-review.md:414-437`).
- **LJ-1.17.** The pre-computed FAIL table, "start from these", and the
  design probe dropped from SCOPE against a standing recommendation
  (`lj-1.17-review.md:346-375`).
- **LJ-1.32.** The archive read scoped to "section 4" while the cure sat in
  section 6; the ladder framing asked the wrong question
  (`lj-1.32-review.md:240-273`).
- **LJ-1.33.** Both causes: the expensive delivered projections named at
  `file:line` as "the delivered machine side", and "take its `Clause`
  shapes as the source" (`lj-1.33-review.md:143-178`; C-33).
- **LJ-1.34.** Partial: "the delivered body rather than a re-typed one"
  pushed the costly shape, but the decisive defect was the return's
  unmeasured cure (`lj-1.34-review.md:349-374`).
- **LJ-1.41.** NOT the brief. The brief named the cure and the agent looked
  past it (`lj-1.41-review.md:206-241`). The one-sided "do not weaken"
  line got a note, not a causal share.
- **LJ-1.27 (uphold).** The review tested the brief first and cleared it:
  the brief's instruction contributed 1 constant of 17
  (`lj-1.27-review.md:61-113`).

Sharpening the orchestrator's own claim: the memo counts three
brief-caused refusals (C-32, C-33, C-36). The reviews assign the brief a
large or decisive share in FIVE fires (1.15, 1.16, 1.17, 1.32, 1.33), a
partial share in two (1.34, 1.38), and explicitly clear it in the C-36 case
(1.41). The memo under-claims by two and over-claims the one it is most
confident about.

**Where the sample is too small.** Ten fires cannot separate predictor A
from predictor B, because five overturns carry both. The one case with B
absent (1.41) still overturned on A, which is weak evidence that A is the
deeper predictor. Brief length, tier, and task kind show no signal at this
sample size. Do not build a rule on those.

## 3. DID DD25 PAY?

**Yes, by a wide margin. And its firing pattern indicts the process that
feeds it.**

**The cost.** Ten in-harness Opus reviews at maximum effort: 10 review
dispatches against 39 primary dispatches, about 26 percent dispatch
overhead. Six reviews also consumed Agda slots for probe batteries. One
review exported a defect: `[LJ-1.6-R]`'s non-initial-transfer obligation
was a misread, propagated into the ledger and a brief, and had to be killed
by `[LJ-1.17-R]` (`lj-1.17-review.md:21-27,399-404`). So the safety net is
not free and not infallible.

**What it caught, with the counterfactual price of each wrong verdict:**

- **LJ-1.16:** the refused shape was priced 1.0-3.0k lines and 220-890 s;
  the fourth shape measured 116 lines at 0.0103 s/line and became DD27 and
  the delivered hull at 0.0039 (`lj-1.16-review.md:20-29`,
  `dev/PLAN.md:185`). Error factor 3-20x in lines, 56-1100x in seconds.
- **LJ-1.33 and LJ-1.34:** two NO-GOs on the crossing at 0.334 and 0.436
  s/line; the same theorems check at 0.0108 and 0.0072. Factors 31x and
  61x. Each NO-GO would have stopped the phase (C-34,
  `dev/LESSONS.md:3074-3084`).
- **LJ-1.17:** a FAIL that inverts to 0.72-0.82x PASS under the right
  denominator, plus a 150-400-line false obligation removed
  (`lj-1.17-review.md:34-62`).
- **LJ-1.32:** the phase was stopped behind a gate that was already open
  (`lj-1.32-review.md:22-38`).
- **LJ-1.41:** nine rows declared unclosable; the cure is one conjunct,
  about 100 lines and 0.22 s (`lj-1.41-review.md:9-58`).
- **LJ-1.15:** a NO-GO that would have re-priced route A upward on numbers
  that land INSIDE the booked band (`lj-1.15-review.md:9-34`).

**What the upholds bought.** `[LJ-1.27-R]` confirmed the NO-GO and, in
confirming it, wrote `src/ProbeDD25E.agda`, which became the erase route
and then block 1's design (`_build/briefs/LJ-1.5.md:28-37`). `[LJ-1.38-R]`
converted "vacuous" into "false", scoped the rework to 968 lines, found
1,021 lines the return had written off as re-opened, and found block 1
defective where the return had an uncertainty (`lj-1.38-review.md:31-38,
255-282`). A review that agrees was not just confidence; twice it was the
next block's engineering.

**The arithmetic.** 11-12 of 39 primary dispatches, about 30 percent,
produced conclusions or content that was later overturned, re-done or
discarded: 1.10 discarded, seven overturned verdicts, roughly half of
1.37's build, and the 1.40/1.42 repair chain. The ten reviews corrected
seven of those, produced the designs for at least three delivered blocks,
and supplied the measurements behind eight of the phase's eleven laws.
No single alternative use of ten dispatches comes close. **DD25 paid.**

**The indictment.** A 70 percent overturn rate on negatives is not a fact
about reviews. It is a fact about the negatives. The codex tier's
measurements reproduced essentially every time they were re-run; its
verdict-level inferences failed seven times in ten. DD25 is a working
compensator for a systematic upstream defect that changes 1, 3 and 4 attack
directly. **Track the overturn rate. If it stays near 70 percent after
those changes land, stop asking gate dispatches for verdict words at all:
have them return measurements against a brief-stated decision table, and
draw the verdict at the audit.** DD25 as a permanent 26 percent overhead
would mean the process treats its symptom forever.

**One boundary note.** No negative headline escaped the trigger:
`[LJ-1.31]`'s headline was DELIVERED (`_build/lj-1.31-report.md:3-11`), so
DD25 rightly did not fire; the loss there belonged to C-32. `[LJ-1.2]`'s
NO-GO predates the first fire and was vindicated by `[LJ-1.11]`
(`lj-1.11-review.md:113`). The trigger, as specified, held.

## 4. THE UNCOVERED FAILURE

**Findings parked in a report's margin have no path into the loop. No law
covers this and no checker sees it.**

The phase's costliest defect was announced twice before it was found:

1. `_build/lj-1.5-report.md:210-213`, delivered 2026-08-11 01:14
   (`f48ffd7`): "The matrix-to-clause link is unproven." That sentence IS
   the missing-conjunct defect, in block 1, from day one
   (`lj-1.41-review.md:329-347`; C-36, `dev/LESSONS.md:3217-3221`).
2. `_build/lj-1.37-report.md:229-239`: the atom-slot disagreement and "the
   satisfaction-level agreement is the next block's leg-D work". The
   orchestrator committed DELIVERED over both items and re-published item 1
   as fact in the next brief.

The same channel dropped a correct review recommendation (`lj-1.6-review.md:463-467`
to `lj-1.17-review.md:370-375`) while propagating an incorrect one into the
ledger. The selection is random because the channel is the orchestrator's
memory. `dev/ORCHESTRATION.md` section 6's checklist audits claims, slots,
wiring, gates and records; no step reads the uncertainty section.

**The law it needs**, proposed for the orchestrator to number: *an
uncertainty item in a return is an obligation; the audit discharges it,
registers it as owed, or accepts it with a written reason, before the
status word is chosen.* Measurement: two items named the 968-line defect,
four green gates and one commit passed over them, and three dispatches were
spent finding what the record already said.

**The enforcement point**, so this is not a wish: a step in
`dev/ORCHESTRATION.md` section 6 between steps 2 and 6, plus the STAGED
status word in the task index. Half of it can be mechanical:
`check-task-index.py` already parses the rows; it can refuse DELIVERED for
a task whose report carries a WHAT I AM NOT SURE OF section with no
disposition marker. The disposition itself stays a judgment, and the row
being visibly STAGED is the honest enforcement, exactly as DD25's row rule
works today.

C-35 covers the consumer half of this (no consumer, no DELIVERED) and was
admitted from the same episode. It does not cover the margin channel: an
uncertainty can name a defect no consumer will reach for weeks.

## 5. THE BRIEF AS AN ARTEFACT

**The template did not bloat in words. It accreted structure, and the
structure is both the best and the worst of it.**

Measured over the 39 briefs, in dispatch order: word counts run 1,014 to
1,968 with no trend (first six mean 1,491; last six mean 1,585). Section
counts climb steadily: 12 to 14 early, 16 to 18 late. The growth is
law-citation lists (the MANDATORY RULES section grew with each admitted
law) and the RETURN questionnaire (10 items in LJ-1.5, 12 in LJ-1.37 and
LJ-1.42).

**What a good brief has.** The model is `_build/briefs/LJ-1.19.md`, 159
lines, 1,014 words, GO at 30 lines against a 50-line gate:

- **The real question ordered first.** "Does the CONSUMER survive the
  restriction? Answer this before you write the proof" (`LJ-1.19.md:52-55`).
- **The anti-anchor licence.** "If 50 is the wrong number, say so with your
  measured one; that is a correction, not a failure" (`:63-66`).
- **Inherited-error warnings.** "What was wrong in the refusal, so you do
  not inherit it" (`:28-38`).
- **FIND-IT archive framing.** "FIND IT and cite it at `file:line`"
  (`:99-100`), the exact pattern `dev/ORCHESTRATION.md:435-441` credits
  from the LJ-1.6/LJ-1.19 controlled comparison.
- **A rival cure named** (`:101-103`), which is the N+1 slot the LJ-1.16
  template lacked.

The licence clause is measured as load-bearing in the other direction too:
`[LJ-1.34]`'s brief carried it twice and the agent ignored it, which is
what separated a brief-caused overturn from a return-caused one
(`lj-1.34-review.md:365-374`).

**What the bad briefs had** is section 2's predictor B list: derived
verdict tables, entry points at `file:line`, section-scoped reads,
pre-failed gate disjuncts, fixed-slot return templates, one-sided
constraints.

**The template metabolizes laws fast, and that is real credit.** C-34,
admitted from the 1.33/1.34 pair, headlines the very next build brief
(`LJ-1.37.md:14-21`). C-32's "read WHOLE" appears in every ARCHIVE section
from LJ-1.5 on. C-36's two halves open LJ-1.42 (`LJ-1.42.md:15-28`).

**And the limit of the template is the phase's lesson.** LJ-1.37's brief is
template-perfect: every law cited, every figure sourced, a 12-item
questionnaire. It still shipped the false theorem, because all 12 items ask
about syntax, lines, seconds and placement, and none asks whether a row
MEANS what the machine's row means (`LJ-1.37.md:199-216`). A brief can only
gate what its author thought to ask; the semantic gate has to live in the
audit (changes 1 and 2), not in more sections.

**The questionnaire's fixed slots have one measured cost.** The LJ-1.16
RETURN block asked for "THE THREE PRICES" and the report had no place for a
fourth shape (`lj-1.16-review.md:434-437`). Ask for the obligation and for
N+1, not for an enumerated list.

## 6. WHAT TO STOP

1. **Stop putting derived conclusions in briefs.** The "corrected table,
   start from these" pattern (`lj-1.17-review.md:346-357`), the
   pre-computed refusal headline (`lj-1.16-review.md:427-429`), and the
   found-fact relay of an unverified sibling claim
   (`lj-1.38-review.md:203-227`) each converted one agent's error into two
   documents' error. Three fires carry it; two are overturns. The
   replacement costs nothing: raw numbers with `file:line`, derivation left
   to the agent. (This is change 3's stop form.)

2. **Stop enumerated return templates and sub-step stop rules.** The
   three-slot template suppressed the fourth shape that became DD27
   (`lj-1.16-review.md:434-437`). The arm-1 stop rule in `[LJ-1.24]`'s
   brief left arms 2 and 3 unmeasured, recorded as a self-defect in
   `dev/JOURNAL.md:344-346`. The stop-line in `[LJ-1.38]`'s brief invited a
   stop at a wall that does not exist (`lj-1.38-review.md:224-227`).
   Stop-lines should bind budgets, not routes; return sections should
   demand the verdict, the evidence classes and the USED sections, and let
   the shape list be open.

3. **Stop section-granular SCOPE (read) on sibling documents.** C-32
   already rules "cite whole documents"; the practice survives as a habit,
   and it hid `src/ProbeDD25E.agda` for a full dispatch
   (`lj-1.32-review.md:240-264`). The stop is free: the documents are
   short, and an agent that reads a whole review costs minutes.

Each stop removes text from briefs. None adds a section. That is the
correct direction for a template already at 17 sections.

## 7. WHAT I COULD NOT CHECK

1. **I ran no Agda and no `make check`** (constraint; a sibling held the
   slot). Every rate, wall and line count here is a recorded figure. D-10
   makes them residues. The DD25 arithmetic in section 3 would survive a
   2x error in any single figure; it would not survive the discovery that
   review measurements do not reproduce. Spot-re-running two review probes
   (`src/ProbeDD25E1.agda`, `src/ProbeDD25CD.agda`) would settle that
   cheaply.
2. **Dispatch costs are counted in dispatches, not seconds or tokens.** I
   found no recorded wall-clock or token cost per review, so "26 percent
   overhead" weights an Opus review equal to a codex dispatch. If a review
   costs 3x a codex dispatch, DD25's overhead is nearer 60 percent and the
   pay-off argument still holds by the counterfactual prices, but the
   "cheap confidence" framing weakens. Recording per-dispatch cost in the
   task index would settle it.
3. **I read 6 reports whole and the rest through the reviews and PLAN
   rows.** The predictor-A classification for the ten fires rests on the
   reviews' quotations of the returns, which I verified at the quoted
   `file:line` where the review gave one. A hostile reading would re-derive
   the classification from the ten reports directly.
4. **`[LJ-1.42]` is in flight.** Its brief carries the phase's next open
   risk: `PropAgree`'s 0.0368 s/line marginal rate projects a DD24 breach
   by a third if it holds across nine rows
   (`lj-1.41-review.md:277-309`). Whether change 1 would have altered any
   of its framing is untestable until it returns.
5. **The reviews' own error rate is measured at one.** I found one
   review-exported defect (the non-initial transfer). I did not
   systematically re-audit each review's recommendations against later
   evidence; the phase did that for me only where a later review happened
   to collide. A one-pass sweep of the ten reviews' NEXT-STEPS sections
   against the current record would bound the rate.
