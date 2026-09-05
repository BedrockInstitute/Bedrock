# LJ-1.211: why is the DD25 overturn rate 71 percent

STATUS: COMPLETE. Written incrementally per C-22. Read-only audit.
No file outside the write scope was edited. No Agda ran. No commit, no push.
Every finding is marked MEASURED or INFERRED.

## 0. LEAD

**The briefs cause the overturns. The rate is an artifact. Both are true.**

**The cause split of the register's 10 overturns, by primary cause:**

| cause | count |
|---|---:|
| 1. the brief carried a false premise | 2 |
| 2. the brief fixed a method that could not answer | 4 |
| 3. the brief shipped a conclusion as an instruction | 2 |
| 4. the agent erred on its own, with the brief clean | 2 |
| 5. the reviewer was wrong | 0 |

**The brief caused 8 of the 10. The agent caused 2. The reviewer caused 0.**
**MEASURED** from the reviews' own brief-cause sections and the audit commit
bodies. The two agent-caused cases are LJ-1.34-R and LJ-1.41-R. In both, the
review says the brief did not cause the outcome
(`agents/tasks/archive/LJ-1-34/lj-1.34-review.md:331-332`,
`agents/tasks/archive/LJ-1-41/lj-1.41-review.md:207-208`).

**The single change that would lower the rate most:** make the brief's
load-bearing premises a gate-visible artifact. A brief that funds a gate, a
build or a probe on a premise declares that premise in a `## PREMISES`
section, with a basis at `file:line`. The return marks each premise VERIFIED
or REFUTED at `file:line`. A DD25 review attacks that list first. This is
the LJ-1.66-R review's own two-part gate, generalized
(`agents/tasks/archive/LJ-1-66/lj-1.66-review.md:230-258`). It covers the
premise shapes behind 7 of the 8 brief-caused overturns. INFERRED for the
counterfactual coverage; MEASURED for the premise shapes in section 1.

**The rate is an artifact, in two ways. MEASURED.**

1. **The register counts a split as an overturn.** The cell for LJ-1.66-R
   reads "SPLIT: measures upheld, conclusions overturned"
   (`dev/PLAN.md:624`). The classifier counts it as OVERTURN because the
   word "UPHELD" does not contain "UPHOLD" (`scripts/dd25-record.py:40`,
   verified by running `classify`). The register's own docstring says a
   split is its own category (`scripts/dd25-record.py:34-36`). Recount:
   **9 overturn, 2 split, 3 uphold, 64 percent.**
2. **The register undercounts the review population.** It counts only rows
   whose code ends in `-R` (`scripts/dd25-record.py:30`). Six more DD25
   reviews carry plain codes in the same table: LJ-1.179, LJ-1.180,
   LJ-1.181, LJ-1.182, LJ-1.200 and LJ-1.201 (`dev/PLAN.md:752,782-784,769-770`).
   Five upheld. One overturned. Full-record recount: **11 overturn, 8
   uphold, 1 split, 55 percent.**

At 55 percent, the 60 percent indictment threshold does not fire. The figure
"71 percent" in the register's output and in the LJ-1.208 row
(`dev/PLAN.md:777`) does not survive either recount.

## 1. THE CAUSE SPLIT, WITH EVIDENCE

Each row names the primary cause. Co-causes are named where the record names
them. The verdict cells are at `dev/PLAN.md:572,571,574,588,548,550,559,596,593,624`.

### 1.1 Category 2: the brief fixed a method that could not answer. 4 reviews.

**LJ-1.15-R.** The brief fixed the gate before the probe ran: GO at 40 lines,
NO-GO otherwise (`agents/tasks/archive/LJ-1-15/LJ-1.15.md:39-49`). The booked
row allowed 133 lines per clause. The gate sat below the band it tested. The
review says "A NO-GO produced by a gate below its own band carries no
information about the route. Both halves of the NO-GO trace to the gates"
(`agents/tasks/archive/LJ-1-15/lj-1.15-review.md:325-339`). The review also
found one agent-side error: statement 2's diagnosis was wrong in both reasons
(`lj-1.15-review.md:36-39`). The overturn was confirmed by LJ-1.19: Cure A is
green at 30 lines (commit `c9ffa34`).

**LJ-1.16-R.** The brief said "Price at least these three shapes before
building any of them" and named three
(`agents/tasks/archive/LJ-1-16/LJ-1.16.md:40-49`). The review found a fourth
shape that never appears in the report and no archive record refuses it
(`lj-1.16-review.md:7-9`). Its section header is "The brief foreclosed the
fourth shape" (`lj-1.16-review.md:414`). The audit commit says the review
"hunts a fourth shape the brief may have foreclosed by naming three"
(commit `b831e50`). The obstruction was the hull's index type, a design
choice, not the mathematics (`dev/PLAN.md:571`).

**LJ-1.32-R.** The brief scoped the archive read to one section of
`lj-1.27-review.md` (section 4). The erase route and the probe name were in
section 6. The audit commit says "THE CAUSE WAS THE BRIEF, and the fix is
mechanical" (commit `5aa4bd6`). The review measured the unchanged gate probe
at 18.95 s, a GO, and the whole crossing at 0.0107 s per line
(`agents/tasks/archive/LJ-1-32/lj-1.32-review.md:10-40`). The orchestrator
also held the pre-cure figure and quoted it three times, which is C-32's
measured instance (`dev/LESSONS.md:2965-3004`). Co-cause: a stale figure in
the brief.

**LJ-1.33-R.** The brief named one delivered entry point and one style. It
pointed at `Sequence.lagda.md:217-229`, the content projections, and never
named `Model.lagda.md:667-678`, the formula readings
(`agents/tasks/archive/LJ-1-33/lj-1.33-review.md:149-167`). The review says
the brief caused both expensive halves (`lj-1.33-review.md:143-145`). The
PLAN row says "BOTH causes were my brief. But it prices a PROXY, not the real
leg D" (`dev/PLAN.md:548`). C-33 records the law
(`dev/LESSONS.md:3005-3054`). Co-cause: the return named a cure and deferred
it, which is C-34's shape (`dev/LESSONS.md:3189-3217`).

### 1.2 Category 1: the brief carried a false premise. 2 reviews.

**LJ-1.17-R.** The wrong denominator stood in three places at once: the
ledger, the brief written from it, and the return that propagated it back.
The budget was divided by the wing's line count today, 2,677, when the wing
is 12 to 18 percent built (commit `a4e4e11`). C-31 records the law and says
"A wrong denominator in a ledger looks exactly like a measurement"
(`dev/LESSONS.md:1873-1913`). The review's corrected arithmetic: the wing
passes at 0.82x and 0.72x (`dev/PLAN.md:574`).

**LJ-1.50-R.** The brief prescribed "build at VARIABLE SLOTS" and attributed
it to P-u. P-u prescribes composing the absoluteness through the unplaced
form, which is `EraseTransfer`, the exit the return then called a design
decision (`agents/tasks/archive/LJ-1-50/lj-1.50-review.md:286-305`). P-t had
already closed the variable-slot axis (`lj-1.50-review.md:305-318`). The
audit commit says "MY BRIEF WAS PART OF IT" (commit `c88cb22`). Co-cause:
the return's own probe spelled the count proof inline, which produced the
150,133 ms figure (`lj-1.50-review.md:320-330`); C-34 fired a third time
because the return deferred a named cure (commit `c88cb22`).

### 1.3 Category 3: the brief shipped a conclusion as an instruction. 2 reviews.

**LJ-1.7-R.** The brief wrote P-u as a prohibition: "if you need absFo or a
placed Delta-0, STOP: the wall is flat at 8 GB". P-u's content is certify
before you place, and its cure is a constant-free formula, so no placement is
needed at all (commit `feba5dc`). The agent stopped on a constant count and
called it a wall, while the file documented the cure itself
(`agents/tasks/archive/LJ-1-7/lj-1.7-review.md:13-30`). C-37 records the
law: a law written as a wall hides its own cure
(`dev/LESSONS.md:3399-3444`). Co-cause: the return's blocker 2 was a
conflation of two fibres (`lj-1.7-review.md:25-29`).

**LJ-1.66-R.** The register counts this review as an overturn. Its cell and
its review say SPLIT (`dev/PLAN.md:624`,
`agents/tasks/archive/LJ-1-66/lj-1.66-review.md:23-30`). The overturn part is
of LJ-1.67's conclusion. The LJ-1.67 brief prescribed the mechanism in its
own words, and the mechanism claim and the prescribed shape contradicted
each other in the same paragraph. The agent built what it was told and
measured it honestly (commit `ce48c1e`; `lj-1.66-review.md:773-807`). The
LJ-1.66 brief carried a false structural premise, and its GO gate could not
see the premise fail (`lj-1.66-review.md:230-258`).

### 1.4 Category 4: the agent erred on its own. 2 reviews.

**LJ-1.34-R.** The review says "the decisive defect is in the return, not in
your brief. This is not a second C-33" (`agents/tasks/archive/LJ-1-34/lj-1.34-review.md:331-332`).
The return named a generic leaf layer as its cure and declined to measure it,
citing P-l. P-l forbids pricing by analogy. It never forbids building and
measuring (`lj-1.34-review.md:326-329`). The brief's "Measure it; do not
argue it" line was the licence the return did not use
(`lj-1.34-review.md:349-352`). The review also upheld the deciding claim:
"the Delta-0 certificate does not close... That is true, it is the whole
remaining obligation" (`lj-1.34-review.md:37-40`). So this review is a
partial by content: the price was overturned, the phase-blocking claim was
upheld.

**LJ-1.41-R.** The review answers "DID THE BRIEF CAUSE IT? NO. Your brief
did not lock the shape, and it named the cure"
(`agents/tasks/archive/LJ-1-41/lj-1.41-review.md:207-208`). The return
inferred an impossibility from a type error. The review built a one-line
Delta-0 witness and two-way transfers in four probes
(`lj-1.41-review.md:10-24`). C-36 records the law: a type error says the
types differ, never that no term connects them (`dev/LESSONS.md:3302-3350`).
One brief line contributed: "do not weaken" had no matching "you MAY
strengthen" (`lj-1.41-review.md:220-228`). The primary cause is the return.

### 1.5 Category 5: 0 reviews.

No review among the 10 overturns should be reversed. Each correction was
later re-verified on the record: LJ-1.15 by LJ-1.19 (commit `c9ffa34`);
LJ-1.16 by the DD27 ruling and LJ-1.18 (commit `a4e4e11`); LJ-1.17 by the
orchestrator's own recomputation (commit `a4e4e11`); LJ-1.32 by the
orchestrator's re-runs (commit `5aa4bd6`); LJ-1.33 and LJ-1.34 by the
orchestrator's endpoint reproductions (commits `3566676`); LJ-1.41 by four
probes re-run by the orchestrator (C-36 provenance, `dev/LESSONS.md:3350`);
LJ-1.50 by the orchestrator's re-runs at 154.92 s against 2.20 s (commit
`c88cb22`); LJ-1.7 by the built cures (commit `feba5dc`); LJ-1.66 by P-w,
admitted (commit `ce48c1e`). MEASURED.

The reviews are not too eager in their verdicts. The register's binary count
is too coarse. Two overturns upheld the phase-blocking question in their own
text: LJ-1.33-R priced a proxy (`dev/PLAN.md:548`) and LJ-1.34-R upheld the
certificate claim (`lj-1.34-review.md:37-40`). One review's proposed law
over-reached and was amended the same day: P-w's copy claim
(`dev/PLAN.md:629`). These do not reverse the verdicts. They do show that
counting each review as a full overturn or a full uphold loses the finding.

**The sample is small, and the artifact audit is the boundary.** The cause
split rests on 9 true overturns, not 10, and two of those are partials by
content (LJ-1.33-R and LJ-1.34-R). The claim "the briefs are the dominant
cause" survives because 8 of 10 carries even if one case is re-bucketed. The
claim "the rate is 71 percent" does not survive any recount. To make the
split carry a conclusion, the register must count the full population first,
then accumulate more reviews under the corrected classifier. INFERRED.

## 2. THE RATE IS AN ARTIFACT, IN DETAIL

The register output says 10 overturn, 1 split, 3 uphold, 71 percent. The
cells say otherwise, in two ways. MEASURED.

**The classifier bug.** `classify` tests `"UPHOLD" in v` and `"OVERTURN" in
v` (`scripts/dd25-record.py:40`). The cell for LJ-1.66-R is "SPLIT: measures
upheld, conclusions overturned" (`dev/PLAN.md:624`). "UPHELD" does not
contain "UPHOLD". The function returns OVERTURN. Verified by running the
function: the same cell returns SPLIT only for LJ-1.6-R's "UPHOLD the stop,
OVERTURN reason and price". The docstring says a split is its own thing
(`scripts/dd25-record.py:34-36`). The register contradicts its own rule.

**The population filter.** The row regex matches only codes ending in `-R`
(`scripts/dd25-record.py:30`). The table holds six more DD25 reviews with
plain codes: LJ-1.179 (OVERTURNED), LJ-1.180 (UPHELD), LJ-1.181 (UPHELD),
LJ-1.182 (UPHELD), LJ-1.200 (UPHELD BUT MISATTRIBUTED) and LJ-1.201 (UPHELD
BUT MISATTRIBUTED) (`dev/PLAN.md:752,782-784,769-770`). Five of six upheld.
The LJ-1.208 gate itself uses the wide definition: a review is a `-R` row or
a row whose cell names a DD25 review (`agents/tasks/LJ-1-208/lj-1.208-report.md:37-44`).
The register uses the narrow one.

**The recount.**

| population | overturn | split | uphold | rate |
|---|---:|---:|---:|---:|
| the register as run | 10 | 1 | 3 | 71 percent |
| register cells, classifier fixed | 9 | 2 | 3 | 64 percent |
| full DD25 record on 2026-08-14 | 11 | 1 | 8 | 55 percent |

The 60 percent threshold fires only for the first two populations. It does
not fire for the full record. The 55 percent figure is MEASURED from the
verdict cells; the "UPHELD BUT MISATTRIBUTED" cells are read as upholds
because the verdict stood, and the misattribution is recorded separately.

## 3. DD4 AND WHAT DISTINGUISHES THE OVERTURNS

All 14 review-era briefs carry DD4. I checked each one by grep: LJ-0.4f,
LJ-1.15, LJ-1.16, LJ-1.17, LJ-1.27, LJ-1.32, LJ-1.33, LJ-1.34, LJ-1.38,
LJ-1.41, LJ-1.50, LJ-1.6, LJ-1.66 and LJ-1.7, all DD4-YES. MEASURED.

So DD4's presence does not separate the overturns from the upholds. It is a
constant, not a discriminator. The separation is the correctness of the
brief's load-bearing premises. No gate in this project reads a premise for
truth. The gates read form: the tier line, the archive citation, the DD4
section. The failure is invisible to every gate. INFERRED, from the
classification in section 1.

## 4. THE THREE UPHOLDS, FOR CONTRAST

LJ-0.4f-R upheld the refusal and found the return's one false finding, a
false D-10 claim (`dev/PLAN.md:529`). LJ-1.27-R built the cure the return
hypothesized; it walls at 8 GB, and the brief did not cause the NO-GO
(`dev/PLAN.md:583`). LJ-1.38-R upheld the refusal, and worse: the rows were
false of the satisfaction table (`dev/PLAN.md:555`). The brief was wrong on
one slot premise (commit `931c13e`), but the verdict stood. These three show
that DD25 reviews can uphold a correct negative and still correct the record.

## 5. THE COSTS, RANKED

The ranking uses the record's own words about what each overturn cost.
MEASURED from the cited commit bodies and review files.

1. **Category 2, four reviews.** Two of them (LJ-1.33 and LJ-1.34, by
   lineage) produced NO-GOs at 25 to 61 times the true rate. C-34 says each
   NO-GO would have stopped the phase (`dev/LESSONS.md:3207-3208`). LJ-1.16
   forced a re-price and the DD27 owner fork (commit `a4e4e11`). LJ-1.32
   spent a whole dispatch measuring walls around a gate that was already
   open (commit `5aa4bd6`).
2. **Category 3, two reviews.** LJ-1.7's STOP blocked the condensation
   transfer until the review's cures were built (commit `feba5dc`). LJ-1.66
   misdirected the optimization: "The residual was never the real problem,
   and I have been optimizing it for six dispatches" (commit `ce48c1e`).
3. **Category 1, two reviews.** LJ-1.17's wrong denominator stood in three
   places and would have stopped the square law (commit `a4e4e11`). LJ-1.50
   mispriced a route by about 500 times (commit `c88cb22`).
4. **Category 4, two reviews.** LJ-1.41 blocked the eleven-row closure until
   four probes cleared it (commit `8019b6a`). LJ-1.34's NO-GO at 0.436 would
   have stopped the phase on a price 61 times too high (commit `3566676`).

## 6. THE PROPOSALS, EACH WITH A MOMENT AND A TRIGGER

### Change 1 (CHECKER): the brief-premises gate, which is the two-part gate generalized

**MOMENT.** The commit that lands a brief, and the audit of a return.

**TRIGGER.** A brief that carries any of these tokens: "the gate is", "GO
needs", "NO-GO is", "the only lever", "shapes", "section", a LESSONS law ID,
"do not weaken", "measure it, do not argue it", or a figure with a unit.

**The mechanism.** A checker, shaped like `check-dd25-review-named.py`,
refuses a brief that carries a trigger token and no `## PREMISES` section.
The section lists each load-bearing premise with a basis at `file:line`. The
return must mark each premise VERIFIED or REFUTED at `file:line`. A DD25
review attacks that list before anything else. This is the LJ-1.66-R
review's cure, written by the review: "GO only if (a) the unit cost is 0.05
s or more AND (b) the applications genuinely collapse. Verify (b) by reading
the sites BEFORE you build anything"
(`agents/tasks/archive/LJ-1-66/lj-1.66-review.md:230-258`). It is also the
LJ-1.15-R review's cure: "Derive every line gate from the booked row's own
per-unit figure, and write that derivation in the brief"
(`agents/tasks/archive/LJ-1-15/lj-1.15-review.md:407-409`).

It would have caught the premise shapes behind LJ-1.15, LJ-1.16, LJ-1.32,
LJ-1.33, LJ-1.50, LJ-1.7 and LJ-1.66. The counterfactual coverage is
INFERRED. The premise shapes themselves are MEASURED in section 1.

### Change 2 (CHECKER): fix the register

**MOMENT.** Running `dd25-record.py`.

**TRIGGER.** A verdict cell that contains "UPHELD" or "SPLIT", or a review
row whose code does not end in `-R`.

**The mechanism.** Match "UPHELD" as an uphold word, and count a DD25 review
by the wide definition the LJ-1.208 gate uses: a `-R` row, or any row whose
cell names a DD25 review. The register then prints 64 percent, or 55 percent
over the full record, instead of 71.

### Change 3 (SKILL): a law citation quotes the law's action

**MOMENT.** Writing a brief that cites a LESSONS law.

**TRIGGER.** Any law ID in the brief: P-u, P-v, P-l, P-t, C-32, C-33, C-34,
C-36, C-37, C-39, or any other `P-`, `C-`, `D-` or `DD` ID.

**The mechanism.** Extend the existing `load-bearing-claim` skill
(`.claude/skills/load-bearing-claim/SKILL.md`) with one rule: when a brief
cites a law, quote the law's ACTION sentence beside the ID. C-37 is the law
behind this: state a law with the action it prescribes, never only the
prohibition (`dev/LESSONS.md:3399-3444`). LJ-1.50-R and LJ-1.7-R are the
measured instances: the briefs cited P-u and prescribed the wrong half of it
(`lj-1.50-review.md:286-305`; commit `feba5dc`).

## 7. WHAT THIS AUDIT DID NOT DO

This audit did not edit a brief, a report, a master, a checker or a `dev/`
file. It did not run Agda, `make check`, a dispatch, a commit or a push. It
did not run `git checkout`, `git stash`, `git reset --hard` or `git clean`.
MEASURED: none of these happened.

## 8. ARCHIVE USED (DD18)

- `scripts/dd25-record.py`, read whole. TOOK the row regex at `:30`, the
  classifier at `:38-46` and its docstring at `:30-36`, and the rate line at
  `:87-95`. Ran it: output quoted in section 0.
- `dev/PLAN.md` rows `:529,:548,:550,:555,:559,:569,:571,:572,:574,:583,
  :588,:593,:596,:624` for the 14 verdicts; `:752,:769-770,:782-784` for the
  six uncounted reviews; `:258` for DD0; `:263` for DD8; `:274` for DD25;
  `:777` for the LJ-1.208 row.
- `agents/tasks/LJ-1-200/LJ-1.200-report.md` and
  `agents/tasks/LJ-1-201/LJ-1.201-report.md`, read WHOLE. TOOK the UPHELD
  BUT MISATTRIBUTED verdicts and their brief-cause sections.
- The 14 review files under `agents/tasks/archive/`, read at their verdict
  and brief-cause sections, cited throughout section 1.
- `agents/tasks/LJ-1-208/lj-1.208-report.md`, read whole. TOOK the wide
  review definition and the register's purpose.
- `agents/tasks/LJ-1-183/lj-1.183-report.md`, read whole. TOOK the admitted
  six and the DD4 census method.
- `agents/tasks/LJ-1-157/lj-1.157-report.md`, read whole. TOOK the shape: a
  fact returned by an agent does not persist unless the orchestrator
  re-injects it into later briefs.
- `agents/tasks/LJ-1-189/lj-1.189-report.md`, read whole. TOOK the finding
  that a lesson does not reach the writing moment, and the discipline that a
  proposal names its cure kind.
- `agents/tasks/LJ-1-206/lj-1.206-report.md` and commit `a06c6ed`, read.
  TOOK the third same-day case: the brief's instruction caused the outcome
  it then reported.
- `dev/LESSONS.md`: C-22, C-31, C-32, C-33, C-34, C-36, C-37, C-39 to C-43,
  D-10, D-26, D-29, D-30, P-l, I-5, read at their entries.
- `archive/dev/TASKS-archived.md:116` for T85, the cure LJ-1.6's agent never
  opened; `:260` for the T255 shape, an orchestrator refutation in the
  retired route. SHAPE TAKEN: the orchestrator's premise failures repeat
  across the route change. What does NOT transfer: the retired rows use a
  different numbering and predate DD25, so their review records do not enter
  the register.
- Commit bodies, read whole: `35cb762`, `a7e5bd0`, `b831e50`, `a4e4e11`,
  `5aa4bd6`, `3566676`, `931c13e`, `8019b6a`, `c88cb22`, `feba5dc`,
  `ce48c1e`, `c9ffa34`, `a06c6ed`.

## 9. LITERATURE USED (DD18)

Not this task's subject. None read.
