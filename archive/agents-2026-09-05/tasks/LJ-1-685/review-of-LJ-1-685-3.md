# review-of-LJ-1-685-3: adversarial review of LJ-1.685#3

## HEAD
head_slot: mathematician_adversarial
machine: shared
task: LJ-1.685
attacked: the return of LJ-1.685#3, `agents/tasks/LJ-1-685/review-of-LJ-1-685-2.md`, with its acceptance arm `agents/tasks/LJ-1-685/runs/accept-4.out`
verdict: **upheld**

Upheld means: the predecessor review's verdict stands, and I state it in
full so the word cannot be misread. The predecessor (#3) upheld #2's
overturn of the author's stale verdict line. The author's line said the
floor, the packing and the term "follow"
(`agents/tasks/LJ-1-685/lj-1.685-report.md:9-10`). The body delivers all
three, the first arm discharged the obligation
(`agents/tasks/LJ-1-685/runs/accept-1.out:16-23`, `:27`, `:32`), and the
only defect left in the author's return is its two unfilled survey
sections (`lj-1.685-report.md:90` and `:94`). I attacked #3's return for
its whole length and every attack failed. The mathematics is a GO at the
strength the brief set. This upheld verdict does not close the task, for
the same two measured reasons #3 gave, re-measured today on
`runs/accept-4.out` (section 3).

This return also carries one finding that is MINE and not the
predecessor's: the dispatch that carries it breaks the critic invariant.
The return I attack was produced by my own head slot, and by the same
model. Section 0 gives the measurement, and section 4 names the program
line that causes it. The breach does not change any fact under review,
and I did not let it change the verdict. I report it because a critic
that hides a defect in its own dispatch is worth less than the return it
attacks.

## 0. THE INVARIANT, THE SIX FACTS, AND THE RECORD THIS REVIEW USED

**The invariant.** The author head is `coder`
(`agents/tasks/LJ-1-685/LJ-1.685.md:4`). Review #2 ran as
`coder_adversarial` (`agents/tasks/LJ-1-685/review-LJ-1-685-1.md:4`).
Review #3 ran as `mathematician_adversarial`
(`agents/tasks/LJ-1-685/review-LJ-1-685-2.md:4`). THIS dispatch also
runs as `mathematician_adversarial`
(`agents/tasks/LJ-1-685/review-LJ-1-685-3.md:4`). The slot rule reads
"THE INVARIANT: the critic is never the author. A return your own head
produced goes to the other head"
(`dev/pod/instructions/mathematician_adversarial.md:39-40`). This
dispatch attacks a return its own head produced. The design's own rule
is stronger and is model level: "The critic is never the same model as
the author" (`dev/memos/LJ-4-pod-program-design.md:2954`).

**The measurement.** The worktree's tracked transition log ends before
every instance of this task, exactly as the brief warned: it holds 4512
lines, its only LJ-1.685 line is seq 4510 to READY at
2026-08-26T19:00:05Z with `model: null` and `effort: null` at file line
4511, and its last line is seq 4511, LJ-1.681 to RUNNING at
2026-08-26T19:00:38Z (`dev/pod/transitions/2026-08.jsonl:4511`). Per the
brief I used the accept arms for the six facts. For the model and
routing facts I also read, read only, the main tree's live copy of the
same log, `/Users/alsg/Agentic/Bedrock/dev/pod/transitions/2026-08.jsonl`,
which runs past this worktree's base and holds 4559 lines. What it
carries for this task:

| dispatch | attempt | role | model | effort | live log line |
|---|---|---|---|---|---|
| author #1 | 0 | coder | grok-4.6 | high | :4532 (seq 4531) |
| review #2, first run | 1 | coder_adversarial | glm-5.3 | (empty) | :4544 (seq 4543) |
| review #2, second run | 2 | coder_adversarial | glm-5.3 | (empty) | :4549 (seq 4548) |
| review #3 | 3 | mathematician_adversarial | glm-5.3 | (empty) | :4554 (seq 4553) |
| this review #4 | 4 | mathematician_adversarial | glm-5.3 | (empty) | :4559 (seq 4558), the last line |

So the breach is measured twice over. At slot level: #3 and this
dispatch share one head. At model level: #3's critic was the same model
as #2's author (glm-5.3 over glm-5.3, `:4549` over `:4544`), and this
dispatch repeats it (glm-5.3 over glm-5.3, `:4559` over `:4554`).
Against the design's sentence at `:2954` the chain broke one dispatch
before anyone could see it. #3's section 0 claim, "Three heads, no
overlap", was true at slot level and was everything its sources could
show: its log copy carried no model fact, and no accept arm carries one.

**The cause, in the program.** The routing line that sent this dispatch
out is seq 4557 (`:4558`): row `sys-lint-accept`, action `accept`, no
head slot set. The launch code then picks the review head by fallback:
`slot = t.head_slot or ("mathematician_adversarial" ...)` at
`scripts/pod/pod.py:5389-5391`. The fallback hard codes one head. Its
guard `reviewed()` only checks that THIS attempt was not already a
`mathematician_adversarial` dispatch (`scripts/pod/pod.py:2565-2576`).
Nothing in the path reads the previous return's author head or model, so
the fallback cannot see that it is appointing the author's own head as
the critic. This is the same class of template defect as the two #3
reported, and it is measured on this task twice (section 1.3).

**The arm of the attacked return.** `runs/accept-4.out` carries: tier
wide, GHCRTS `-A64m -I0 -M2g` (`:5-6`), one Agda slot (`:7`), conjuncts
1 through 5 held and conjunct 6 FAILED (`:10-15`), no Agda run at all
because the slot refuses `.agda` writes and the eight probe files sit in
`changed_files_refused` with `runs_all: []` and `agda_vacuous: true`
(`:24`), changed files 30 with 1 own, the review file itself (`:16-17`,
`:24`), 0 in-fence lines (`:18`), obligations delta 0 and 0 open
(`:19`, `:24`), error class lint and exit 1 (`:21-22`). The eight
refused files were green at their last run
(`runs/accept-3.out:16-23`).

## 1. THE FOUR QUESTIONS, USED AS THE LENS

The four are DD25's, at `archive/dev/DD-archived.md:35`. No other list.

### 1.1 Is the verdict correct on its own numbers? YES.

#3's verdict line is "upheld", aimed at #2's overturn of the author's
line at `lj-1.685-report.md:9-10`. Its own numbers say that line is
false in the understating direction: the floor exploration
(`runs/FLOOR.agda.txt:87` carries the obligation with a hole;
`runs/floor-1.out` and `runs/floor-2.out` both end EXIT=42), the packing
(`runs/PACK.agda:27-28`, `pack∃` generic in the formula; sealed at
`runs/PACKAT.agda:27-56`; green at `runs/pack-2.out`, `packat-3.out`
through `packat-5.out`, all EXIT=0) and the term
(`agents/tasks/LJ-1-685/Probe685.agda:71-89`, rc 0 at 2.25 s,
`runs/accept-1.out:16`) all landed, with obligations delta -1 and 0 open
(`runs/accept-1.out:27`, `:32`). The two placeholders at
`lj-1.685-report.md:90` and `:94` are the residue of the C-22 skeleton
(`dev/LESSONS.md:2307`). #3 said this in the same words its body
proves, and the arms carry it.

### 1.2 Is the measurement sound? YES. I re-measured the decisive parts.

- **The one check that decides this escalation.** I ran
  `scripts/pod/check-survey-quotes.py LJ-1.685` in THIS checkout before
  writing this file: rc 1, ten unanswered paths, byte for byte #3's
  list and the arms' `lint_detail`: `archive/dev/DD-archived.md`,
  `archive/dev/ORCHESTRATION.md`, `archive/dev/PLAN-archived.md`,
  `archive/dev/STATUS-archived.md`, `archive/dev/TASKS-archived.md`,
  `dev/literature/BIBLIOGRAPHY.md`, `dev/literature/devlin-errata.md`,
  `dev/literature/glossary-review-2026-08.md`,
  `dev/literature/level-formula-slot-roles.md`,
  `dev/literature/primary-sources.md`.
- **The full conjunct 6 member set, re-run today.** The six pinned
  members (`scripts/pod/accept.py:86-98`) all pass green in this
  checkout: lint-agda, lint-prose, glossary, fences, probes, markers.
  Only the survey member fails, and it fails on
  `lj-1.685-report.md`, a file no review may touch.
- **The `postulate` search** over the task home: no hit in any `.agda`
  or `.agda.txt` file.
- **The wall cap reading** is code backed: `runs/run.sh:2-3` says "The
  wall cap is perl's alarm: SIGALRM kills the exec'd agda", and
  `runs/w3-2.out` and `runs/w3-3.out` record EXIT=142 under it.
- **The routing chain**, which #3 could only infer from the arms, is
  now measured from the live log's four routing lines: seq 4537 routed
  `task-lj-1-685-accept-failed` (`:4538`), seq 4547 routed
  `sys-sigkill-escalate` (`:4548`), seq 4552 routed `sys-lint-accept`
  (`:4553`), seq 4557 routed `sys-lint-accept` (`:4558`). #3's
  inference matches the record it could not read.

### 1.3 Did the BRIEF cause the outcome? NO for the work, YES for the loop, and every brief side defect has now fired a THIRD time.

The work brief funded the term and the term landed. The loop causes are
template side and #3 named both. Both are still live in MY OWN brief,
byte identical: the lint note commands "fix THIS, and re-run the
pre-commit checks yourself before you return" (generated at
`scripts/pod/pod.py:2678`, present at
`agents/tasks/LJ-1-685/review-LJ-1-685-3.md:17`), while the same brief's
scope line says the reader writes one file "and nothing else"
(`review-LJ-1-685-3.md:11`), and the only act that cures the named
check is an edit to `lj-1.685-report.md`, outside that scope. The wrong
pointer is still wrong: `review-LJ-1-685-3.md:36` points the three
questions at `dev/memos/LJ-4-pod-program-design.md:2853-2858`, a range
that holds branch disjointness (verified today at `:2855-2857`), while
the questions live at `:2984-2988` (verified). Three generated review
briefs of this task now carry both defects (`review-LJ-1-685-1.md:17`,
`:36`; `review-LJ-1-685-2.md:17`, `:36`; `review-LJ-1-685-3.md:17`,
`:36`), and LJ-1.679's review recorded the pointer defect before them
(`agents/tasks/LJ-1-679/review-of-LJ-1-679-1.md:32-36`). To those two I
add the third template defect, measured at this dispatch and not
visible before it: the AD27 fallback at `scripts/pod/pod.py:5389-5391`
names one review head and never checks the previous return's author, so
a lint loop inside the adversarial family reviews itself (section 0).

### 1.4 Is there a cure the return missed? NO. The one cure stands, and this dispatch is its fourth measured proof.

A compliant review file was on disk at accept-2, at accept-3 and at
accept-4, and conjunct 6 failed all three times with the same ten paths
(`runs/accept-2.out:15`, `runs/accept-3.out:15`, `runs/accept-4.out:15`).
The gate reads the report and refuses review companions by docstring
(`scripts/pod/check-survey-quotes.py:427-440`). This return is the
fourth instance of the same measurement. The cure is one edit outside
every review scope, and section 3 names it. Two facts #3 did not carry,
both measured today, and both making the cure more urgent rather than
less:

- **The clock.** Row `sys-lint-accept` has TWO consecutive CHECKING to
  READY lines in the live log (`:4553`, `:4558`). The cap is
  `attempt_max = 4` (`dev/pod/heads.toml:273`), and the park fires when
  prior consecutive runs of the row plus one reach it
  (`scripts/pod/pod.py:5083-5085`). So at most ONE more review dispatch
  follows this one before LJ-1.685 parks at
  `attempt_max:sys-lint-accept`, with a green probe and a closed
  obligation. LJ-1.512 parked exactly so
  (`dev/pod/queue.toml:3774-3777`) and LJ-1.615 parked on the fourth
  consecutive match of this same row (`dev/pod/queue.toml:5543`,
  `:5546`). Those two are the complete list of tasks parked on this
  row; #3 named both.
- **The happy path, now precise.** The arm of a mathematician_adversarial
  return runs no Agda (`runs/accept-4.out:24`, `runs_all: []`), so no
  load kill can mask it. If `lj-1.685-report.md`'s two survey sections
  are filled in THIS worktree before the next arm runs, conjunct 6 goes
  green, the arm exits 0, and with `obligations_open: 0` the row that
  matches is `sys-obligations-satisfied` (`dev/pod/table.toml:803-816`,
  `obligations_open_max = 0`), action `done`, outcome `go`. The task
  then closes GO on the next arm. It does not need the critic row.

## 2. THE THREE QUESTIONS, ANSWERED

These are section 6.6's own list. My brief points them at
`dev/memos/LJ-4-pod-program-design.md:2853-2858`; that range holds
branch disjointness, and the list lives at `:2984-2988`. I answer the
questions as worded.

1. **Does the predecessor's verdict LINE match its own BODY?** Yes. The
   line is "upheld" and the body defines the word in its second
   paragraph: the predecessor review's verdict stands, and that
   predecessor overturned the author's stale line. The body proves
   exactly that with the arm's numbers (eight green runs at
   `runs/accept-1.out:16-23`, obligations delta -1 with 0 open at
   `:27` and `:32`, the term at `Probe685.agda:71-89`, the placeholders
   at `lj-1.685-report.md:90` and `:94`), it separates the return level
   defect from the work, and it withholds the close in section 3. The
   line claims exactly what the body proves. This is not the measured
   class of `[LJ-1.373]` and `[LJ-1.376]`: no verdict line here
   contradicts the body under it.
2. **Is every load-bearing claim backed by a `file:line` that resolves
   today?** Yes. I opened every citation in #3's return, by class: the
   arms (`runs/accept-1.out:5-6`, `:9`, `:10-15`, `:16-23`, `:21`,
   `:23-27`, `:29-30`, `:32`; `runs/accept-2.out:8`, `:15`, `:21`,
   `:25`, `:27-28`, `:30`); the checker
   (`scripts/pod/check-survey-quotes.py:421-425`, `:427-440` with the
   docstring "A review companion is another dispatch's return and is
   not judged here", `:450-452`, the DECLINE pattern at `:123-126`);
   the router (`scripts/pod/pod.py:2678`, `:1700-1703`;
   `scripts/pod/accept.py:226-227`; `dev/pod/table.toml:790-800` with
   `action = "accept"` at `:793`, and `:4317-4321`;
   `dev/pod/queue.toml:3774-3777`, `:5543`, `:5546`); the transitions
   record (file line 4511, 4512 lines, last line seq 4511, all three
   re-measured today); the probes and runs (`Probe685.agda:46-48`,
   `:66-69`, `:71-89`; `runs/FLOOR.agda.txt:87`; `runs/PACK.agda:27-28`;
   `runs/PACKAT.agda:27-56`; `runs/W3.agda:10-12`; `runs/TRANS.agda:31`,
   `:36`, `:47-49`; `runs/PINS.agda:51-59`; `runs/run.sh:2-3`); the
   predecessor task homes (`agents/tasks/LJ-1-520/Probe520.agda:124-125`,
   `:160`, `:192-195`; `agents/tasks/LJ-1-678/Probe678.agda:27`, `:32`;
   `agents/tasks/LJ-1-684/Probe684.agda:69-72`;
   `agents/tasks/LJ-1-672/lj-1.672-report.md:9-11`, `:174-180`,
   `:184-185`; `agents/tasks/LJ-1-672/review-of-LJ-1-672-1.md:8`;
   `agents/tasks/LJ-1-672/runs/W3.agda:52`, `:67`;
   `agents/tasks/LJ-1-678/lj-1.678-report.md:9-10`, `:150-154`;
   `agents/tasks/LJ-1-679/review-of-LJ-1-679-1.md:32-36`); the src
   chapters (`src/L/Coding/Bound.lagda.md:93-94`, `:147-152`;
   `src/L/Hierarchy.lagda.md:334-335`;
   `src/L/Condensation.lagda.md:7390-7391`); and the records
   (`dev/LESSONS.md:2307`, `:1375`, `:3762`;
   `dev/pod/direction.md:37`; `archive/dev/DD-archived.md:35`;
   `dev/pod/instructions/coder_adversarial.md:28`;
   `agents/tasks/LJ-1-685/LJ-1.685.md:4`). Every one resolves today. I
   found no broken citation. I re-derived #3's N2 myself: line 194 of
   `Probe520.agda` is the forward conjunct, line 195 the reverse, and
   the author's single line cite at `lj-1.685-report.md:66` names 194.
3. **Is the predecessor's enumeration complete?** Complete at the level
   that decides the verdict. The enumeration of the reverse's inputs
   (powIter as a hypothesis, the bridge as a hypothesis, `IsOrd` in the
   k-value telescope, and nothing else, `Probe685.agda:71-76` against
   `lj-1.685-report.md:70-84`), of the four attack lines on the term,
   and of the routing after the return (LJ-1.512 and LJ-1.615 are the
   only two tasks parked on `sys-lint-accept`, and #3 named both) are
   each complete and each backed. Three additions exist, all mine, and
   none changes the verdict. First, the model facts of section 0 and
   the invariant breach they measure, which no earlier reviewer's
   sources could show. Second, the attempt budget: two of four
   consecutive `sys-lint-accept` runs are spent, so at most one more
   review dispatch remains before the park. Third, the closing row on
   the happy path: `sys-obligations-satisfied`, not the critic row,
   ends this task once the report is filled.

## 3. WHY THIS UPHELD VERDICT CANNOT CLOSE THE TASK, AND THE ONE ACT THAT CAN

- **The gate reads the report, not any review.** Conjunct 6 runs
  `check-survey-quotes.py LJ-1.685` by task code
  (`scripts/pod/accept.py:226-227`); the checker pairs the work brief
  `LJ-1.685.md` (`scripts/pod/check-survey-quotes.py:421-425`) with
  `lj-1.685-report.md` (`:427-440`), and its docstring refuses review
  companions. Re-measured today: rc 1, the ten paths of section 1.2.
  No file I may write is read by that check.
- **The closing row cannot fire.** Row `sys-critic-upheld-no-go`
  demands exit 0 and `obligations_open_min = 1`
  (`dev/pod/table.toml:4317-4321`). The obligation count is 0
  (`runs/accept-4.out:24`), exit 0 is unreachable while the report is
  unfilled, and there is no NO-GO to uphold: the work is GO grade and
  the obligation is discharged. Measured on three arms before this one
  (`runs/accept-2.out:15`, `runs/accept-3.out:15`,
  `runs/accept-4.out:15`); this return is the fourth.
- **The loop that follows, and its clock.** A lint red routes to
  `sys-lint-accept` (`dev/pod/table.toml:790-800`), whose action is
  `accept` (`:793`), and the loop repeats until `attempt_max` parks the
  task (`scripts/pod/pod.py:5083-5085`;
  `dev/memos/LJ-4-pod-program-design.md:2854`). The cap is 4
  (`dev/pod/heads.toml:273`) and two consecutive runs are spent
  (section 1.4). Without an act outside this slot, LJ-1.685 is the
  third task to park on this row, after LJ-1.512 and LJ-1.615.
- **The repair, one act, unchanged through three reviews.** Fill
  `lj-1.685-report.md`'s `## ARCHIVE USED` and `## LITERATURE USED`
  sections: each of the ten paths of section 1.2 read at a line and
  quoted, or declined in writing. "A written decline is compliance"
  (`scripts/pod/check-survey-quotes.py:450-452`). The edit must land in
  THIS worktree's copy,
  `.pod-state/worktrees/LJ-1-685/agents/tasks/LJ-1-685/lj-1.685-report.md`,
  because the arm runs here. The author slot or the maintainer can do
  it in one edit. No review dispatch can: my scope is this file
  (`review-LJ-1-685-3.md:11`), and filling the author's survey
  sections with a critic's words would put my authorship inside the
  return under review. I refuse that for the reason #2 gave
  (`agents/tasks/LJ-1-685/review-of-LJ-1-685-1.md`, section 3).
- **If an arm that runs Agda dies at rc -9 with no Agda error name**,
  that is the load fact of `runs/accept-2.out:8` and `:21` again, not a
  fact about any return. The arm of THIS return runs no Agda
  (`runs/accept-4.out:24`), so the note binds the next arm that does.

## 4. WHAT THE NEXT BRIEF SHOULD CARRY

1. Address the fill to the author slot or the maintainer, never to a
   review slot. One edit in `lj-1.685-report.md`, in THIS worktree,
   named in section 3. The clock in section 1.4 says it lands before
   the next arm or the task parks.
2. No new mathematics. The obligation is discharged and green. Keep the
   restructured W3 shape: the generic pack in `runs/PACK.agda` plus the
   thin re-export in `runs/W3.agda:10-12`.
3. Fix the review brief pointer to
   `dev/memos/LJ-4-pod-program-design.md:2984-2988`. Four generated
   review briefs have now carried the wrong range: LJ-1.679's and all
   three of this task's.
4. Fix the lint note at `scripts/pod/pod.py:2678`: it has now commanded
   an out-of-scope act on three review briefs of this task
   (`review-LJ-1-685-1.md:17`, `review-LJ-1-685-2.md:17`,
   `review-LJ-1-685-3.md:17`). When the failing check reads the
   predecessor's return, the note must name the maintainer as the
   actor.
5. Fix the AD27 fallback at `scripts/pod/pod.py:5389-5391` so the
   review head is never the previous return's author head, and the
   model is never the previous return's author model. Measured twice
   in this task's chain (section 0). Until it is fixed, a lint loop
   inside the adversarial family keeps reviewing itself, and the
   invariant that #3 could verify for its own dispatch is unverifiable
   by construction for every dispatch after it.
6. Read an rc -9 arm kill as load, per `runs/accept-2.out`, before
   pricing any "failure" it reports.

## 5. THE MATHEMATICIAN'S OWN CLAUSES, ON THIS RETURN

W1: no architecture decision is at stake; nothing here changes the
candidate status of the two towers. W2: the author's W2 answer stands
verified, the reverse is written once at a generic carrier
(`Probe685.agda:71-76`, `runs/PACK.agda:27-28`), and no fixed form was
required. W3 and A21: I name no probe and I write no `.agda` file; the
one measurement this review needed was the program's own check, which I
re-ran read only, plus the pinned pre-commit members. W4: no module is
retired here. W7: the probe consumes `[LJ-1.520]`'s shape and introduces
no object-language index. W8: I write no Agda and open no provability
question, so no literature stop arises; the bridge stays a hypothesis.

## 6. THE STANDING DIRECTION

No conflict. `dev/pod/direction.md:37` orders one SRC collection after
LJ-1 as a whole, not after `[LJ-2.5]`. This task is LJ-1 work, it
starts no collection and no phase 3, and the predecessor's reading
stands.

## 7. WHAT I DID AND DID NOT DO

I wrote this file and nothing else. I wrote no `.agda` file and no
`runs/` file, and I started no Agda process: this slot attacks a return
and never re-runs it (`scripts/pod/pod.py:1700-1703`). I re-ran the
conjunct 6 members myself, read only: the six pinned members passed
green and `check-survey-quotes.py LJ-1.685` returned rc 1 with the ten
paths named in section 1.2. I read the main tree's live transition log
read only, outside this checkout, and I cited it as such in section 0.
I did not set `GHCRTS`. No commit, no push. The working tree holds
exactly this one new file from this dispatch.

## ARCHIVE USED

- **`archive/dev/DD-archived.md` READ.** `archive/dev/DD-archived.md:35`
  reads "The questions are: is the refusal correct on its own numbers;
  is the measurement sound; did the BRIEF cause the outcome; and is
  there a cure the return missed." This is the four-question lens of
  section 1, and I used no other list.
- **`archive/dev/ORCHESTRATION.md` DECLINED.** Not read. The dispatch
  rules of the retired route decide nothing here; the live routing
  facts are in `scripts/pod/` and `dev/pod/table.toml`, both read at
  their lines.
- **`archive/dev/PLAN-archived.md` DECLINED.** Not read. The live
  status is `dev/pod/screen.toml`, and no planning history bears on
  this verdict.
- **`archive/dev/measurements/README.md` DECLINED.** Not read. This
  review audits returns and arms that already exist; it commissions no
  new measurement protocol.
- **`archive/dev/README.md` DECLINED.** Not read. A guide to the
  retired archive; no retrieval was needed beyond the one file used
  above.
- **`archive/dev/STATUS-archived.md` DECLINED.** Not read. The failing
  check names this path against the work brief; the live status is
  `dev/pod/screen.toml` and no archived status decides this verdict.
- **`archive/dev/TASKS-archived.md` DECLINED.** Not read. The failing
  check names this path against the work brief; the dispatch history
  this review needed is in the transitions log and the accept arms,
  both read at their lines.

## LITERATURE USED

- **`dev/literature/BIBLIOGRAPHY.md` DECLINED.** Not read. No source
  was added and none was missing; the obligation under review is
  discharged.
- **`dev/literature/devlin-errata.md` DECLINED.** Not read. This review
  quotes no scanned certificate and certifies no Devlin leaf.
- **`dev/literature/primary-sources.md` DECLINED.** Not read. The
  bridge stays a hypothesis, so no primary text decides anything in
  this verdict.
- **`dev/literature/level-formula-slot-roles.md` DECLINED.** Not read.
  The term's strength is fixed by the brief's own hypothesis list, not
  by the bound's role in Devlin's text.
- **`dev/literature/glossary-review-2026-08.md` DECLINED.** Not read.
  No naming question arose and this review proposes no
  `dev/glossary.toml` entry.
