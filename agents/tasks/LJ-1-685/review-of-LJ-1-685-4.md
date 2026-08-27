# review-of-LJ-1-685-4: adversarial review of LJ-1.685#4

## HEAD
head_slot: mathematician_adversarial
machine: shared
task: LJ-1.685
attacked: the return of LJ-1.685#4, `agents/tasks/LJ-1-685/review-of-LJ-1-685-3.md`, with its acceptance arm `agents/tasks/LJ-1-685/runs/accept-5.out`
verdict: upheld

Upheld means: the predecessor review's verdict stands, and I state it
in full so the word cannot be misread. The predecessor (#4) upheld #3's
uphold of #2's overturn of the author's stale verdict line. The author's
line said the floor, the packing and the term "follow"
(`agents/tasks/LJ-1-685/lj-1.685-report.md:9-10`). The body delivers all
three, the first arm discharged the obligation
(`agents/tasks/LJ-1-685/runs/accept-1.out:16-23`, `:27`, `:32`), and the
only defect left in the author's return is its two unfilled survey
sections (`lj-1.685-report.md:90` and `:94`). I attacked #4's return for
its whole length. Every attack failed except one: its park-precedent
enumeration misses LJ-1.620, and that miss makes its own diagnosis
stronger, not weaker (section 2.3). The mathematics is a GO at the
strength the brief set. This upheld verdict does not close the task, for
the same measured reasons #4 gave, re-measured today on
`runs/accept-5.out`, and the clock is now one tick shorter: this return
is the last dispatch of the lint loop before the park (section 3).

This dispatch repeats the invariant breach #4 measured on its own, and I
report it in section 0 with the log line that proves it. The breach does
not change any fact under review and I did not let it change the
verdict.

## 0. THE INVARIANT, THE SIX FACTS, AND THE RECORD THIS REVIEW USED

**The invariant.** The author head is `coder`
(`agents/tasks/LJ-1-685/LJ-1.685.md:4`). Review #2 ran as
`coder_adversarial` (`agents/tasks/LJ-1-685/review-LJ-1-685-1.md:4`).
Review #3 ran as `mathematician_adversarial`
(`agents/tasks/LJ-1-685/review-LJ-1-685-2.md:4`). Review #4 ran as
`mathematician_adversarial`
(`agents/tasks/LJ-1-685/review-LJ-1-685-3.md:4`). THIS dispatch also
runs as `mathematician_adversarial`
(`agents/tasks/LJ-1-685/review-LJ-1-685-4.md:4`). The slot rule reads
"THE INVARIANT: the critic is never the author. A return your own head
produced goes to the other head"
(`dev/pod/instructions/mathematician_adversarial.md:39-40`). The design's
own rule is stronger and is model level: "The critic is never the same
model as the author" (`dev/memos/LJ-4-pod-program-design.md:2954`).

**The measurement.** The worktree's tracked transition log ends before
every instance of this task, exactly as the brief warned: it holds 4512
lines, its only LJ-1.685 line is seq 4510 to READY at
2026-08-26T19:00:05Z with `model: null` and `effort: null` at file line
4511, and its last line is seq 4511, LJ-1.681 to RUNNING at
2026-08-26T19:00:38Z (`dev/pod/transitions/2026-08.jsonl:4511`). I
re-measured all three numbers today; they are unchanged. Per the brief I
used the accept arms for the six facts. For the model and routing facts
I also read, read only, the main tree's live copy of the same log,
`/Users/alsg/Agentic/Bedrock/dev/pod/transitions/2026-08.jsonl`, which
runs past this worktree's base and now holds 4564 lines. What it carries
for this task:

| dispatch | attempt | role | model | live log line |
|---|---|---|---|---|
| author #1 | 0 | coder | grok-4.6 | :4532 (seq 4531) |
| review #2, first run | 1 | coder_adversarial | glm-5.3 | :4544 (seq 4543) |
| review #2, second run | 2 | coder_adversarial | glm-5.3 | :4549 (seq 4548) |
| review #3 | 3 | mathematician_adversarial | glm-5.3 | :4554 (seq 4553) |
| review #4 | 4 | mathematician_adversarial | glm-5.3 | :4559 (seq 4558) |
| this review #5 | 5 | mathematician_adversarial | glm-5.3 | :4564 (seq 4563), the last line |

So the breach #4 measured repeats at this dispatch and is now three
links long. At slot level: #3, #4 and this dispatch share one head, each
attacking the previous one's product. At model level: #4's critic was
the same model as #3's author (glm-5.3 over glm-5.3, `:4559` over
`:4554`), and this dispatch repeats it (glm-5.3 over glm-5.3, `:4564`
over `:4559`), against the design's sentence at `:2954`.

**The cause, in the program, unchanged since #4 reported it.** The row
that keeps routing these returns is `sys-lint-accept`
(`dev/pod/table.toml:790-800`, action `accept` at `:793`) and it sets no
head. The launch code picks the review head by the AD27 fallback:
`slot = t.head_slot or ("mathematician_adversarial" ...)` at
`scripts/pod/pod.py:5389-5391`. The fallback hard codes one head. Its
guard `reviewed()` only checks that THIS attempt was not already a
`mathematician_adversarial` dispatch (`scripts/pod/pod.py:2565-2576`).
Nothing in the path reads the previous return's author head or model, so
the fallback cannot see that it appoints the author's own head as the
critic. #4 reported this; no fix landed between its return and mine.

**The arm of the attacked return.** `runs/accept-5.out` carries: tier
wide, GHCRTS `-A64m -I0 -M2g` (`:5-6`), one Agda slot (`:7`), conjuncts
1 through 5 held and conjunct 6 FAILED (`:10-15`), no Agda run at all
because the slot refuses `.agda` writes and the eight probe files sit in
`changed_files_refused` with `runs_all: []` and `agda_vacuous: true`
(`:24`), changed files 31 with 1 own, the review file itself (`:16-17`,
`:24`), 0 in-fence lines (`:18`), obligations delta 0 and 0 open
(`:19`, `:24`), error class lint and exit 1 (`:21-22`). The eight
refused files were green at their last run
(`runs/accept-1.out:16-23`).

## 1. THE FOUR QUESTIONS, USED AS THE LENS

The four are DD25's, at `archive/dev/DD-archived.md:35`. No other list.

### 1.1 Is the verdict correct on its own numbers? YES.

#4's verdict line is "upheld", aimed at #3's uphold of #2's overturn of
the author's line at `lj-1.685-report.md:9-10`. The arms say that line
is false in the understating direction: the floor exploration
(`runs/FLOOR.agda.txt:87` carries the obligation with a hole;
`runs/floor-1.out` and `runs/floor-2.out` both end EXIT=42), the packing
(`runs/PACK.agda:27-28`, `pack∃` generic in the formula; sealed at
`runs/PACKAT.agda:27-56`; green at `runs/pack-2.out`, `packat-3.out`
through `packat-5.out`, all EXIT=0) and the term
(`agents/tasks/LJ-1-685/Probe685.agda:71-89`, rc 0 at 2.25 s,
`runs/accept-1.out:16`) all landed, with obligations delta -1 and 0 open
(`runs/accept-1.out:27`, `:32`). The two placeholders at
`lj-1.685-report.md:90` and `:94` are the residue of the C-22 skeleton
(`dev/LESSONS.md:2307`). #4 said this in the same words its body proves,
and the arms carry it.

### 1.2 Is the measurement sound? YES. I re-measured the decisive parts, and one of them is new.

- **The one check that decides this escalation.** I ran
  `scripts/pod/check-survey-quotes.py LJ-1.685` in THIS checkout before
  writing this file: rc 1, ten unanswered paths, byte for byte #4's
  list, the arms' `lint_detail` and my own brief's quoted lint output:
  `archive/dev/DD-archived.md`, `archive/dev/ORCHESTRATION.md`,
  `archive/dev/PLAN-archived.md`, `archive/dev/STATUS-archived.md`,
  `archive/dev/TASKS-archived.md`, `dev/literature/BIBLIOGRAPHY.md`,
  `dev/literature/devlin-errata.md`,
  `dev/literature/glossary-review-2026-08.md`,
  `dev/literature/level-formula-slot-roles.md`,
  `dev/literature/primary-sources.md`.
- **The pairing measurement, mine and new.** #4 read from the code that
  the gate never reads a review file. I measured both sides. Run as
  `check-survey-quotes.py --brief agents/tasks/LJ-1-685/LJ-1.685.md
  --report agents/tasks/LJ-1-685/review-of-LJ-1-685-3.md`, the checker
  prints "LJ-1-685 clean (0 note(s), 0 defect(s))" and returns 0. So the
  attacked return satisfies the survey duty, on the WORK BRIEF's own
  candidate lists, and the red at task-code pairing is caused by one
  thing only: `report_of` picks `lj-1.685-report.md` and its docstring
  refuses review companions, "A review companion is another dispatch's
  return and is not judged here"
  (`scripts/pod/check-survey-quotes.py:427-440`). No compliant review
  can ever turn conjunct 6 green, and the compliance of the review under
  attack is now measured, not inferred.
- **The six pinned members of conjunct 6** (`scripts/pod/accept.py:86-98`)
  all pass green in this checkout, re-run by me read only today:
  lint-agda, lint-prose, glossary, fences, probes, markers, each rc 0.
- **The `postulate` search** over the task home: no hit in any `.agda`
  or `.agda.txt` file.
- **The wall cap reading** is code backed: `runs/run.sh:2-3` says "The
  wall cap is perl's alarm: SIGALRM kills the exec'd agda", and
  `runs/w3-2.out` and `runs/w3-3.out` record EXIT=142 under it.
- **The routing chain**, now four routings deep in the live log: seq
  4537 routed `task-lj-1-685-accept-failed` (`:4538`), seq 4547 routed
  `sys-sigkill-escalate` (`:4548`), and `sys-lint-accept` routed three
  times, seq 4552 (`:4553`), seq 4557 (`:4558`) and seq 4562 (`:4563`),
  the last of which dispatched THIS return. #4's inference matched the
  record it could not fully read.

### 1.3 Did the BRIEF cause the outcome? NO for the work, YES for the loop, and every brief-side defect has now fired a FOURTH time.

The work brief funded the term and the term landed. The loop causes are
template side and #3 named the two; both are still live in MY OWN brief,
byte identical: the lint note commands "fix THIS, and re-run the
pre-commit checks yourself before you return" (generated at
`scripts/pod/pod.py:2678`, present at
`agents/tasks/LJ-1-685/review-LJ-1-685-4.md:17`), while the same brief's
scope line says the reader writes one file "and nothing else"
(`review-LJ-1-685-4.md:11`), and the only act that cures the named
check, measured in 1.2, is an edit to `lj-1.685-report.md`, outside that
scope. The wrong pointer is still wrong: `review-LJ-1-685-4.md:36`
points the three questions at
`dev/memos/LJ-4-pod-program-design.md:2853-2858`, a range that holds
branch disjointness (verified today at `:2855-2857`), while the
questions live at `:2984-2988` (verified). Four generated review briefs
of this task now carry both defects (`review-LJ-1-685-1.md:17`, `:36`;
`review-LJ-1-685-2.md:17`, `:36`; `review-LJ-1-685-3.md:17`, `:36`;
`review-LJ-1-685-4.md:17`, `:36`), and LJ-1.679's review recorded the
pointer defect before them
(`agents/tasks/LJ-1-679/review-of-LJ-1-679-1.md:32-36`). To those two I
add the third, the AD27 fallback at `scripts/pod/pod.py:5389-5391`,
which #4 measured and which fires a third time at this dispatch
(section 0).

### 1.4 Is there a cure the return missed? NO. The one cure stands, and this dispatch is its fifth measured proof.

A compliant review file was on disk at accept-2, accept-3, accept-4 and
accept-5, and conjunct 6 failed all four times with the same ten paths
(`runs/accept-2.out:15`, `runs/accept-3.out:15`,
`runs/accept-4.out:15`, `runs/accept-5.out:15`). The pairing
measurement of 1.2 closes the question: the gate reads the author's
report and refuses every review companion, so no review content can
cure it. The cure is one edit outside every review scope, and section 3
names it. Four facts, all measured today, make the cure more urgent
rather than less:

- **The clock is one tick from the end.** `sys-lint-accept` has routed
  three times in a row (`:4553`, `:4558`, `:4563`). The park fires when
  `same_row_runs(t, row_id, root) + 1 >= limits["attempt_max"]`
  (`scripts/pod/pod.py:5083-5084`), `attempt_max = 4`
  (`dev/pod/heads.toml:273`), and `same_row_runs` counts consecutive
  `CHECKING -> READY` lines of the same row from the log
  (`scripts/pod/pod.py:2577-2592`). The routing after THIS return's arm
  is the fourth consecutive match. This is the last dispatch of the
  loop.
- **The park is a designed signal, not a loss.** The program's own
  comment on that cap: "THE CAP NAMES THE ROW THAT KEPT MATCHING. That
  is a design error in the ROW and not in the task, and the park is how
  the maintainer learns of it" (`scripts/pod/pod.py:5085-5086`).
- **Three tasks have parked on this row, not two.** LJ-1.512
  (`dev/pod/queue.toml:3774-3777`), LJ-1.615 (`:5543`, `:5546`) and
  LJ-1.620 (`:5690-5691`), whose park shape is THIS task's shape
  exactly: a report whose cells still read "(FILLED)".
- **Recovery from this loop is real.** LJ-1.500 recovered on attempt 5
  from the same loop (`dev/pod/queue.toml:3775`).

## 2. THE THREE QUESTIONS, ANSWERED

These are section 6.6's own list. My brief points them at
`dev/memos/LJ-4-pod-program-design.md:2853-2858`; that range holds
branch disjointness, and the list lives at `:2984-2988`. I answer the
questions as worded.

1. **Does the predecessor's verdict LINE match its own BODY?** Yes. The
   line is "upheld" and the body defines the word in its second
   paragraph: the predecessor review's verdict stands, and that
   predecessor upheld the overturn of the author's stale line. The body
   proves exactly that with the arm's numbers (eight green runs at
   `runs/accept-1.out:16-23`, obligations delta -1 with 0 open at `:27`
   and `:32`, the term at `Probe685.agda:71-89`, the placeholders at
   `lj-1.685-report.md:90` and `:94`), it separates the return level
   defect from the work, and it withholds the close in section 3. The
   line claims exactly what the body proves. This is not the measured
   class of `[LJ-1.373]` and `[LJ-1.376]`: no verdict line here
   contradicts the body under it.
2. **Is every load-bearing claim backed by a `file:line` that resolves
   today?** Yes. I opened every citation in #4's return, by class: the
   checker (`scripts/pod/check-survey-quotes.py:421-425`, `:427-440`
   with the docstring "A review companion is another dispatch's return
   and is not judged here", `:450-452`, the DECLINE pattern at
   `:123-126`); the runner (`scripts/pod/accept.py:86-98`, `:99`,
   `:226-227`); the router (`scripts/pod/pod.py:2678`, `:1700-1703`,
   `:2565-2576`, `:5083-5086`, `:5389-5391`;
   `scripts/pod/table.toml:790-800` with `action = "accept"` at `:793`,
   `:803-816`, `:4317-4321`; `dev/pod/heads.toml:273`;
   `dev/pod/queue.toml:3774-3777`, `:5543`, `:5546`); the transitions
   record (worktree file line 4511, 4512 lines, last line seq 4511, all
   three re-measured today; live `:4532`, `:4538`, `:4544`, `:4548`,
   `:4549`, `:4553-4554`, `:4558-4559`, `:4563-4564`, all re-measured
   today); the arms (`runs/accept-1.out:5-6`, `:9`, `:10-15`, `:16-23`,
   `:21`, `:23-27`, `:29-30`, `:32`; `runs/accept-2.out:8`, `:15`, `:21`,
   `:25`, `:27-28`, `:30`;
   `runs/accept-3.out:15`; `runs/accept-4.out:10-15`, `:15`, `:16-19`,
   `:21-22`, `:24`; `runs/accept-5.out:5-7`, `:10-15`, `:16-19`,
   `:21-22`, `:24`); the probes and runs (`Probe685.agda:46-48`,
   `:66-69`, `:71-76`, `:71-89`; `runs/FLOOR.agda.txt:87`;
   `runs/PACK.agda:27-28`; `runs/PACKAT.agda:27-56`; `runs/W3.agda:10-12`;
   `runs/TRANS.agda:31`, `:36`, `:47-49`; `runs/PINS.agda:51-59`;
   `runs/run.sh:2-3`; `runs/floor-1.out`, `runs/floor-2.out` EXIT=42;
   `runs/pack-2.out`, `runs/packat-3.out`, `runs/packat-4.out`,
   `runs/packat-5.out` EXIT=0; `runs/w3-2.out`, `runs/w3-3.out`
   EXIT=142); the predecessor task homes
   (`agents/tasks/LJ-1-520/Probe520.agda:124-125`, `:160`, `:192-195`;
   `agents/tasks/LJ-1-678/Probe678.agda:27`, `:32`;
   `agents/tasks/LJ-1-684/Probe684.agda:69-72`;
   `agents/tasks/LJ-1-672/lj-1.672-report.md:9-11`, `:174-180`,
   `:184-185`; `agents/tasks/LJ-1-672/review-of-LJ-1-672-1.md:8`;
   `agents/tasks/LJ-1-672/runs/W3.agda:52`, `:67`;
   `agents/tasks/LJ-1-678/lj-1.678-report.md:9-10`, `:150-154`;
   `agents/tasks/LJ-1-679/review-of-LJ-1-679-1.md:32-36`); the src
   chapters (`src/L/Coding/Bound.lagda.md:93-94`, `:147-152`;
   `src/L/Hierarchy.lagda.md:334-335`;
   `src/L/Condensation.lagda.md:7390-7391`); and the records
   (`dev/LESSONS.md:2307`, `:1375`, `:3762`; `dev/pod/direction.md:37`;
   `archive/dev/DD-archived.md:35`;
   `dev/memos/LJ-4-pod-program-design.md:2854`, `:2855-2857`, `:2954`,
   `:2984-2988`; `dev/pod/instructions/coder_adversarial.md:28`;
   `agents/tasks/LJ-1-685/LJ-1.685.md:4`). Every one resolves today. I
   found no broken citation. One precision note, already carried by #4
   and true: line 194 of `Probe520.agda` is the forward conjunct, line
   195 the reverse, and the author's single line cite at
   `lj-1.685-report.md:66` names 194. The citation resolves; the line it
   names is the wrong member of the pair. That defect sits in the
   author's return, not in #4's, and it moves no number in any verdict.
3. **Is the predecessor's enumeration complete?** Complete at the level
   that decides the verdict, with ONE miss that I name. The enumeration
   of the reverse's inputs (powIter as a hypothesis, the bridge as a
   hypothesis, `IsOrd` in the k-value telescope, and nothing else,
   `Probe685.agda:71-76` against `lj-1.685-report.md:70-84`), of the
   four attack lines on the term, and of the routing after the return
   are each backed. The miss: #4 wrote that LJ-1.512 and LJ-1.615 are
   "the complete list of tasks parked on this row". LJ-1.620 also
   parked at `attempt_max:sys-lint-accept`
   (`dev/pod/queue.toml:5690-5691`), with this task's exact report
   shape, cells still reading "(FILLED)". The list has three members,
   not two. The miss strengthens the diagnosis and changes no part of
   the verdict. Four additions exist beyond it, all mine, and none
   changes the verdict either: the pairing measurement of 1.2, which
   proves review content compliant and the pairing alone at fault; the
   third `sys-lint-accept` routing (`:4563`), which dispatched this
   return and makes it the loop's last dispatch; the invariant breach
   at this dispatch itself (section 0); and LJ-1.500's recovery on
   attempt 5 (`dev/pod/queue.toml:3775`), which shows the loop is
   escapable before the cap.

## 3. WHY THIS UPHELD VERDICT CANNOT CLOSE THE TASK, WHAT FOLLOWS IT, AND THE ONE ACT THAT CHANGES THE ENDING

- **The gate reads the report, not any review.** Conjunct 6 runs
  `check-survey-quotes.py LJ-1.685` by task code
  (`scripts/pod/accept.py:226-227`); the checker pairs the work brief
  `LJ-1.685.md` (`scripts/pod/check-survey-quotes.py:421-425`) with
  `lj-1.685-report.md` (`:427-440`), and its docstring refuses review
  companions. Re-measured today: rc 1, the ten paths of section 1.2,
  and the pairing measurement of 1.2 shows the review side already
  clean. No file I may write is read by that check.
- **The closing row cannot fire.** Row `sys-critic-upheld-no-go` demands
  exit 0 and `obligations_open_min = 1` (`dev/pod/table.toml:4317-4321`).
  The obligation count is 0 (`runs/accept-5.out:24`), exit 0 is
  unreachable while the report is unfilled, and there is no NO-GO to
  uphold: the work is GO grade and the obligation is discharged.
  Measured on four arms before this one (`runs/accept-2.out:15`,
  `runs/accept-3.out:15`, `runs/accept-4.out:15`, `runs/accept-5.out:15`);
  this return is the fifth.
- **What follows this return, and its ground.** The author's report on
  disk is unchanged as I write, so conjunct 6 fails again, error
  class lint, exit 1, and row `sys-lint-accept`
  (`dev/pod/table.toml:790-800`) matches a fourth consecutive time.
  The cap parks the task (`scripts/pod/pod.py:5083-5084`;
  `dev/pod/heads.toml:273`; three routings spent at `:4553`, `:4558`,
  `:4563`). The task parks with a green probe, a discharged obligation
  and four review files on disk, the same end state as LJ-1.512,
  LJ-1.615 and LJ-1.620. The program's comment says the park is how the
  maintainer learns of a row design error (`scripts/pod/pod.py:5085-5086`),
  and this row has now burned four tasks on returns whose compliance
  the gate cannot read.
- **The repair, one act, unchanged through four reviews.** Fill
  `lj-1.685-report.md`'s `## ARCHIVE USED` and `## LITERATURE USED`
  sections: each of the ten paths of section 1.2 read at a line and
  quoted, or declined in writing. "A written decline is compliance"
  (`scripts/pod/check-survey-quotes.py:450-452`). The edit must land in
  THIS worktree's copy,
  `.pod-state/worktrees/LJ-1-685/agents/tasks/LJ-1-685/lj-1.685-report.md`,
  because the arm runs here. The author slot or the maintainer can do
  it in one edit. No review dispatch can: my scope is this file
  (`review-LJ-1-685-4.md:11`), and filling the author's survey sections
  with a critic's words would put my authorship inside the return under
  review. I refuse that for the reason #2 gave
  (`agents/tasks/LJ-1-685/review-of-LJ-1-685-1.md`, section 3, "Why I
  do not edit the report"). If the fill lands in this worktree before
  my arm runs, conjunct 6 goes green, the arm exits 0, and with
  `obligations_open: 0` the row that closes is
  `sys-obligations-satisfied` (`dev/pod/table.toml:803-816`), action
  `done`, outcome `go`. The task then closes GO without another
  dispatch.
- **If an arm that runs Agda dies at rc -9 with no Agda error name**,
  that is the load fact of `runs/accept-2.out:8` and `:21` again, not a
  fact about any return. The arm of THIS return runs no Agda
  (`runs/accept-5.out:24`, `runs_all: []`), so the note binds the next
  arm that does.

## 4. WHAT THE NEXT BRIEF, OR THE MAINTAINER, SHOULD CARRY

1. Address the fill to the author slot or the maintainer, never to a
   review slot. One edit in `lj-1.685-report.md`, in THIS worktree,
   named in section 3. The clock in section 3 says the task parks after
   this return unless it lands first.
2. No new mathematics. The obligation is discharged and green. Keep the
   restructured W3 shape: the generic pack in `runs/PACK.agda` plus the
   thin re-export in `runs/W3.agda:10-12`.
3. Fix the review brief pointer to
   `dev/memos/LJ-4-pod-program-design.md:2984-2988`. Five generated
   review briefs have now carried the wrong range: LJ-1.679's and all
   four of this task's.
4. Fix the lint note at `scripts/pod/pod.py:2678`: it has now commanded
   an out-of-scope act on four review briefs of this task. When the
   failing check reads a file outside the dispatch's scope, the note
   must name the maintainer as the actor.
5. Fix the AD27 fallback at `scripts/pod/pod.py:5389-5391` so the review
   head is never the previous return's author head, and the model is
   never the previous return's author model. Measured three times in
   this task's chain (section 0). Until it is fixed, a lint loop inside
   the adversarial family keeps reviewing itself.
6. Decide the gate side, if the task side is not preferred:
   `report_of` (`scripts/pod/check-survey-quotes.py:427-440`) refuses
   review companions, so a review round can never satisfy conjunct 6 on
   the author's report. Either the author's report is filled, or the
   gate, in a review round, must read the round's own return. The
   pairing measurement of 1.2 shows both what the gate reads today and
   what a compliant return looks like.
7. Read an rc -9 arm kill as load, per `runs/accept-2.out`, before
   pricing any "failure" it reports.

## 5. THE MATHEMATICIAN'S OWN CLAUSES, ON THIS RETURN

W1: no architecture decision is at stake; nothing here changes the
candidate status of the two towers. W2: the author's W2 answer stands
verified, the reverse is written once at a generic carrier
(`Probe685.agda:71-76`, `runs/PACK.agda:27-28`), and no fixed form was
required. W3 and A21: I name no probe and I write no `.agda` file; the
measurements this review needed were the program's own checks, which I
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
green, `check-survey-quotes.py LJ-1.685` returned rc 1 with the ten
paths named in section 1.2, and the pairing invocation of section 1.2
returned rc 0 on the attacked return. I read the main tree's live
transition log read only, outside this checkout, and I cited it as such
in section 0. I did not set `GHCRTS`. No commit, no push. The working
tree holds exactly this one new file from this dispatch.

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
