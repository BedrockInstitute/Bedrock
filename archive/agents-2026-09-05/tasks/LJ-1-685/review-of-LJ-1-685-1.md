# review-of-LJ-1-685-1: adversarial review of LJ-1.685#1

## HEAD
head_slot: coder_adversarial
machine: shared
task: LJ-1.685
attacked: the return of LJ-1.685#1, `agents/tasks/LJ-1-685/lj-1.685-report.md`, with its acceptance arm `agents/tasks/LJ-1-685/runs/accept-1.out`
verdict: **overturned**

The predecessor's verdict line says the work is in progress and that
"Floor, packing, and the term follow" (`agents/tasks/LJ-1-685/lj-1.685-report.md:9-10`).
The body under that line is complete. The floor, the packing and the term are
all delivered, all eight `.agda` files typecheck, and the acceptance arm
discharged the obligation. I overturn the stated verdict line, because it is
false against the body it heads. The mathematics stands. The return fails as a
return: its two survey sections are placeholders, and that defect is the one
the first escalation named. Section 3 gives the evidence that a review
dispatch cannot cure it, names the act that can, and records the measured
proof that a compliant review alone changes nothing.

This dispatch is the SECOND run of this review slot on this task. The first
run wrote this same file, and its acceptance failed (`runs/accept-2.out`,
recorded in section 0). I read that draft as a find, not as a fact: I opened
every citation in it myself. Six of its line numbers were wrong, and I
corrected them here (the powIter note, the floor hole, three arm lines and
one checker line). Every cite below is one I resolved today.

## 0. THE INVARIANT, AND THE RECORD THIS REVIEW USED

The author head slot is `coder` (`agents/tasks/LJ-1-685/LJ-1.685.md:4`). This
review runs as `coder_adversarial`. The critic is not the author
(`dev/pod/instructions/coder_adversarial.md:28`).

`dev/pod/transitions/2026-08.jsonl` carries ONE line for this task: seq 4510,
attempt 0, `to: READY` at 2026-08-26T19:00:05Z, with `model: null`,
`effort: null` and `heads_sha256: 665f7468` (file line 4511). The file holds
4512 lines and its last line is seq 4511, another task, LJ-1.681 sent to
RUNNING at 2026-08-26T19:00:38Z. The log ends before the author instance and
before both review instances. It carries no model or effort fact for any of
them. Per the brief, I used the accept arm.

`runs/accept-1.out` carries the six facts of the attacked run: tier `wide`,
GHCRTS `-A64m -I0 -M2g` (`:5-6`), conjuncts 1 through 5 held and conjunct 6
FAILED (`:10-15`), eight `.agda` runs all rc 0 with `Probe685.agda` rc 0 at
2.25 s (`:16-23`), 36 changed files all own (`:24-25`), 0 in-fence lines
(`:26`), obligations delta -1 (`:27`), error class `lint` and exit 1
(`:29-30`). The JSON record on `:32` carries `obligations_open: 0`,
`heap_wall: false` and `agda_vacuous: false`.

`runs/accept-2.out` is the arm of the FIRST review instance's return, not of
the return I attack. It measured three things this review uses. One: conjunct
6 FAILED again (`:15`) although a fully compliant review file was on disk,
with the same survey text as accept-1. Two: conjunct 1 FAILED because
`runs/RENAME3.agda` died at rc -9 after 0.47 s (`:21`), with `heap_wall:
false`, no Agda error name (`error_names_all: []`, `:30`), and machine load
5.3 to 5.9 with two Agda slots running (`:8`). The same file is green in
accept-1 at rc 0, 1.61 s (`accept-1.out:21`). That kill is a machine fact,
not a fact about any return. Three: obligations stayed at delta 0, 0 open
(`:25`, `:30`). The arm exited -9, error class `other` (`:27-28`).

One pointer defect in MY OWN brief, recorded because evidence is `file:line`.
My brief and my slot file both point the three questions at
`dev/memos/LJ-4-pod-program-design.md:2853-2858`. That range holds text about
branch disjointness, not the questions. The three questions are at
`dev/memos/LJ-4-pod-program-design.md:2984-2988`. The LJ-1.679 review
recorded the same defect (`agents/tasks/LJ-1-679/review-of-LJ-1-679-1.md:32-36`)
and it persists. I answered the questions as worded in the brief.

## 1. THE FOUR QUESTIONS, USED AS THE LENS

The four are DD25's, at `archive/dev/DD-archived.md:35`, and no other list.

### 1.1 Is the verdict correct on its own numbers? NO, and only by understating.

The verdict line claims three things still follow: floor, packing, the term.
The arm says all three landed. The floor explorations are
`runs/FLOOR.agda.txt`, which states the obligation with a hole at `:87`
(`same-as-graph-reverse-at = {!!}`), run by `runs/floor-1.out` and
`runs/floor-2.out`, both EXIT=42. The packing is `runs/PACK.agda`, generic in
the formula (`pack∃` takes `φ` as an argument, `PACK.agda:27-28`), sealed at
`runs/PACKAT.agda:27-56`, green at `pack-2.out`, `packat-3.out` to
`packat-5.out`, all EXIT=0. The term is
`agents/tasks/LJ-1-685/Probe685.agda:71-89`, rc 0 at 2.25 s
(`runs/accept-1.out:16`). Obligations delta -1 with 0 open (`:27` and `:32`).
Every number the report does state is true; the report states almost no
numbers, because it was never finished. The line is stale C-22 skeleton text:
the report itself says at `:12-13` it was "Written as a skeleton before any
Agda", and the two survey sections still read "(filled at return)" at `:90`
and `:94`. The C-22 entry is `dev/LESSONS.md:2307`.

### 1.2 Is the measurement sound? YES.

The arm is the measurement and it is sound on its own terms. It started at
04:37:21 (`accept-1.out:9`), after the newest probe edit on disk,
`Probe685.agda` at 04:35 by file mtime in this checkout. It ran in this
checkout, under the same caliber this pane carries, `-A64m -I0 -M2g` wide
(`:5`). The predecessor's own run records corroborate it: `runs/lift-1.out`,
`pins-1.out`, `trans-1.out`, `pack-2.out`, `packat-3.out` to `packat-5.out`
and `p-3.out` all end EXIT=0 under `GHCRTS=[-A64m -I0 -M2g]`.

The walls were handled by the book. `w3-2.out` and `w3-3.out` record
EXIT=142 kills by the run wrapper's own wall cap (`runs/run.sh`: the cap is
perl's alarm, SIGALRM). The author restructured in the same dispatch: the
generic pack moved to `runs/PACK.agda` with an explicit formula argument
(green at `pack-2.out`), and `runs/W3.agda:10-12` became a thin re-export of
it, one `open import ... public` line at `:12`. The arm then runs `W3.agda`
rc 0 at 0.86 s (`runs/accept-1.out:23`). That is the owner's 2026-08-23
heap-wall ruling obeyed: restructure, then test the new shape under the same
cap. The report never records this restructure. The evidence lives only in
`runs/`.

The report's own head claims all check: no `postulate` occurs in any `.agda`
or `.agda.txt` file of this task home, which I measured by search today;
nothing under `src/` changed, 36 of 36 changed files are inside
`agents/tasks/LJ-1-685/` (`accept-1.out:24-25`); and the 0 in-fence figure is
the arm's `:26`.

### 1.3 Did the BRIEF cause the outcome? NO for the work, NO for the lint red, YES for one defect in the first review brief.

The work brief funded the term correctly: it injected both survey blocks with
the answer duty (`agents/tasks/LJ-1-685/LJ-1.685.md`, `## ARCHIVE` and
`## LITERATURE`), it carried law C-22, and its premise set, the K from
`[LJ-1.678]`, powIter and the bridge as hypotheses, was sufficient. The term
landed. The lint red was not caused by the brief: the report acknowledges the
duty by writing both headings and then never fills them. The return stopped
mid-skeleton, not misdirected.

The brief-side defect was in the FIRST review dispatch's brief, B1: it
commanded "fix THIS, and re-run the pre-commit checks yourself before you
return" (`agents/tasks/LJ-1-685/review-LJ-1-685-1.md:17`, generated at
`scripts/pod/pod.py:2678`), while the same brief's scope line said the reader
writes one file "and nothing else" (`review-LJ-1-685-1.md:7-11`). The check
that failed reads a file outside that scope: `report_of` takes the task's own
report and its docstring says "A review companion is another dispatch's
return and is not judged here" (`scripts/pod/check-survey-quotes.py:427-440`).
An instruction a dispatch cannot execute without breaking a stronger rule is
a defect in the brief. My own dispatch brief carries no such note, and I
report the defect so the template does not fire it again on the next
lint-class escalation.

### 1.4 Is there a cure the return missed? NO, for the mathematics. One cure exists for the return, and it is not the critic's.

I closed four attack lines on the term.

- **The bridge's type.** The report says "This file takes that type"
  (`lj-1.685-report.md:45-46`), citing `Probe684.agda:69-72`. The delivered
  `Bridge` at `Probe685.agda:66-69` is that type's SHAPE at this consumer's
  layout: it is quantified over `S ^ (13 + n)` environments at the shifted
  slots `sh13 w`, `sh13 b`, with the K at slot 12, while `[LJ-1.684]`'s is
  over `S ^ m` at unshifted slots. Neither is literally the other. This is
  not a weakening the return hides: the brief itself fixes the bridge as a
  hypothesis, and the matrix the term must satisfy puts `graphBndAt` at
  exactly the shifted layout, `matrix = transK ∧̇ ( pins ∧̇ G.graphBndAt )`
  at `Probe520.agda:125`, instantiated by `module Mx = Matrix {M} (sh w)
  (sh b) kk ...` at `Probe520.agda:160`. The hypothesis must sit at that
  layout to be usable at all. The defect is one word: "that type" should
  read "that type's shape at the shifted slots". Precision note N1, not a
  verdict changer.
- **The unspent powIter.** The body binds it as `_` and spends nothing of it
  (`Probe685.agda:77`). The probe says so before the definition
  (`Probe685.agda:46-48`: "Taken as a hypothesis. The reverse body does not
  spend it"), and the report claims no use of it. Taking a mandated
  hypothesis and not spending it is not a defect.
- **The unspent KValue.facts.** The K is real and is `[LJ-1.678]`'s:
  `runs/TRANS.agda:31` opens `W678.Block (fst (lookup b γ)) ob`, and
  `kk = LsetS lam ordλ` at `TRANS.agda:36`, which is the bound slot of
  `KValue`'s own fourteen-slot environment, `Kenv = LsetS gam ordγ ∷
  LsetS lam ordλ ∷ ...` (`src/L/Condensation.lagda.md:7390-7391`). The
  `facts` field itself is not consumed. The report never claims it is
  consumed; it says the reverse instantiates the k-value at
  `fst (lookup b γ)` (`lj-1.685-report.md:58-60`), which is what the code
  does.
- **Vacuity.** The conclusion depends on the graph hypothesis and the bridge:
  `hgraph = br T.env (LF.lift13 ... hG)` at `Probe685.agda:86-87` feeds
  `A.from-conj T.htrans P.hpins hgraph` at `:78`. The arm records
  `agda_vacuous: false` (`accept-1.out:32`). The term is not vacuous.

For the RETURN, the missed cure is the fill itself, and the checker's own
message names it: "A written decline is compliance"
(`scripts/pod/check-survey-quotes.py:450-452`; the DECLINE pattern it enforces
is at `:123-126`). Two written declines in the predecessor's report would
have closed the duty. That act belongs to the author slot, not to this one.

## 2. THE THREE QUESTIONS, ANSWERED

These are section 6.6's own list, which lives at
`dev/memos/LJ-4-pod-program-design.md:2984-2988` (see the pointer defect in
section 0).

1. **Does the verdict LINE match its own BODY?** No. The line at
   `lj-1.685-report.md:9-10` says the floor, the packing and the term follow.
   The body delivers all three: the term at `Probe685.agda:71-89`, eight
   green `.agda` runs (`runs/accept-1.out:16-23`), obligations delta -1 with
   0 open (`runs/accept-1.out:27` and `:32`). The two survey placeholders at
   `:90` and `:94` are the same disease: the return was never finished. This
   is the measured class of `[LJ-1.373]` and `[LJ-1.376]`: a verdict line its
   own body contradicts. Here the line understates a complete result. That is
   why the verdict is overturned rather than upheld: I do not agree with the
   stated line, and the true state of the body is a GO at the strength the
   brief set.
2. **Is every load-bearing claim backed by a `file:line` that resolves today?**
   Yes. I opened every citation in the report: `lj-1.672-report.md:9-11`,
   `:174-180`, `:184-185`; `review-of-LJ-1-672-1.md:8`;
   `lj-1.678-report.md:9-10` and `:150-154`; `Probe678.agda:27-32`;
   `Probe684.agda:69-72`; `Probe520.agda:192-195`, `:124-164` and `:124-125`;
   `src/L/Coding/Bound.lagda.md:93-94` and `:147-152`;
   `src/L/Hierarchy.lagda.md:334-335`; `dev/pod/direction.md:37`; the pins
   site `LJ-1-672/runs/W3.agda` (`suc-pin` at `:52`, `empty0` at `:67`); and
   the C-22, D-10 and C-42 lesson homes at `dev/LESSONS.md:2307`, `:1375`,
   `:3762`. All resolve today. Three precision notes, none load-bearing.
   N1: the bridge "takes that type" claim is shape-level, as measured in
   1.4. N2: the report cites the reverse conjunct at `Probe520.agda:194`
   (`lj-1.685-report.md:65-66`); line 194 is the FORWARD conjunct, the
   reverse is `:195`. The range the report's table cites, `:192-195`, is
   correct, so the single-line cite is off by one line inside a correct
   range. N3: "This worktree has no `agents/tasks/LJ-1-681/` directory"
   (`lj-1.685-report.md:42-43`) is true here, and the transition log
   corroborates the sibling reading: seq 4511 sends LJ-1.681 to RUNNING at
   2026-08-26T19:00:38Z, 33 seconds after this task went READY. A fourth,
   smaller note: the report's section 1 cites `[LJ-1.678]`'s GO at
   `lj-1.678-report.md:1` (`lj-1.685-report.md:35-36`); line 1 is that
   file's title, and the GO verdict line is `:9-10`. The fact itself
   resolves.
3. **Is the predecessor's enumeration complete?** Complete at the level that
   decides the verdict. The enumeration of what the reverse needs beyond the
   chosen K is: powIter as a hypothesis, the bridge as a hypothesis, and
   IsOrd in the k-value telescope (`lj-1.685-report.md:70-84`). The delivered
   telescope is exactly that and nothing else:
   `PowIterHyp → IsOrd (fst (lookup b γ)) → Bridge → graph → Σ₁`
   (`Probe685.agda:71-76`). The IsOrd argument is backed: `k-value` is
   stated at a generic ordinal (`Probe678.agda:27`), and `Lset-only`
   consumes IsOrd and does not produce it
   (`src/L/Hierarchy.lagda.md:334-335`). transK and pins come from pieces
   already delivered green, `Bound.trans∈λ`
   (`src/L/Coding/Bound.lagda.md:93-94`, used at `runs/TRANS.agda:47-49`)
   and the `[LJ-1.672]` pin combinators, `W672.empty0` and `W672.suc-pin`,
   spent at `runs/PINS.agda:51-59`. No fourth input exists, and the
   `[LJ-1.672]` NO-GO's condition for reopening, an adequate K
   (`lj-1.672-report.md:174-180`), is what `[LJ-1.678]` delivered
   (`lj-1.678-report.md:9-10`).

## 3. WHY THE LINT RED CANNOT LEAVE A REVIEW DISPATCH, AND WHAT CAN LIFT IT

The escalation named the defect: the survey duty. I re-ran the check myself,
before writing this file.

- **What the gate reads.** At acceptance, conjunct 6 runs
  `check-survey-quotes.py LJ-1.685`, which pairs the work brief
  `LJ-1.685.md` (`brief_of`, `scripts/pod/check-survey-quotes.py:421-425`)
  with the report `lj-1.685-report.md` (`report_of`, `:427-440`). Measured
  today in this checkout: rc 1, ten unanswered paths, five under `archive/`
  and five under `dev/literature/`. A review file is not read by this gate.
  A fully compliant review cannot turn this conjunct green.
- **The proof is now measured, not predicted.** The first review instance
  returned with a compliant review file, both survey blocks filled, and its
  arm still failed conjunct 6 with the same text (`runs/accept-2.out:15`).
  The slot was then redispatched, and this dispatch is that redispatch. A
  third compliant review will do the same.
- **Why I do not edit the report.** My scope is one file, this one. The
  failing file is the return I am attacking. The invariant is explicit: the
  critic is never the author (`dev/pod/instructions/coder_adversarial.md:28`).
  Filling the predecessor's survey sections with my words would put my
  authorship inside the return under review, and the record would then claim
  survey answers its author never gave. I refuse that, and I report the
  conflict instead.
- **What routes after this return.** With `obligations_open: 0`, row
  `sys-critic-upheld-no-go` cannot fire: it demands `obligations_open_min =
  1` (`dev/pod/table.toml:4317-4321`). A lint red routes to
  `sys-lint-accept` (`dev/pod/table.toml:790-800`) whatever this review says,
  and that row re-accepts the task. The precedent is measured and terminal:
  `[LJ-1.512]` parked permanently at `attempt_max:sys-lint-accept` with its
  obligation inhabited at delta -1 (`dev/pod/queue.toml:3774-3777`). Without
  an act outside this slot, LJ-1.685 repeats that park, with a green probe
  and a closed obligation.
- **A second, machine-side risk, also measured.** The arm re-runs every
  `.agda` under the task home as conjunct 1. In accept-2 that conjunct
  failed, because `RENAME3.agda` was killed at 0.47 s, rc -9, no Agda error,
  `heap_wall: false`, under machine load 5.3 to 5.9 with two Agda slots
  (`runs/accept-2.out:8`, `:21`, `:30`). The same file is green in accept-1
  at 1.61 s (`accept-1.out:21`). If the next arm dies the same way, that is
  a load fact about the shared machine, not a fact about any return, and it
  must not be read as one.
- **The repair, one act.** Fill `lj-1.685-report.md`'s `## ARCHIVE USED` and
  `## LITERATURE USED` sections, each path read at a line or declined in
  writing. The gate demands the WORK brief's ten, which differ from this
  review brief's ten: `archive/dev/DD-archived.md`,
  `archive/dev/ORCHESTRATION.md`, `archive/dev/PLAN-archived.md`,
  `archive/dev/STATUS-archived.md`, `archive/dev/TASKS-archived.md`,
  `dev/literature/BIBLIOGRAPHY.md`, `dev/literature/devlin-errata.md`,
  `dev/literature/glossary-review-2026-08.md`,
  `dev/literature/level-formula-slot-roles.md`,
  `dev/literature/primary-sources.md`. The author slot or the maintainer can
  do this in one edit. A review redispatch cannot.

## 4. WHAT THE NEXT BRIEF SHOULD CARRY

1. **Address the fill to the author slot or the maintainer**, never to this
   slot. The cure is one edit in `lj-1.685-report.md`, named in section 3.
2. **No new mathematics.** The obligation is discharged and green. Do not
   re-dispatch the term, and do not re-run the probe. Keep the restructured
   W3 shape: the generic pack in `runs/PACK.agda` plus the thin re-export in
   `runs/W3.agda:10-12`.
3. **Fix the review-brief pointer** for the three questions to
   `dev/memos/LJ-4-pod-program-design.md:2984-2988`. Two reviews have now
   recorded the wrong range.
4. **Fix B1**: the lint note's "fix THIS" at `scripts/pod/pod.py:2678` must
   name a file inside the reader's write scope, or name the maintainer as
   the actor, when the failing check reads the predecessor's return.
5. **Read an rc -9 arm kill as load**, per accept-2, before pricing any
   "failure" it reports.

## 5. THE STANDING DIRECTION

No conflict. The report addresses the direction at `dev/pod/direction.md:37`:
this task is LJ-1 work, it starts no SRC collection, and it starts no phase 3.
That reading is correct, and this review changes nothing in it.

I wrote this file and nothing else. I wrote no `.agda` file and no `runs/`
file. I started no Agda process: the role line for this slot reads "You
attack a return, and you never re-run it" (`scripts/pod/pod.py:1700-1703`),
and the accept arm in this checkout is the measurement. I did not set
`GHCRTS`; the pane carries `-A64m -I0 -M2g`, the wide caliber, set by the
program. I re-ran one conjunct-6 member myself, `check-survey-quotes.py
LJ-1.685`, and it returned rc 1 with the ten unanswered paths named in
section 3. I measured the `postulate` search over the task home myself. No
commit, no push.

## ARCHIVE USED

- **`archive/dev/DD-archived.md` READ.** `archive/dev/DD-archived.md:35` reads
  "The questions are: is the refusal correct on its own numbers; is the
  measurement sound; did the BRIEF cause the outcome; and is there a cure the
  return missed." This is the four-question lens of section 1. It is DD25's
  own list and I used no other.
- **`archive/dev/ORCHESTRATION.md` DECLINED.** Not read. The dispatch rules of
  the retired route do not decide a verdict-line or survey defect; the live
  process facts are in `scripts/pod/`.
- **`archive/dev/PLAN-archived.md` DECLINED.** Not read. The live status is
  `dev/pod/screen.toml`, and no planning history bears on this verdict.
- **`archive/dev/measurements/README.md` DECLINED.** Not read. This review
  audits the return's own runs and the acceptance arm, and it commissions no
  new measurement protocol.
- **`archive/dev/README.md` DECLINED.** Not read. A guide to the retired
  archive; no retrieval was needed beyond the one file used above.

## LITERATURE USED

- **`dev/literature/BIBLIOGRAPHY.md` DECLINED.** Not read. No source was added
  and none was missing.
- **`dev/literature/devlin-errata.md` DECLINED.** Not read. This review quotes
  no scanned certificate and certifies no Devlin leaf.
- **`dev/literature/primary-sources.md` DECLINED.** Not read. The bridge stays
  a hypothesis, so no primary text decides anything in this verdict.
- **`dev/literature/level-formula-slot-roles.md` DECLINED.** Not read. The
  term's strength is fixed by the brief's own hypothesis list, not by the
  bound's role in Devlin's text.
- **`dev/literature/glossary-review-2026-08.md` DECLINED.** Not read. No
  naming question arose and this review proposes no `dev/glossary.toml`
  entry.
