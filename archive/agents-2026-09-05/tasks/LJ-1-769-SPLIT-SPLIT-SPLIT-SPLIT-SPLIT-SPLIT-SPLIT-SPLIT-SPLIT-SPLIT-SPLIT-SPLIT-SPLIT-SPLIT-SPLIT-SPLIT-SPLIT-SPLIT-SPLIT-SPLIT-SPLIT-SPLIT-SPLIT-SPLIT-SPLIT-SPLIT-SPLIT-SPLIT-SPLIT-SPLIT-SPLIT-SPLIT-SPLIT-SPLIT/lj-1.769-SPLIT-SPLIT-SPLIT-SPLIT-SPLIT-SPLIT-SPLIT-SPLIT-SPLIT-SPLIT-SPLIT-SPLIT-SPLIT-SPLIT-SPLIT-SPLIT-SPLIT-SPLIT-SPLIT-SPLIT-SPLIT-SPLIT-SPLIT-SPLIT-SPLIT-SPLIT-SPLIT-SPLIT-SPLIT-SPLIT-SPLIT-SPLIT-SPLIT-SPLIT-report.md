# LJ-1.769-SPLITx34 report: push-raw-at-vars, gate stop, instruments delivered

## HEAD

head_slot: coder
machine: shared
agda_tier: heavy
task: LJ-1.769-SPLITx34 (34 SPLIT tokens; full paths in section 2)
obligation: agents/tasks/[this task's 34-token directory]/Probe769S34.agda::push-raw-at-vars
verdict: **STOP AT THE BRIEF'S GATE. NO AGDA RAN, NOTHING IS MEASURED,
AND NO VERDICT ABOUT THE TERM IS CLAIMED.** Swap used was 30228.75 MB
at the dispatch's first command against the brief's 8192 MB line, and
every later reading stayed above the line (section 1), so the gate
forbade every Agda run, canary included. The transcription duty
survived the gate, as the brief orders it and as the whole line's
returns have practised it: the obligation and its frame are
TRANSCRIBED into this task's own namespace at `.agda.txt`,
receipt-checked and diff-verified against the sources the brief
named, beside the retargeted run harnesses. The obligation stays open
at supply 0 (the brief's own MEASURED TODAY: `push-raw-at-vars => 0`).
This row is ENVIRONMENT and claims neither `heap_wall` nor a
mathematical NO-GO. The branch this return fits is `transfer-park`.

## 1. The gate

One command: `sysctl vm.swapusage`.

- Reading 1, the dispatch's first command, before any read and any
  transcription: `used = 30228.75M` (total 31744.00M, free 1515.25M).
- Reading 2, after the source and predecessor reads, before the
  report skeleton: `used = 30172.75M` (total 31744.00M, free 1571.25M).
- Reading 3, after the skeleton was written, before the instruments:
  `used = 30164.75M` (total 31744.00M, free 1579.25M).
- Reading 4, after the diff receipts, before this report was filled:
  `used = 30156.75M` (total 31744.00M, free 1587.25M).
- Reading 5, the dispatch's last command before this return:
  recorded in section 7.

Every reading is far above the 8192 MB line, so the brief's gate
clause ordered the stop at the first command and the stop stands at
every later reading. `pgrep -l agda` returned nothing at the start,
nothing at reading 2, and nothing at reading 4: no Agda of this
dispatch exists, and none was started. The pane caliber was read
first-hand (`GHCRTS=[-A64m -I0 -M4g]`, the heavy tier) and no number
is claimed under it, because no process ran.

For scale: the two predecessors' first readings are 32781.06 MB
(32-token task) and 30348.75 MB (33-token task). This dispatch's
first reading is 120.00 MB below the 33-token one, and the distance
remaining to the 8192 MB line is 22036.75 MB. No drain rate is
claimed from these points.

## 2. The transcription and its receipts

Both source reads the brief names resolved in the MAIN CHECKOUT at
the paths as written, in the 32-token directory:
`agents/tasks/LJ-1-769-SPLIT-...-SPLIT/Probe769S32.agda.txt`
(107 lines, full token run on disk) and its
`runs/Frame769S32.agda.txt` (162 lines).

- `Probe769S34.agda.txt`, 110 lines. The comment header above the
  first `open import` line is rewritten for this task. The provenance
  chain's outermost reference is UNCHANGED from the predecessor's:
  both briefs name the same source, the 32-token task's parked
  obligation `Probe769S32`. The inner chain is copied VERBATIM, and
  the gate note carries this dispatch's own reading. Receipt: diff
  from the first `open import` line down shows EXACTLY TWO DIFFERING
  LINES (`5c5`, `21c21`): the module line (this task's top level, 34
  tokens, `Probe769S34`) and the Frame import line (this task's
  vendored frame `runs/Frame769S34.agda.txt`). The term's name is
  already the brief's `push-raw-at-vars` in the source, so no name
  line differs. The obligation's body is otherwise byte-identical to
  the source's.
- `runs/Frame769S34.agda.txt`, 164 lines, source body size kept. From
  the OPTIONS line down there is EXACTLY ONE DIFFERING LINE (`28c28`):
  the module line (34 tokens, `runs.Frame769S34`). The new top header
  is rewritten for this task (outermost chain entry = the source this
  dispatch read, gate reading of this dispatch); the source's own
  older provenance headers (its `[LJ-1.767-SPLIT]` and inherited
  ones) are preserved verbatim after the OPTIONS line, so the diff
  discipline stays checkable at any later date.
- `runs/run.sh` (12 lines) and `runs/run-obligation.sh` (14 lines),
  retargeted from the predecessor's committed harnesses: 33 -> 34
  tokens in every path, `S33` -> `S34` in every stem, `probe769s33-1`
  -> `probe769s34-1`. Receipts: diff against the 33-token harnesses
  shows nothing but retarget lines (2 source lines in `run.sh`: the
  usage comment and the out path; 6 source lines in
  `run-obligation.sh`: the comment stem, ROOT, cp, run, grep, rm).
  Post-check: no `S33` string remains in either harness, and the ROOT
  line mechanically counts 34 SPLIT tokens. One Agda process, caliber
  from the pane, never set in any file, 1800 s cap, gate re-checked
  by the harness itself before anything runs. The harness comment
  carries the 8192 MB line the brief's gate clause orders.

Construction discipline: no path in this dispatch was hand-typed.
Every SPLIT run was produced by a variable or a loop, and every
string replacement was ASSERTED to occur exactly the expected number
of times before any file was written. On the first construction
attempt one assertion fired (the report stem, see 2.1) and nothing
was written in that attempt.

Naming rule: this task's directory holds NO `.agda` file. A name is
earned by an EXIT=0 run, and nothing ran.

### 2.1 Two defects found and closed inside this dispatch

- **Premise 1's citation does not carry its figure to a readable
  home.** The brief's premise 1 records "GATE STOP 32. Swap 32781.06
  MB" and gives as basis THIS task's report at line 11, a file that
  did not exist at dispatch time. The figure's true home is the
  32-token task's report, measured at its line 11: "AND NO VERDICT
  ABOUT THE TERM IS CLAIMED.** Swap used was 32781.06 MB". The stop
  is unaffected: this dispatch's own readings are section 1. The next
  brief should cite the 32-token report, or the brief clause itself,
  for the 8192-gate figure chain.
- **The predecessor's parked instruments carry a one-short report
  stem.** The 33-token task's `Probe769S33.agda.txt` and
  `runs/Frame769S33.agda.txt` name, in their UNVERIFIED notes, a
  report stem with 32 SPLIT tokens (their source's report) where the
  task's own report has 33. Not this dispatch's files to fix; this
  dispatch's instruments name this task's own 34-token report stem.
  Recorded so the next reader does not read the predecessor's note
  as this line's convention.

## 3. What was not written, and why

- `Probe769S34.agda`: not written. The stem is not earned until an
  EXIT=0 run promotes it.
- `review-of-push-raw-at-vars.md`: not written. This row is
  ENVIRONMENT; a gate stop claims no mathematical NO-GO, and the
  line's earlier returns held the same line on the same scope entry.
- anything under `runs/*.out`: no Agda ran.
- anything under `src/`: nothing.

The deliverables of this dispatch are UNTRACKED in THIS worktree.
Their absolute home until the program commits them is this task's
directory here. The next worktree reaches them only after the
program commits, which is why this dispatch's own reads resolved
cross-checkout.

## 4. The runs

None. The gate ordered the stop before any Agda, and the reading was
far above the line at all in-dispatch readings. The run order is
staged and unchanged for the next dispatch that holds a green gate:
canary first, on a same-stem `.agda` copy of
`runs/Frame769S34.agda.txt` through `runs/run.sh`; then, green there,
the obligation through `runs/run-obligation.sh`, which re-checks the
gate itself, re-copies the probe to its `.agda` stem, runs it under
the 1800 s cap, promotes the name on `EXIT=0`, and deletes the copy
on every other exit.

The line's only measured Agda price re-read by the predecessor at
`agents/tasks/LJ-1-769-SPLIT/runs/frame769split.out` stands:
`15.77 real`, `1743634432  maximum resident set size`, `EXIT=0`.
That is the FRAME canary of the 1-SPLIT task, not this obligation,
and the number the next dispatch reports is the number its own run
measures.

Ratio bar note: the write scope holds raw `.agda.txt` probes and
shell harnesses, no `.lagda.md` master under `src/`, so the in-fence
line count of this task is 0 and the 0.0123 s per line bar has
nothing to divide.

## 5. W3, the widest unmeasured term

Whether `push-raw-at-vars` checks at `-M4g` when swap used is below
8192 MB. Still unmeasured; this dispatch adds no number, because no
Agda ran. The invariant that bears on W3 STANDS: the obligation has
never typechecked through the promotion protocol in ANY split form;
this task's directory, like every predecessor's, holds only
`.agda.txt` instruments, while the frame instrument has earned its
name on this line. The supply figure is unchanged at 0.

## 6. What the next brief needs

- The gate is the binding constraint. First readings across the last
  three dispatches: 32781.06 (32 tokens), 30348.75 (33), 30228.75
  (34). The distance to the 8192 MB line is 22036.75 MB. No rate is
  claimed from these points.
- The swap's holders are outside this repository's reach, so no
  in-tree action can close this stop: it ends when the machine frees
  swap (reboot or holder exit), and the evidence is section 1.
- Each further park_and_split on this row re-pays the full dispatch
  price (brief build, worktree admission, cross-checkout reads,
  transcription with receipts, report, acceptance) for a gate reading
  still above the line. That is the queue's call, not this slot's;
  the measurement behind it is section 1.
- Premise 1's basis citation should be fixed (see 2.1): cite the
  32-token report for the 32781.06 figure, or the brief clause.
- The brief's named source has now been the SAME file for two
  consecutive dispatches (33 and 34 both transcribe the 32-token
  task's instruments). If the queue means to advance the chain, the
  next brief should name the then-current parked instruments; if it
  means to keep the 32-token source, the receipts above stay exactly
  two lines and one line and the chain is stable.

## 7. Close readings

- Reading 5, after this report was filled and before the survey
  check: `used = 30140.75M` (total 31744.00M, free 1603.25M). Five
  readings: 30228.75, 30172.75, 30164.75, 30156.75, 30140.75. The
  drift is down and small across the dispatch; no drain rate worth
  naming comes from readings that never approach the line.
- `pgrep -l agda` at the close: nothing.
- Working tree: this task's directory holds `Probe769S34.agda.txt`,
  `runs/Frame769S34.agda.txt`, `runs/run.sh`,
  `runs/run-obligation.sh`, and this report, all untracked. Nothing
  committed, nothing pushed, `src/` untouched.

## ARCHIVE USED

All five injected archive candidates are declined, and the decline is
the honest answer: this row is a mechanical gate stop plus a
transcription with diff receipts. It needs no history. Nothing in
these files bears on swap usage, on a namespace retarget, or on
diff-verified transcription receipts.

- archive/dev/ORCHESTRATION.md: declined, not read; an orchestration
  history has nothing in it that bears on a swap gate stop or on a
  retarget receipt.
- archive/dev/DD-archived.md: declined, not read; retired design
  decisions bear on no measurement this dispatch took, and the gate
  this dispatch enforced is the live brief's own clause.
- archive/dev/PLAN-archived.md: declined, not read; a retired plan
  cannot change a gate figure read five times above the line.
- archive/dev/TASKS-archived.md: declined, not read; this dispatch's
  task definition lives in the brief, not in a retired task list.
- archive/dev/STATUS-archived.md: declined, not read; standing status
  is the screen, and a retired status file has nothing in it for
  this row.

## LITERATURE USED

All five injected literature candidates are declined, and the decline
is the honest answer: this dispatch ran no Agda, proved nothing, and
wrote no mathematical prose, so no literature bears on it.

- dev/literature/BIBLIOGRAPHY.md: declined, not read; no source was
  consulted and none is claimed.
- dev/literature/devlin-errata.md: declined, not read; no Devlin
  material was used, because no mathematics was done.
- dev/literature/primary-sources.md: declined, not read; the gate
  stopped the mathematics before any primary source could bear on
  anything measured here.
- dev/literature/glossary-review-2026-08.md: declined, not read; no
  term in this report was chosen against a glossary review.
- dev/literature/level-formula-slot-roles.md: declined, not read; no
  level formula appears in this dispatch's write scope.
