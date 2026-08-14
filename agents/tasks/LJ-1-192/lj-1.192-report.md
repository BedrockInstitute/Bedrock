# LJ-1.192 report: P2, the artifact-over-proxy SKILL

tier: pi (deepseek-subagent-mode), model deepseek-v4-flash. Build dispatch.
The model is a command-line flag and this line only records the choice.

## 0. LEAD

The skill is at `.claude/skills/artifact-over-proxy/SKILL.md`. Its
`description:` line, quoted whole:

> The artifact is the evidence; the status field is a hint. Load when about
> to record, report or act on an outcome that came from a proxy: a status
> table, a verdict cell, an index row, a STATUS: header, a summary line,
> a machine-load figure, a note, or a tool's exit message, rather than from
> the file the claim is about. The cheap test: name the artifact you opened.
> If you cannot name one, you read a proxy. Triggers: status, DIED, RUNNING,
> FAILED, CLEAN, success, queued, never ran, done, finished, recorded,
> reported, outcome, result, verdict, cell, row, header, note, summary, the
> table says, the row says, the cell says, the note says, exit message,
> quiet, no agent running, machine load, measured load, count as price.

The build stopped at BUILT. The abort criteria were fixed before the run
(D-1) and each is answered in section 1.

## 1. The abort criteria, answered

1. **BUILT.** The skill exists. The description is quoted in section 0. The
   rules with their evidence are in section 2. No Agda ran, no agent was
   dispatched, no commit was made. STOP.
2. **The shape is narrower than the proposal claims? NO.** The shape is a
   class, MEASURED. The three episodes the brief names (DIED, RUNNING,
   verdict cell) plus the three the proposal adds (header, quiet, no-op) are
   six distinct instances at six distinct commits. The proxies differ: a
   status table, a brief header, an index row, a verdict cell, an exit
   message, a load claim. The tools differ: `dispatch.py` status, the plan
   status screen, the task index, a CLI. One disease, six costumes: an
   outcome recorded without a named artifact opened. A skill for one
   situation is worth less than an honest refusal. This is not one
   situation.
3. **A rule cannot be written as a trigger? NO.** All six rules trigger at
   their write moment, because each error is the write. The skill has no
   reading rule. The reading half is attention, and the skill says so in
   its boundary paragraph.

## 2. The rules, with their evidence

Each rule is taken from `agents/tasks/LJ-1-189/lj-1.189-report.md:190-234`
(proposal section 5), whole. Every commit hash is kept. Each episode was
verified by reading its commit body whole with `git log -1 --format=%B`.

| rule | episode | evidence |
|---|---|---|
| the artifact is the evidence; the status field is a hint | [LJ-1.187] recorded as DIED because the status table said so; the report was on disk; the third time in one session | `2b95717`, whose body names the first two: `RUNNING` as proof a launch worked, and a grep of status output |
| a header is not a report | [L3.32-T261]'s probe ran; the plan said it never ran, for four days | `4a12cac`; the provenance is commit `808c1c5`, which read T261's brief header |
| "quiet" means measured load, never an absence of siblings | no agent was running; the machine was not quiet | `21446f2`, whose body measured the load |
| a verdict cell is not the report, and a count is not a price | [LJ-1.175] read [LJ-1.156]'s count as its price | `0e004c7` |
| a row is not the row below it | [LJ-1.177] read [LJ-1.155]'s row and not [LJ-1.158]'s, which sat directly below it | `0cb9b17` |
| a no-op that prints success is not success | `check-probes.py --archive` no-op'd and printed "check-probes: clean" | `bd64fba` |

## 3. Would this skill have loaded at the moment of each error?

INFERRED. The load itself is not observable until the skill exists, because
the skill is the trigger. The answer is yes at every one of the six moments,
because each error is the recording moment, and the trigger word is in the
model's own text at that moment:

- at `2b95717` the model wrote "DIED" and "the status table said so"
- at the `RUNNING` episode it wrote "RUNNING" and "success"
- at `4a12cac` it wrote "queued" and "never ran"
- at `0e004c7` it wrote "verdict cell" and "count"
- at `21446f2` it wrote "quiet" and "no agent running"
- at `bd64fba` it wrote "clean"

The boundary is the same one `[LJ-1.189]` section 8 names
(`agents/tasks/LJ-1-189/lj-1.189-report.md:279-298`): the skill fires at the
write moment, and it cannot fire when the model reads a proxy and records
nothing. That residue is attention, not a skill moment. The skill promises
no cure for it.

## 4. Classification, in the brief's words

MEASURED: the six episodes, each verified at its commit by reading the
commit body whole. MEASURED: the shape is a class, by six distinct
instances at six distinct commits. INFERRED: the skill would have loaded at
the moment of each error; the load is not observable until the skill
exists. UNMEASURED: nothing in this deliverable claims a machine behavior
nobody has observed, and no such claim was needed.

## 5. The searches I ran

The brief's trap is a search that excludes what it looks for. I swept by
shape, never by one spelling, and I name every search:

- `git log -1 --format="%h %s" <hash>` for each of the six episode hashes:
  existence only. One pass per episode, never a spelling grep.
- `git log -1 --format=%B <hash>` for each of the six: the episode bodies,
  read whole.
- `grep -n "LJ-1.187" dev/JOURNAL.md`: to find the journal entry that
  records the habit.
- `grep -n "C-32|C-39|C-40|C-41|C-42|C-43" dev/LESSONS.md`: to find the
  law rows the brief mandates, then each row read whole.
- `grep -n "## 5. P2|## 4. P1|## 6. P3|## 8. Errors" agents/tasks/LJ-1-189/lj-1.189-report.md`:
  line numbers for citations.

I did not grep the commit corpus for "status" or "DIED". The episodes came
from the proposal whole, and each was then verified at its commit. A
spelling grep would have been the trap.

## ARCHIVE USED (DD18)

- `agents/tasks/LJ-1-189/lj-1.189-report.md`, read whole. Took section 5
  (lines 190-234): the six rules, the trigger list, the sharp question, and
  the honest note that this is the most attention-adjacent of the four
  proposals. Took section 8 (lines 279-298): the no-cure list, so the skill
  promises no cure for attention. Took section 9 (lines 302-330): the sweep
  method. Took section 10 (lines 341-348): DD4.
- `.claude/skills/dispatch-herdr/SKILL.md`, read whole. Took the skill
  shape: the description as the trigger mechanism (lines 1-5), the
  MEASURED/INFERRED/UNMEASURED convention (lines 15-18), and the dispatch
  half of the rule at mistake 2 (lines 294-297), which this skill
  generalizes. Its own mistake 2 is one of the three episodes this skill
  generalizes, as the brief says.
- `.claude/skills/asd-ste100/SKILL.md`, read whole. Took the description
  shape (frontmatter, lines 1-8): the description says what the skill DOES,
  then lists trigger phrases.
- `dev/LESSONS.md` C-32 (line 2965), C-39 (line 3539), C-40 (line 3620),
  C-41 (line 3657), C-42 (line 3704), C-43 (line 3758), each read whole.
  C-32: a law that did not reach the moment of action is the argument this
  whole batch rests on. C-42: the sweep law, whose converse the row rule
  cites in its own commit body. C-39, C-40, C-41, C-43: the process laws
  the skill must not restate.
- `dev/JOURNAL.md` lines 654-685, the [LJ-1.187] entry: the habit record
  and the "third time" line.
- `git log -1 --format=%B` for the six episode hashes, plus `808c1c5`:
  the primary evidence corpus, cited in section 2.

## LITERATURE (DD18)

Not this task's subject. Nothing in `dev/literature/` bears on whether a
skill can carry an outcome-recording rule to the moment of writing; DD18 is
satisfied by this one honest line.
