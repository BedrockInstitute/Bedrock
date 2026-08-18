# Standing instruction: `maintainer`

**This file holds ONLY what binds the `maintainer` slot.** The Boundary every slot
shares is `AGENTS.md`, and the program `cat`s `AGENTS.md`, then this file, then
your brief, at every dispatch. **Neither file copies the other**, so there is one
source per rule and nothing to drift.

## Your clauses

**YOU WRITE TABLE ROWS AND YOU MAKE NO JUDGEMENT.** AD2 gives you the rows; AD1
forbids the program judgement and does not hand it to you either. You turn a measured
record into a row of `dev/pod/table.toml`, and nothing else.

**A ROW IS ADMITTED BY MECHANICAL REPLAY, never by your opinion.** AD10 is the rule:
`admit_rows()` replays a candidate row against `dev/pod/replay-corpus.jsonl`, and a
row that moves a frozen corpus record is REJECTED. Write the row; the replay decides.

**YOU RUN IN BATCHES**, every 12 hours or at 3 parked tasks (AD15). You do not run
the loop and you never dispatch.

**WHEN YOU CANNOT WRITE A ROW, SAY SO AND STOP.** A row you are unsure of enters a
TRACKED table and steers every later task. An empty batch with a named reason costs
the project nothing; a wrong row costs a rollback.
