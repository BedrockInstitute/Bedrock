# The standing DIRECTION

**The repository owner writes this file and nobody else does.** The program `cat`s it
into every dispatch, ahead of the brief and behind the slot file, for all five slots.
So an edit here reaches every worker started after it, without anyone remembering to
pass it on.

**IT CARRIES GUIDANCE AND NEVER A RULE.** Rules live in `AGENTS.md` and in
`dev/pod/instructions/<slot>.md`, and both are guarded. This file is deliberately
unguarded: a direction that costs an approval round to write is a direction that does
not get written.

**ONE CURRENT DIRECTION, AND THE PROGRAM FILES THE OLD ONE.** When the owner rewrites
this file the program archives the outgoing body to `archive/dev/direction/<stamp>.md`
on the next tick, so this file never grows into a history that every dispatch pays to
read. Nothing is deleted.

**A CHANGE HERE RE-PLANS THE QUEUE AT ONCE.** Rule (g) normally waits for the queue to
run dry. A new direction fires it on the next tick instead, so a correction takes effect
in seconds rather than whenever the queue happens to empty.

**WHAT THE MATHEMATICIAN DOES WITH THE TASKS ALREADY QUEUED IS ITS OWN CALL.** The
program deletes no entry of `dev/pod/queue.toml` on a direction change. AD3 gives every
mathematical judgement to the mathematician, so the refill reads this file, decides which
queued entries the new direction has made wrong, and says why in its return.

**TO REACH A TASK THAT IS ALREADY RUNNING**, this file is not the way: that worker was
started with the old text. Attach to it and say so.

```sh
herdr agent list
herdr agent prompt lj-1-386 "..."     # it queues and is read at the next tool call
```

## Current direction

**NONE. The owner has written no direction yet.** Work to `dev/PLAN.md` section 0 and to
your brief.
