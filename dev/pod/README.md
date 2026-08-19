# Running the POD

**This is the ONE home for how the loop is operated.** Its audience is the repository
owner and the `maintainer` slot. A developer document, English only.

**IT IS NOT IN `AGENTS.md`, and that is the point.** Owner's ruling, 2026-08-19.
`AGENTS.md` is `cat`ed ahead of every brief for all five slots, so anything written
there is read by a mathematician who only needs to do mathematics and by a coder who
only needs to write Agda. **A worker does not operate the loop and must not be told how
to.** The Boundary stayed in `AGENTS.md`; this left it.

The design behind all of it is `dev/memos/LJ-4-pod-program-design.md`, which this file
never restates.

## How the loop is started, and it is a plain terminal

```sh
sh scripts/pod/keeper.sh                          # the keeper, which owns the loop
.venv/bin/python scripts/pod/pod.py tick --plan   # one pass, launching nothing
```

**START THE KEEPER, NOT THE LOOP.** `keeper.sh` runs `pod.py` as a direct child in the
same pane, so this pane's scrollback is the loop's own output. When the loop crashes the
keeper restarts it in place, with a backoff; after three fast failures it stops guessing
and asks the maintainer, then waits for `.pod-state/keeper-retry`.

**IT RESTARTS A CRASH AND NEVER A DECISION.** `pod run` exits 3 on rule (d)'s STOP and 4
on a startup refusal, and neither is restarted. Read the reason before you restart
anything: a stop is a decision with an author.

| exit | what it means | what to do |
|---|---|---|
| 0 | a signal arrived. Every running worker is untouched | start the keeper again |
| 1 | a crash | the keeper restarts it. Read the pane |
| 3 | STOPPED, a decision | read the newest `STOPPED` line in `dev/pod/transitions/`, then `pod.py resume` |
| 4 | it refused to start and never ticked | read the pane. The reason is printed |

## The hot restart

**`.pod-state/reload` reloads the loop between two ticks.** `cmd_run()` re-execs itself,
and it also reloads on its own when a `scripts/pod/*.py` change has settled for one full
tick. `os.execv` keeps the pid, so the keeper sees no death and every running worker is
untouched. A source that does not compile is REFUSED and the old image keeps running.

**A HOT RESTART IS NOT A RESUME.** A reload cures stale CODE. It does not clear
`.pod-state/STOPPED`.

## `pod.py` is a program and not an agent

Do not start it from inside a coding-agent session in the hope that the session's own
model or effort applies: it does not, and the session would only be a shell. **The
program launches all five heads itself**, each with the model and effort of its row in
`dev/pod/heads.toml`.

## The panes open and close themselves

A dispatch splits a pane in the keeper's own workspace and starts the head inside it, so
a running head is already in front of you. A clean finish closes that pane; every other
ending keeps it, because a dead agent's terminal is the only record of how it died.
**Nothing ever takes your focus**: the program splits and starts, and never calls
`pane focus`.

**THE ONE PANE THAT NEVER CLOSES IS THE MAINTAINER'S**, because it is resident. That is
what makes it reachable at any hour.

```sh
herdr agent list                     # every live head and its pane
herdr agent prompt pod-batch "..."   # send one message without leaving your pane
herdr agent attach pod-batch         # only from ANOTHER workspace; in the pod's own
                                     # workspace the pane is already on your screen
```

**A FINISHED AGENT IS NOT A DEAD ONE.** MEASURED 2026-08-18: after its turn a head
reports `agent_status: done`, and a second `herdr agent prompt` is accepted and answered
on the same session. Only `herdr pane close` ends an agent.

**A PROMPT TO A BUSY HEAD QUEUES AND NEVER INTERRUPTS** (`dev/LESSONS.md` C-61): it is
read when the head finishes its current tool call, and once cost 4.25 hours. To reach a
busy head, end what is keeping it busy first.
