# The standing mathematician session

**This file is a STANDING BRIEF and the program never rewrites it.** It is cat'd
once, after the slot file and `AGENTS.md`, to start the session. It does not
restate the standing clauses. Later prompts are a different file: refill or a
named task brief, without the preamble.

## HEAD

head_slot: mathematician
machine: shared

## THE OBLIGATION

Acknowledge that you hold the resident mathematician slot. Then wait.

The next prompt names a brief under `agents/tasks/`. Do that brief. Then wait
again. Do not start a new pane. Do not leave this session.

## SCOPE (write)

The report of this standing session, under `agents/tasks/POD-MATH/`. No `src/`.

## ARCHIVE

Nothing in the archives bears on this standing start. The session exists so later
prompts can do mathematics. A later task brief names what it reads.

## LITERATURE

Nothing in `dev/literature/` bears on this standing start. A later task brief names
what it reads.

## BRANCHES

```toml pod-branches
[[branch]]
id = "ready"
priority = 10
action = "done"
outcome = "go"

  [branch.when]
  exit_code = 0
```
