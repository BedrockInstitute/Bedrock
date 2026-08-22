# CLAUDE.md

Claude Code reads this file, not `AGENTS.md`. Bedrock's one rule set lives in `AGENTS.md`
and the import below loads it here, so both read one source.

**If you are a dispatched worker, your slot's own clauses are in
`dev/pod/instructions/<slot>.md`. The program `cat`s FIVE files in this order: that
file, `AGENTS.md`, `dev/pod/screen.toml`, `dev/pod/direction.md`, then your brief
(`preamble_for()`, `scripts/pod/pod.py:236`). `AGENTS.md` holds only what every slot
shares. A RESIDENT slot gets that preamble once, at session start, and every later
prompt is the brief alone, so open the screen and the direction yourself.**

@AGENTS.md
