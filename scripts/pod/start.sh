#!/bin/sh
# start.sh: bring the whole pod up with one command. The counterpart of `pod.py stop`.
#
# **WHY IT EXISTS.** Starting the pod was four commands typed by hand, and two of them had
# to be right about a pane id the operator had to look up first. The measured cost of that
# on 2026-08-19 was a maintainer handover in which the FIRST step, freeing the resident
# agent's name, is silent when it is skipped: `maintainer_alive()` answers TRUE while any
# agent holds `pod-batch`, so `ensure_maintainer()` never starts the new head and every
# batch reaches the old one. A script can check that; a person reading a list cannot be
# relied on to.
#
# **IT RUNS THE KEEPER IN A PANE AND NEVER AS ITS OWN CHILD.** `pod run` is an infinite
# loop, so a keeper started as this script's child dies when the shell that ran it goes
# away, and its output lands nowhere the owner reads. `herdr pane run` makes the pane the
# parent, which is the same reason `wait-and-start.sh` ends in `exec`.
#
# Usage:  sh scripts/pod/start.sh [--no-resume]
set -u

ROOT=$(cd "$(dirname "$0")/../.." && pwd)
cd "$ROOT" || exit 1
PY=${POD_PY:-"$ROOT/.venv/bin/python"}
NAME=pod-batch
RESUME=1
[ "${1:-}" = "--no-resume" ] && RESUME=0

die() { printf 'pod start: REFUSED. %s\n' "$1" >&2; exit 1; }

command -v herdr >/dev/null 2>&1 || die "herdr is not on PATH, so no pane can be opened."
[ -x "$PY" ] || die "$PY is missing. Run \`make venv\`."

# 1. THE RESIDENT NAME MUST BE FREE, and this is the check a person forgets.
#
# **AN UNREADABLE LIST REFUSES AND NEVER CLEARS.** MEASURED 2026-08-19 by an adversarial
# review of this file: the first version swallowed every failure with `sys.exit(0)` and no
# output, so empty stdin from a down server, and a warning line before the JSON, both read
# as「the name is free」. One of them had `pod-batch` in the payload. FM12 is the rule this
# breaks and the tree already states it: a blind sensor never admits. It now prints
# `UNREADABLE` and the caller stops.
# **THE CALL IS BOUNDED, and a hung server used to block this script for ever.** There is
# no `timeout(1)` on this machine, MEASURED at `scripts/pod/facts.py`'s own note about
# gap M2, so the bound is python's, which is where the parse already happens.
holder=$("$PY" -c '
import subprocess, sys
try:
    d = subprocess.run(["herdr", "agent", "list"], capture_output=True, text=True,
                       timeout=20)
except Exception:
    print("UNREADABLE herdr-agent-list-timed-out-or-could-not-start"); sys.exit(0)
sys.stdout.write(d.stdout)
' | "$PY" -c '
import sys, json
raw = sys.stdin.read()
try:
    rows = json.loads(raw)["result"].get("agents")
except Exception:
    print("UNREADABLE herdr-agent-list-did-not-parse"); sys.exit(0)
if rows is None:
    print("UNREADABLE herdr-returned-no-agent-list"); sys.exit(0)
for a in rows:
    if a.get("name") == "pod-batch":
        print(a.get("agent"), a.get("pane_id")); break
')
case "$holder" in
  UNREADABLE*) die "the name check could not run: ${holder#UNREADABLE }.
  \`herdr agent list\` gave nothing this script could read, so it cannot tell whether the
  resident name $NAME is free. Starting anyway would risk a second maintainer beside a
  live one. Check the herdr server, then run this again." ;;
esac
if [ -n "$holder" ]; then
    die "the name $NAME is held by [$holder].
  \`maintainer_alive()\` answers TRUE while ANY agent holds it, whatever kind, so
  \`ensure_maintainer()\` would never start the head in dev/pod/heads.toml and every
  batch, close notification and keeper alarm would reach that agent instead.
  Retire it first, then run this again."
fi

# 2. THE LOOP IS STOPPED UNTIL SOMEBODY CLEARS IT. `resume` is the owner's call, which is
#    why `--no-resume` exists: it starts the keeper against a STOPPED loop, which exits 3
#    at once and is only ever what you want when you mean to inspect and not to run.
if [ "$RESUME" = 1 ]; then
    printf 'pod start: resuming.\n'
    "$PY" scripts/pod/pod.py resume
    rc=$?
    # **EXIT 3 IS A DECISION AND NEVER A FAILURE**, and treating it as one refused to
    # start the pod on 2026-08-19 when the loop resumed, ticked once and stopped again on
    # its own parked count. That is the loop working. The keeper must still come up: it
    # is what prompts the maintainer, and the maintainer is the role that clears a park.
    # `keeper.sh` reads exit 3 correctly and does not restart it.
    case $rc in
        0|3) ;;
        4)  die "the loop REFUSED to start (exit 4). It never ticked. Read the message
  above, repair it, then run this again." ;;
        *)  die "resume exited $rc, which is a crash and not a decision. Nothing was
  started." ;;
    esac
    [ "$rc" = 3 ] && printf 'pod start: the loop resumed and then STOPPED on its own
  count. That is rule (d), not a failure. The keeper still comes up, because it is what
  prompts the maintainer, and the maintainer is the role that clears a park.\n'
else
    printf 'pod start: --no-resume, so .pod-state/STOPPED is left in place.\n'
fi

# 3. A PANE OF ITS OWN, in the pod's workspace when one is recorded.
WS=$(cat "$ROOT/.pod-state/herdr-workspace" 2>/dev/null || true)
BASE=$(herdr pane list 2>/dev/null | "$PY" -c '
import sys, json
ws = sys.argv[1] if len(sys.argv) > 1 else ""
try: panes = json.load(sys.stdin)["result"]["panes"]
except Exception: sys.exit(0)
here = [p for p in panes if not ws or p["workspace_id"] == ws]
# A pane with no agent is preferred; any pane in the workspace will do, because the
# split makes a NEW pane either way and never disturbs what is in the one it splits.
free = [p for p in here if not p.get("agent")]
pick = (free or here or panes)
print(pick[0]["pane_id"] if pick else "")
' "$WS")
[ -n "$BASE" ] || die "no pane to split. Open a terminal in herdr first."

PANE=$(herdr pane split "$BASE" --direction down 2>/dev/null | "$PY" -c '
import sys, json
try: print(json.load(sys.stdin)["result"]["pane"]["pane_id"])
except Exception: pass
')
[ -n "$PANE" ] || die "the pane split failed, so the keeper has nowhere to run."

printf 'pod start: keeper pane %s\n' "$PANE"
herdr pane run "$PANE" sh scripts/pod/keeper.sh >/dev/null 2>&1 \
    || die "herdr could not start the keeper in $PANE."

printf 'pod start: up. The keeper owns %s and restarts the loop on a crash.\n' "$PANE"
printf 'pod start: the maintainer starts on the next tick, from dev/pod/heads.toml.\n'
printf '  herdr pane read %s        # what the loop is doing\n' "$PANE"
printf '  herdr agent list                 # the heads, once they start\n'
