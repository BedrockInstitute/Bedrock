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
holder=$(herdr agent list 2>/dev/null | "$PY" -c '
import sys, json
try: rows = json.load(sys.stdin)["result"].get("agents") or []
except Exception: sys.exit(0)
for a in rows:
    if a.get("name") == "pod-batch":
        print(a.get("agent"), a.get("pane_id")); break
')
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
    "$PY" scripts/pod/pod.py resume || die "resume failed. Nothing was started."
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
