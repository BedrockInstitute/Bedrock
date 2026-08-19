#!/bin/sh
# wait-and-start.sh: sleep until a wall-clock time, then resume the loop and start the
# keeper. It is the alarm the owner asked for on 2026-08-19, when the coder vendor's
# five-hour quota emptied and every coder dispatch returned 429 and wrote nothing.
#
# **IT RUNS IN THE KEEPER'S OWN PANE AND DEPENDS ON NO AGENT SESSION.** The maintainer
# cannot host a process: an agent starts one only inside a tool call, the call's time
# limit ends it, and its output never reaches this pane. So the alarm is a plain shell
# script started in the pane it will hand over to, exactly as `keeper.sh` is.
#
# **IT RESUMES BEFORE IT STARTS.** `.pod-state/STOPPED` is set, because rule (d) stopped
# the loop at seven parked tasks. Starting the keeper without clearing it would exit 3 in
# zero seconds, which is the shape the owner saw all afternoon.
#
# Usage:  sh scripts/pod/wait-and-start.sh "2026-08-19 20:19:47"
set -u

ROOT=$(cd "$(dirname "$0")/../.." && pwd)
cd "$ROOT" || exit 1
PY=${WAIT_PY:-"$ROOT/.venv/bin/python"}
WHEN=${1:?usage: wait-and-start.sh "YYYY-MM-DD HH:MM:SS"}

target=$(date -j -f "%Y-%m-%d %H:%M:%S" "$WHEN" +%s 2>/dev/null) || {
    printf 'wait-and-start: cannot read the time %s\n' "$WHEN" >&2; exit 2; }

printf 'wait-and-start: holding until %s. The coder vendor quota resets then.\n' "$WHEN"
printf 'wait-and-start: interrupt this pane to cancel the alarm.\n'

while [ "$(date +%s)" -lt "$target" ]; do
    left=$(( target - $(date +%s) ))
    printf '\rwait-and-start: %d min left  ' "$(( left / 60 ))"
    sleep 30
done
printf '\nwait-and-start: the wait is over.\n'

# THE PARKED SET IS NOT CLEARED HERE. `resume` un-parks what its own rules un-park and
# nothing else; the seven parked tasks are a real state and the maintainer reads them.
"$PY" scripts/pod/pod.py resume --once || {
    printf 'wait-and-start: resume REFUSED. Not starting the keeper.\n' >&2; exit 1; }

printf 'wait-and-start: handing this pane to the keeper.\n'
exec sh scripts/pod/keeper.sh
