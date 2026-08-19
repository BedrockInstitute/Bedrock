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
# **IT JOINS ALL ARGUMENTS, because the caller may not preserve the quoting.**
# MEASURED 2026-08-19: `herdr pane run` passes its COMMAND words through
# individually, so a quoted "YYYY-MM-DD HH:MM:SS" arrived as two arguments and
# `$1` held only the date. Reading `$*` accepts both spellings.
if [ $# -eq 0 ]; then
    printf 'usage: wait-and-start.sh "YYYY-MM-DD HH:MM:SS"\n' >&2; exit 2
fi
WHEN=$*

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

# **`--retry` IS REQUIRED HERE AND A PLAIN RESUME WOULD HAVE DONE NOTHING.** MEASURED
# 2026-08-19 on the live state: all seven parked tasks either route to NO MATCH or carry
# no record at all, so rule (a2) un-parks none of them. Seven IS `parked_max`, so the
# loop would tick once and rule (d) would stop it again. The cause here was external to
# every one of them, a vendor quota, which is exactly what the flag is for.
# **IT NAMES TWO CODES AND NOT EVERY PARK.** The seven parked tasks did not all want
# the same thing. LJ-1.396 and LJ-1.397 met the vendor's 429, started, retried, exited
# clean and wrote NOTHING, so they never had a turn and a re-run is the only honest
# answer. The other five had already delivered and are stuck only because their records
# predate fact 8; re-running them would burn agent time to buy a bookkeeping close, and
# AD3 gives that judgement to the mathematician at the next refill, which reads the
# transition log and can drop them from the queue in one line.
"$PY" scripts/pod/pod.py resume --retry LJ-1.396 LJ-1.397 --once || {
    printf 'wait-and-start: resume REFUSED. Not starting the keeper.\n' >&2; exit 1; }

printf 'wait-and-start: handing this pane to the keeper.\n'
exec sh scripts/pod/keeper.sh
