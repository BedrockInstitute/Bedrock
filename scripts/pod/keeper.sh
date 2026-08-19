#!/bin/sh
# keeper.sh: the thing that must never die, and it is twenty lines of shell.
#
# THE OWNER RULED THE MASTER ORDER WRONG ON 2026-08-18. The maintainer is the role that
# repairs `pod.py`, and `pod.py` used to be the only thing that could start a maintainer,
# so the loop's repairman was the loop's own child. A dead loop stayed dead and silent.
#
# THE REPAIR IS NOT TO GIVE THE MAINTAINER MORE POWER. An agent starts a process only
# inside a tool call: the process is a child of that call, its output goes to the tool
# result and never to this pane, and `pod.py run` is an infinite loop that the call's own
# time limit ends. **A model cannot host this loop.** So the liveness job goes to the
# dumbest thing in the system, which is this file, and the maintainer keeps only the job
# a model is good at, which is finding out WHY the loop died.
#
#   you  ->  keeper.sh  ->  pod.py  ->  maintainer (ensured idempotently every tick)
#
# Liveness is a straight chain and never a cycle. Repair runs the other way: the
# maintainer reads THIS pane with `herdr pane read`, edits the tree, and touches the
# retry file below. It never restarts anything.
#
# RUN IT IN THE PANE YOU USED TO RUN `pod.py run` IN. `pod.py` is a direct child, so this
# pane's scrollback is the loop's own output plus every crash and every restart, and that
# is the same screen the maintainer reads.
set -u

ROOT=$(cd "$(dirname "$0")/../.." && pwd)
cd "$ROOT" || exit 1
PY=${KEEPER_PY:-"$ROOT/.venv/bin/python"}
LOOP=${KEEPER_LOOP:-scripts/pod/pod.py}
RETRY="$ROOT/.pod-state/keeper-retry"
WSFILE="$ROOT/.pod-state/herdr-workspace"
AGENT=pod-batch

# THE FOUR NUMBERS, overridable from the environment SO THAT THEY CAN BE TESTED. A
# restart policy nobody can exercise is a restart policy nobody has checked, and this one
# only runs on the day everything else has already gone wrong.
HEALTHY=${KEEPER_HEALTHY:-300}       # a run shorter than this is a FAST failure
MAX_FAST=${KEEPER_MAX_FAST:-3}       # this many and we stop guessing and ask for help
BACKOFF=${KEEPER_BACKOFF:-5}         # seconds, doubled per fast failure, capped
BACKOFF_MAX=${KEEPER_BACKOFF_MAX:-300}

# Tell the maintainer, and NEVER the owner first: owner's ruling, 2026-08-18. The prompt
# queues if the head is busy and is read when its current tool call ends (C-61).
tell() {
    printf 'keeper: %s\n' "$1"
    command -v herdr >/dev/null 2>&1 && herdr agent prompt "$AGENT" "$1" >/dev/null 2>&1
}

# Sleep, but wake at once if the maintainer says it has landed a repair.
nap() {
    n=$1
    while [ "$n" -gt 0 ]; do
        if [ -e "$RETRY" ]; then
            rm -f "$RETRY"
            printf 'keeper: the maintainer landed a repair. Restarting now.\n'
            return 0
        fi
        sleep 1
        n=$((n - 1))
    done
}

mkdir -p "$ROOT/.pod-state" 2>/dev/null
rm -f "$RETRY"

# THIS PANE IS THE POD'S WORKSPACE, and stamping it is the keeper's job rather than the
# owner's. The dispatch driver reads `.pod-state/herdr-workspace` to decide where to open
# an agent pane; **when it cannot read one it CREATES a workspace**, so a missing or stale
# file silently puts every agent somewhere the owner is not looking. MEASURED 2026-08-19:
# the file still named `wM`, a workspace closed hours earlier.
#
# IT NEVER OVERWRITES A LIVE SETTING. A workspace id that still resolves is a deliberate
# choice and is left alone; only an absent or dead one is replaced. Outside herdr both
# calls fail, the file stays absent, and the driver's own create path takes over.
stamp_workspace() {
    command -v herdr >/dev/null 2>&1 || return 0
    if [ -s "$WSFILE" ] && herdr workspace get "$(cat "$WSFILE")" >/dev/null 2>&1; then
        printf 'keeper: agent panes go to workspace %s\n' "$(cat "$WSFILE")"
        return 0
    fi
    # THE VENV PYTHON BY ABSOLUTE PATH, not `$PY`. `$PY` is the LOOP's interpreter and is
    # overridable so the restart policy can be tested against a fake loop; borrowing it
    # here made the stamp fail under exactly that override and report「not inside a herdr
    # pane」on a machine that was. Two jobs, two names.
    ws=$(herdr pane current 2>/dev/null | "$ROOT/.venv/bin/python" -c \
        'import json,sys; print(json.load(sys.stdin)["result"]["pane"]["workspace_id"])' \
        2>/dev/null) || ws=""
    if [ -n "$ws" ]; then
        printf '%s' "$ws" > "$WSFILE"
        printf 'keeper: this pane is workspace %s, and agent panes will open beside it\n' "$ws"
    else
        rm -f "$WSFILE"
        printf 'keeper: not inside a herdr pane, so the dispatcher will make its own workspace\n'
    fi
}
stamp_workspace
fast=0
wait_s=$BACKOFF

while :; do
    started=$(date +%s)
    "$PY" "$LOOP" run
    rc=$?
    ran=$(($(date +%s) - started))

    # THE THREE ENDINGS THAT ARE NOT CRASHES. Until 2026-08-18 all three exited 1 and
    # this file could not have existed: restarting a rule (d) STOP repeals the STOP rule,
    # and restarting a lock refusal hot-loops against the runner that already holds it.
    case $rc in
        0)  printf 'keeper: the loop exited on a signal. Nothing to restart.\n'
            exit 0 ;;
        3)  # EXIT 3 IS THREE DIFFERENT DECISIONS AND THIS MESSAGE USED TO NAME ONLY ONE.
            # `.pod-state/STOPPED` has three writers: rule (d) at three parked tasks
            # (pod.py:2629), a matched table row whose action is `stop_loop` (pod.py:2386),
            # and the owner's own `pod stop` (pod.py:3088). Naming rule (d) for all three
            # sent the maintainer to look for parked tasks after a `stop_loop` row fired.
            tell "the pod STOPPED (exit 3) after $ran s. That is a DECISION, not a crash, and it has three possible authors: rule (d) at three parked tasks, a table row whose action is stop_loop, or the owner's own \`pod stop\`. Read the newest LOOP_STOPPED line in dev/pod/transitions/ for the reason before you do anything. To continue: .venv/bin/python scripts/pod/pod.py resume"
            exit 3 ;;
        4)  tell "the loop REFUSED to start (exit 4) after $ran s. It never ticked. Read this pane for the reason, repair it, then touch .pod-state/keeper-retry"
            exit 4 ;;
    esac

    if [ "$ran" -ge "$HEALTHY" ]; then
        fast=0
        wait_s=$BACKOFF
    else
        fast=$((fast + 1))
    fi

    if [ "$fast" -ge "$MAX_FAST" ]; then
        tell "the loop died $fast times in a row, the last after $ran s with exit $rc. I have STOPPED restarting it. Read this pane with: herdr pane read. Repair the tree, then touch .pod-state/keeper-retry and I restart at once."
        while [ ! -e "$RETRY" ]; do sleep 5; done
        rm -f "$RETRY"
        fast=0
        wait_s=$BACKOFF
        printf 'keeper: the maintainer landed a repair. Restarting now.\n'
        continue
    fi

    printf 'keeper: the loop died after %s s with exit %s. Restart %s of %s in %s s.\n' \
        "$ran" "$rc" "$((fast + 1))" "$MAX_FAST" "$wait_s"
    nap "$wait_s"
    wait_s=$((wait_s * 2))
    [ "$wait_s" -gt "$BACKOFF_MAX" ] && wait_s=$BACKOFF_MAX
done
