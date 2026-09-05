#!/bin/bash
# [LJ-1.661] Run harness. One Agda process per run.
# Convention (matching runs/floor-0.*):  $N.out = agda stdout,
# $N.err = agda stderr, $N.time = /usr/bin/time -l -p report, $N.rc = rc line.
set -u
cd "$(dirname "$0")/../../../.."
TASK=agents/tasks/LJ-1-661
RUNS=$TASK/runs
N=${1:?usage: run661.sh <floor-N|wall>}
AGDA=agda
LIB=_build/2.8.0/agda/src   # the compiled library the floors resolve against
GUARD=1500

case $N in
  floor-*) FILE="$TASK/Probe661.agda" ;;
  wall)
    cp "$TASK/Wall661.agda.txt" "$TASK/Wall661.agda"
    FILE="$TASK/Wall661.agda"
    ;;
  *) echo "unknown run: $N" >&2; exit 2 ;;
esac

ROOT=$(pwd)
( ulimit -t $GUARD
  cd "$LIB" && { /usr/bin/time -l -p $AGDA "$ROOT/$FILE" 2> "$ROOT/$RUNS/$N.time"; } \
    > "$ROOT/$RUNS/$N.out" 2> "$ROOT/$RUNS/$N.err" ) &
PID=$!
wait $PID
RC=$?
[ -f "$TASK/Wall661.agda" ] && rm -f "$TASK/Wall661.agda"
printf 'rc=%s\n' "$RC" > "$RUNS/$N.rc"
echo "[$N] lib=$LIB" >> "$RUNS/log.md"
echo "[$N] rc=$RC $(date)" >> "$RUNS/log.md"
exit $RC
