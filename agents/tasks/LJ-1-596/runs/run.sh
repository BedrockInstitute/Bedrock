#!/bin/sh
# [LJ-1.593] one Agda run, one output file.  ONE PROCESS AT A TIME: the
# guard is a PID FILE and not a `pgrep` pattern, because a pattern also
# matches the shell that greps for it.  MEASURED on run s4-2, which was
# refused by a poll command that carried the pattern in its own argv.
# GHCRTS is NOT set here; the program sets it on this pane.
set -u
TARGET="$1"
TAG="$2"
DIR="agents/tasks/LJ-1-596/runs"
OUT="${DIR}/${TAG}.out"
PIDF="${DIR}/.agda.pid"
if [ -f "$PIDF" ] && kill -0 "$(cat "$PIDF")" 2>/dev/null; then
  echo "REFUSED: agda pid $(cat "$PIDF") of this task is still live" > "$OUT"
  exit 3
fi
{
  echo "# ${TAG}: ${TARGET}"
  echo "# GHCRTS=${GHCRTS:-unset}"
  /usr/bin/time -l agda "$TARGET" 2>&1 &
  echo $! > "$PIDF"
  wait $!
  echo "EXIT=$?"
} > "$OUT" 2>&1
rm -f "$PIDF"
