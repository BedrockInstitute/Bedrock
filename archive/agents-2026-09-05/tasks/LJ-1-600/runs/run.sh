#!/bin/sh
# One Agda process, caliber from the pane, never set here.
# usage: runs/run.sh <file.agda> <out-name> <cap-seconds>
# No `timeout(1)` on this macOS: the cap is a watchdog loop that kills
# the agda process group when the wall clock passes the cap.
f="$1"; out="agents/tasks/LJ-1-600/runs/$2.out"; cap="$3"
{
  echo "GHCRTS=[$GHCRTS]"
  echo "cap=${cap}s (set by this task, see the brief's time-box clauses)"
  echo "started $(date -u +%Y-%m-%dT%H:%M:%SZ)"
} > "$out"
/usr/bin/time -l agda "$f" >> "$out" 2>&1 &
agda_pid=$!
( i=0
  while kill -0 $agda_pid 2>/dev/null; do
    if [ "$i" -ge "$cap" ]; then
      echo "CAP ${cap}s REACHED, killing agda pid $agda_pid" >> "$out"
      kill -9 $agda_pid 2>/dev/null
      exit 0
    fi
    sleep 1; i=$((i+1))
  done ) &
dog_pid=$!
wait $agda_pid; rc=$?
kill $dog_pid 2>/dev/null
echo "EXIT=$rc" >> "$out"
echo "ended $(date -u +%Y-%m-%dT%H:%M:%SZ)" >> "$out"
grep -E "^EXIT=|real|maximum resident|^ended|^started|^cap|CAP " "$out"
