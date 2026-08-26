#!/bin/sh
# One Agda process, caliber from the pane, never set here.
# usage: agents/tasks/LJ-1-667/runs/run.sh <file.agda> <out-name>
#
# No perl alarm: on this pane `time -l perl -e alarm` returned
# `time: signal: Invalid argument` and EXIT=1 with no Agda error
# (runs/p-1.out).  The working shape is `/usr/bin/time -l agda`.
# Wall cap is the dispatch's own tool timeout.  Every .out carries
# GHCRTS, a start stamp, an end stamp and EXIT=.
f="$1"; out="agents/tasks/LJ-1-667/runs/$2.out"
{
  echo "GHCRTS=[$GHCRTS]"
  echo "started $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  /usr/bin/time -l agda "$f"
  echo "EXIT=$?"
  echo "ended $(date -u +%Y-%m-%dT%H:%M:%SZ)"
} > "$out" 2>&1
grep -E "^EXIT=|real|maximum resident|^ended|^started|GHCRTS" "$out"
