#!/bin/sh
# One Agda process, caliber from the pane, never set here.
# usage: agents/tasks/LJ-1-720/runs/run.sh <file.agda> <out-name>
#
# The working shape is `/usr/bin/time -l agda`, copied from
# [LJ-1.700] (agents/tasks/LJ-1-700/runs/run.sh).  Wall cap is the
# dispatch's own tool timeout.  Every .out carries GHCRTS, a
# start stamp, an end stamp and EXIT=.
f="$1"; out="agents/tasks/LJ-1-720/runs/$2.out"
{
  echo "GHCRTS=[$GHCRTS]"
  echo "started $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  /usr/bin/time -l agda "$f"
  echo "EXIT=$?"
  echo "ended $(date -u +%Y-%m-%dT%H:%M:%SZ)"
} > "$out" 2>&1
grep -E "^EXIT=|real|maximum resident|^ended|^started|GHCRTS|error|unsolved" "$out"
