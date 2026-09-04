#!/bin/sh
# One Agda process, caliber from the pane, never set here.
# usage: agents/tasks/LJ-1-722/runs/run.sh <file.agda> <out-name>
#
# Copied from [LJ-1.717] (agents/tasks/LJ-1-717/runs/run.sh), which
# copied from [LJ-1.700].  Every .out carries GHCRTS, a start stamp,
# an end stamp and EXIT=.
f="$1"; out="agents/tasks/LJ-1-722/runs/$2.out"
{
  echo "GHCRTS=[$GHCRTS]"
  echo "started $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  /usr/bin/time -l agda "$f"
  echo "EXIT=$?"
  echo "ended $(date -u +%Y-%m-%dT%H:%M:%SZ)"
} > "$out" 2>&1
grep -E "^EXIT=|real|maximum resident|^ended|^started|GHCRTS|error|unsolved" "$out"
