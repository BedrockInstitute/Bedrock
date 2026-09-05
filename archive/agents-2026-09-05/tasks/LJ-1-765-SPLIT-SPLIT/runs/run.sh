#!/bin/sh
# One Agda process, caliber from the pane, never set here.
# usage: agents/tasks/LJ-1-765-SPLIT-SPLIT/runs/run.sh <file.agda> <out-name>
f="$1"; out="agents/tasks/LJ-1-765-SPLIT-SPLIT/runs/$2.out"
{
  echo "GHCRTS=[$GHCRTS]"
  echo "started $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  /usr/bin/time -l timeout 1800 agda "$f"
  echo "EXIT=$?"
  echo "ended $(date -u +%Y-%m-%dT%H:%M:%SZ)"
} > "$out" 2>&1
grep -E "^EXIT=|real|maximum resident|^ended|^started|GHCRTS" "$out"
