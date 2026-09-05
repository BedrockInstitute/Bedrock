#!/bin/sh
# One Agda process, caliber from the pane, never set here.
# usage: runs/run.sh <file.agda> <out-name>
f="$1"; out="agents/tasks/LJ-1-537/runs/$2.out"
{
  echo "GHCRTS=[$GHCRTS]"
  echo "started $(date -u +%Y-%m-%dT%H:%M:%SZ)"
} > "$out"
/usr/bin/time -l agda "$f" >> "$out" 2>&1
echo "EXIT=$?" >> "$out"
tail -40 "$out"
