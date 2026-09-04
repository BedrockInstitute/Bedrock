#!/bin/sh
# DIAGNOSTIC runner: short cap for bisect instruments only.
# One Agda process, caliber from the pane, never set here.
# usage: runs/diag.sh <file.agda> <out-name> <cap-seconds>
f="$1"; out="agents/tasks/LJ-1-767/runs/$2.out"; cap="$3"
{
  echo "GHCRTS=[$GHCRTS]"
  echo "DIAGNOSTIC bisect, cap $cap s (never reported as a price)"
  echo "started $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  /usr/bin/time -l timeout "$cap" agda "$f"
  echo "EXIT=$?"
  echo "ended $(date -u +%Y-%m-%dT%H:%M:%SZ)"
} > "$out" 2>&1
grep -E "^EXIT=|real|maximum resident|^ended|^started|GHCRTS|DIAGNOSTIC" "$out"
