#!/bin/sh
# One Agda process, caliber from the pane, never set here.
# usage: agents/tasks/LJ-1-734/runs/run.sh <file.agda> <out-name> [cap-seconds]
#
# The wall cap is a perl alarm (SIGALRM at the given seconds), because
# this macOS has no `timeout`.  Every .out carries GHCRTS, a start
# stamp, an end stamp and EXIT=.
f="$1"; out="agents/tasks/LJ-1-734/runs/$2.out"; cap="${3:-1800}"
{
  echo "GHCRTS=[$GHCRTS]"
  echo "cap ${cap}s (perl alarm)"
  echo "started $(date -u +%Y-%m-%dT%H:%M:%SZ)"
} > "$out"
/usr/bin/time -l perl -e "alarm shift; exec @ARGV" "$cap" agda "$f" >> "$out" 2>&1
echo "EXIT=$?" >> "$out"
echo "ended $(date -u +%Y-%m-%dT%H:%M:%SZ)" >> "$out"
grep -E "^EXIT=|real|maximum resident|^ended|^started" "$out"
