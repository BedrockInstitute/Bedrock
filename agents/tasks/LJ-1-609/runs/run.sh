#!/bin/sh
# One Agda process, caliber from the pane, never set here.
# usage: agents/tasks/LJ-1-609/runs/run.sh <file.agda> <out-name>
#
# No `timeout` wrapper: this macOS has none ([LJ-1.602], runs/w3-1.out,
# exit 127, no Agda process started).  The cap that binds is the pane's
# GHCRTS heap guard plus the dispatch's own time-box; both are recorded
# in every .out this script writes.
f="$1"; out="agents/tasks/LJ-1-609/runs/$2.out"
{
  echo "GHCRTS=[$GHCRTS]"
  echo "started $(date -u +%Y-%m-%dT%H:%M:%SZ)"
} > "$out"
/usr/bin/time -l agda "$f" >> "$out" 2>&1
echo "EXIT=$?" >> "$out"
echo "ended $(date -u +%Y-%m-%dT%H:%M:%SZ)" >> "$out"
grep -E "^EXIT=|real|maximum resident|^ended|^started" "$out"
