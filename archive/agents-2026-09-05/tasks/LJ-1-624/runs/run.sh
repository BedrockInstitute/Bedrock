#!/bin/sh
# One Agda process, caliber from the pane, never set here.
# The wall clock is a perl alarm because this machine has no `timeout(1)`.
# usage: runs/run.sh <file> <out-name> [limit-seconds]
f="$1"; out="agents/tasks/LJ-1-624/runs/$2.out"; lim="${3:-900}"
{
  echo "GHCRTS=[$GHCRTS]"
  echo "started $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "limit ${lim}s"
} > "$out"
/usr/bin/time -l perl -e 'alarm shift; exec @ARGV' "$lim" agda "$f" >> "$out" 2>&1
echo "EXIT=$?" >> "$out"
echo "ended $(date -u +%Y-%m-%dT%H:%M:%SZ)" >> "$out"
grep -E "^EXIT=|real|maximum resident|Heap|^ended" "$out"
