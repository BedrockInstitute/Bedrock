#!/bin/sh
# usage: runs/bounded.sh <file.agda> <out-name> <seconds>
f="$1"; out="agents/tasks/LJ-1-584/runs/$2.out"; b="$3"
{ echo "GHCRTS=[$GHCRTS]"; echo "BOUND=${b}s"; echo "started $(date -u +%Y-%m-%dT%H:%M:%SZ)"; } > "$out"
/usr/bin/time -l agda "$f" >> "$out" 2>&1 &
tp=$!
( sleep "$b"; kill -KILL "$tp" 2>/dev/null ) & wd=$!
wait "$tp"; rc=$?
kill "$wd" 2>/dev/null
echo "EXIT=$rc" >> "$out"
echo "ended $(date -u +%Y-%m-%dT%H:%M:%SZ)" >> "$out"
grep -E "^EXIT=|real|maximum resident|^ended|^started|^BOUND" "$out"
