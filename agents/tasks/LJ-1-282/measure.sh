#!/bin/zsh
# LJ-1.282 measurement harness.
#   usage: measure.sh <label> <n-runs> <agda-file> <agdai-path> [extra agda flags]
# Deletes the interface before every run, so every run is cold for that file.
# Records the one-minute load average at the start of each run.
set -u
cd /Users/alsg/Agentic/Bedrock
LABEL="$1"; N="$2"; FILE="$3"; IFACE="$4"; shift 4
OUT="agents/tasks/LJ-1-282/timings.csv"
export GHCRTS="-A64m -I0 -M8g"
for i in $(seq 1 "$N"); do
  rm -f "$IFACE"
  LOAD=$(uptime | sed 's/.*load averages*: //' | awk '{print $1}' | tr -d ',')
  START=$(python3 -c 'import time; print(time.time())')
  agda "$@" "$FILE" > "agents/tasks/LJ-1-282/${LABEL}-run${i}.log" 2>&1
  RC=$?
  END=$(python3 -c 'import time; print(time.time())')
  EL=$(python3 -c "print(f'{$END-$START:.2f}')")
  echo "$LABEL,$i,$RC,$EL,$LOAD" >> "$OUT"
  echo "$LABEL run$i rc=$RC elapsed=${EL}s load=$LOAD"
done
