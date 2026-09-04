#!/bin/sh
# persistent relauncher for the swap-guard window: ONE agda at a time;
# relaunch immediately after each watchdog kill, so every attempt uses a
# full sweep gap. usage: relaunch.sh <file.agda> <out-base> [max-tries]
TASK=agents/tasks/LJ-1-732
f="$TASK/runs/$1"; base="$2"; max="${3:-12}"; n=0
while [ $n -lt "$max" ]; do
  n=$((n+1))
  ./agents/tasks/LJ-1-732/runs/run.sh "$f" "$base-$n"
  if grep -q "^EXIT=0" "$TASK/runs/$base-$n.out"; then
    echo "GREEN $base-$n"
    exit 0
  fi
  if ! grep -q "command terminated abnormally" "$TASK/runs/$base-$n.out"; then
    echo "REAL-ERROR $base-$n (agda diagnostic, not a kill)"
    exit 2
  fi
  echo "killed $base-$n, relaunching"
done
echo "EXHAUSTED $base after $max tries"
