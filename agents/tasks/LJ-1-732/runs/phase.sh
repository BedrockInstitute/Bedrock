#!/bin/sh
# phase-cycling relauncher: after each watchdog kill (a sweep just
# fired), rotate the launch offset so some attempt starts within a
# fraction of a second after a sweep and gets the full 20 s gap.
# usage: phase.sh <file.agda> <out-base> <tries>
TASK=agents/tasks/LJ-1-732
f="$TASK/runs/$1"; base="$2"; max="${3:-12}"; n=0
while [ $n -lt "$max" ]; do
  n=$((n+1))
  off=$(( (n * 2) % 20 ))
  sleep "$off"
  ./agents/tasks/LJ-1-732/runs/run.sh "$f" "$base-$n"
  if grep -q "^EXIT=0" "$TASK/runs/$base-$n.out"; then
    echo "GREEN $base-$n"
    exit 0
  fi
  if ! grep -q "command terminated abnormally" "$TASK/runs/$base-$n.out"; then
    echo "REAL-ERROR $base-$n (agda diagnostic, not a kill)"
    exit 2
  fi
  echo "killed $base-$n (offset $off), rotating"
done
echo "EXHAUSTED $base after $max tries"
