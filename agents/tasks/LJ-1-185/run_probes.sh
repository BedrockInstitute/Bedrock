#!/bin/sh
# LJ-1.185: the probe series, both accounts, four repeats.
#
# Agda 2.8.0 refuses `--profile=internal` with `--profile=definitions`, so each
# spelling is read twice. The pairs are INTERLEAVED, so machine drift moves
# both accounts together instead of only one. Repeat 1 is the warm-up and it is
# discarded.
#
# It calls `agents/tasks/LJ-1-155/measure.py`, which refuses to start beside
# another agda binary and records the load before and after every run (C-26,
# C-12).
#
# DD4: the loop takes its file list from the argument line, so it drives a
# J-tower probe set unchanged.

set -e
ROOT=/Users/alsg/Agentic/Bedrock
OUT=$ROOT/agents/tasks/LJ-1-185/runs
PY=$ROOT/.venv/bin/python
M=$ROOT/agents/tasks/LJ-1-155/measure.py

FILES=${*:-"agents/tasks/LJ-1-185/ProbeLJ1185B.agda agents/tasks/LJ-1-185/ProbeLJ1185C.agda agents/tasks/LJ-1-185/ProbeLJ1185D.agda"}

cd "$ROOT"
for i in 1 2 3 4; do
  for f in $FILES; do
    LJ1155_TAG=defs$i $PY "$M" "$OUT" definitions "$f"
    LJ1155_TAG=int$i  $PY "$M" "$OUT" internal    "$f"
  done
done
