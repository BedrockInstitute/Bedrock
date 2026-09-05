#!/bin/sh
# LJ-1.331 probe runner. One arm per call. It records the machine state
# before and after, the wall seconds and the exit code beside the raw
# profile, so every figure in the report has its own run file.
#
# usage: sh agents/tasks/LJ-1-331/run.sh <ARM> <FILE> [extra agda flags]
# It refuses to start when two agda processes already run (C-12).
set -u
ARM="$1"
FILE="$2"
shift 2
ROOT=/Users/alsg/Agentic/Bedrock
OUT="$ROOT/agents/tasks/LJ-1-331/runs/$ARM.out"
SLOTS=$(ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l | tr -d ' ')
if [ "$SLOTS" -ge 2 ]; then
  echo "REFUSED: $SLOTS agda processes already run (C-12 caps at two)."
  exit 3
fi
{
  echo "# arm $ARM"
  echo "# file $FILE"
  echo "# flags --profile=definitions $*"
  echo "# GHCRTS -A64m -I0 -M8g"
  echo "# agda slots before $SLOTS"
  echo "# load before $(uptime)"
  echo "# started $(date '+%Y-%m-%d %H:%M:%S')"
} > "$OUT"
START=$(date +%s)
GHCRTS="-A64m -I0 -M8g" agda --profile=definitions "$@" "$FILE" >> "$OUT" 2>&1
CODE=$?
END=$(date +%s)
{
  echo "# wall seconds $((END - START))"
  echo "# exit $CODE"
  echo "# agda slots after $(ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l | tr -d ' ')"
  echo "# load after $(uptime)"
} >> "$OUT"
echo "$ARM done: wall $((END - START)) s, exit $CODE"
